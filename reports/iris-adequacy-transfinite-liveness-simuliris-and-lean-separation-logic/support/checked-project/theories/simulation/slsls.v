(** * SLSLS, Separation Logic Stuttering Local Simulation *)
(* Specialize to finite stepindices *)
From iris.algebra Require Export ofe stepindex_finite.
From iris.bi Require Import bi fixpoint_mono.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import language.
From simuliris.simulation Require Export simulation.
Import bi.

(* parameterized over "external" relation that restricts values passed to and
from external function calls *)
(* TODO: Hint Mode? *)
Class simulirisGS (PROP : bi) (Λ : language) := SimulirisGS {
  (* state interpretation *)
  state_interp : prog Λ → state Λ → prog Λ → state Λ → list (expr Λ) → PROP;
  state_interp_pure_prim_step P_t σ_t P_s σ_s e_s T π e_s':
    T !! π = Some e_s →
    (∀ σ_s, prim_step P_s e_s σ_s e_s' σ_s []) →
    state_interp P_t σ_t P_s σ_s T -∗
    state_interp P_t σ_t P_s σ_s (<[π:=e_s']>T);
  (* external function call relation *)
  ext_rel : thread_id → val Λ → val Λ → PROP;
}.

Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language}.
  Context {s : simulirisGS PROP Λ}.

  Set Default Proof Using "Type*".

  Implicit Types
    (e_s e_t e: expr Λ)
    (P_s P_t P: prog Λ)
    (σ_s σ_t σ : state Λ).

  Notation expr_rel := (@exprO _ Λ -d> @exprO _ Λ -d> PROP).

  Local Instance expr_rel_func_ne (F: expr_rel → thread_idO -d> expr_rel) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ π π' ->%discrete_iff%leibniz_equiv e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  (** We do *not* index everything by the program function tables, instead we
  expect the state interpretation to record that information in ghost state. *)
  Definition progs_are (P_t P_s : prog Λ) : PROP :=
    (□ ∀ P_t' P_s' σ_t σ_s T_s, state_interp P_t' σ_t P_s' σ_s T_s → ⌜P_t' = P_t⌝ ∧ ⌜P_s' = P_s⌝)%I.

  Global Instance progs_are_persistent (P_s P_t : prog Λ) :
    Persistent (progs_are P_s P_t).
  Proof. rewrite /progs_are; apply _. Qed.

  (** Simulation relation with stuttering *)
  Definition lift_post (Φ: val Λ → val Λ → PROP) :=
    (λ e_t e_s, ∃ v_t v_s, ⌜e_t = of_val v_t⌝ ∗ ⌜e_s = of_val v_s⌝ ∗ Φ v_t v_s)%I.

  Section sim_def.

  (* Thread id must come after postcondition as otherwise NonExpansive
  applies to the thread id instead of the post-condition. *)
  Definition sim_expr_inner (greatest_rec :  expr_rel -d> thread_id -d> expr_rel) (least_rec : expr_rel -d> thread_id -d> expr_rel) : expr_rel -d> thread_id -d> expr_rel :=
    λ Φ π e_t e_s,
    (∀ P_t σ_t P_s σ_s T_s K_s,
        state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ -∗ |==>
      (* base case *)
      (∃ e_s' σ_s', ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t P_s σ_s' (<[π := fill K_s e_s']> T_s) ∗ Φ e_t e_s')

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ -∗ |==>
        (* stuttering *)
        (⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s T_s ∗ least_rec Φ π e_t' e_s) ∨
        (* take a step *)
        (∃ e_s' e_s'' σ_s' σ_s'' efs_s,
          ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
          ⌜prim_step P_s e_s' σ_s' e_s'' σ_s'' efs_s⌝ ∗
          state_interp P_t σ_t' P_s σ_s'' (<[π := fill K_s e_s'']> T_s ++ efs_s) ∗ greatest_rec Φ π e_t' e_s'' ∗
          [∗ list] π'↦e_t; e_s ∈ efs_t; efs_s, greatest_rec (lift_post (ext_rel (length T_s + π'))) (length T_s + π') e_t e_s))

      ∨ (* call case *)
      (∃ f K_t v_t K_s' v_s σ_s',
        ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
        ⌜steps_no_fork P_s e_s σ_s (fill K_s' (of_call f v_s)) σ_s'⌝ ∗
        ext_rel π v_t v_s ∗ state_interp P_t σ_t P_s σ_s' (<[π := fill K_s (fill K_s' (of_call f v_s))]> T_s) ∗
        (∀ v_t v_s, ext_rel π v_t v_s -∗ greatest_rec Φ π (fill K_t (of_val v_t)) (fill K_s' (of_val v_s)) ))
    )%I.


  Lemma sim_expr_inner_mono l1 l2 g1 g2:
    ⊢ □ (∀ Φ π e_t e_s, l1 Φ π e_t e_s -∗ l2 Φ π e_t e_s)
    → □ (∀ Φ π e_t e_s, g1 Φ π e_t e_s -∗ g2 Φ π e_t e_s)
    → ∀ Φ π e_t e_s, sim_expr_inner g1 l1 Φ π e_t e_s -∗ sim_expr_inner g2 l2 Φ π e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ π e_t e_s) "Hsim".
    rewrite /sim_expr_inner. iIntros (P_t σ_t P_s σ_s T_s K_s) "Ha".
    iMod ("Hsim" with "Ha") as "[Hval | [Hstep | Hcall]]"; iModIntro.
    + iLeft. iApply "Hval".
    + iRight; iLeft. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". by iApply "Hleast". }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame.
      iSplitL "H5"; first by iApply "Hgreatest".
      iApply (big_sepL2_impl with "H6 []"); simpl.
      iIntros "!>" (?????). by iApply "Hgreatest".
    + iRight; iRight. iDestruct "Hcall" as (f K_t v_t K_s' v_s σ_s') "(H1& H2& H3& H4&H5)".
      iExists (f), (K_t), (v_t), (K_s'), (v_s), (σ_s'). iFrame.
      iIntros (? ?) "H1". iApply "Hgreatest". by iApply "H5".
  Qed.

  (* the strongest monotonicity lemma we can prove, allows for changing the post condition and recursive occurrences *)
  Lemma sim_expr_inner_strong_mono l1 l2 g1 g2:
    ⊢ □ (∀ Φ π Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, l1 Φ π e_t e_s -∗ l2 Ψ π e_t e_s)
    → □ (∀ Φ π Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, g1 Φ π e_t e_s -∗ g2 Ψ π e_t e_s)
    → ∀ Φ π Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, sim_expr_inner g1 l1 Φ π e_t e_s -∗ sim_expr_inner g2 l2 Ψ π e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ π Ψ) "HΦΨ". iIntros (e_t e_s) "Hsim".
    rewrite /sim_expr_inner. iIntros (P_t σ_t P_s σ_s T_s K_s) "Ha".
    iMod ("Hsim" with "Ha") as "[Hval | [Hstep | Hcall]]"; iModIntro.
    + iLeft. iDestruct "Hval" as (e_s' σ_s') "(Hnf & SI & HΦ)".
      iExists e_s', σ_s'. iFrame. by iApply "HΦΨ".
    + iRight; iLeft. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". by iApply ("Hleast" with "HΦΨ H1"). }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame.
      iSplitL "H5 HΦΨ"; first by iApply ("Hgreatest" with "HΦΨ H5").
      iApply (big_sepL2_impl with "H6 []"); simpl.
      iIntros "!>" (?????) "Hg". iApply ("Hgreatest" with "[] Hg").
      by iIntros (??) "?".
    + iRight; iRight. iDestruct "Hcall" as (f K_t v_t K_s' v_s σ_s') "(H1& H2& H3& H4&H5)".
      iExists (f), (K_t), (v_t), (K_s'), (v_s), (σ_s'). iFrame.
      iIntros (? ?) "H1". iApply ("Hgreatest" with "HΦΨ [H5 H1]").
      by iApply "H5".
  Qed.

  Instance sim_expr_inner_ne:
    ∀n, Proper ((dist n ==> dist n ==> dist n) ==> (dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n ==> dist n) sim_expr_inner.
  Proof.
    intros n G1 G2 HG L1 L2 HL Φ Ψ HΦΨ π π' Hπ%discrete_iff%leibniz_equiv e_t e_t' Ht%discrete_iff%leibniz_equiv e_s e_s' Hs%discrete_iff%leibniz_equiv; [|apply _..].
    subst; rewrite /sim_expr_inner.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
  Qed.

  Instance sim_expr_inner_proper:
    Proper ((equiv ==> equiv ==> equiv) ==> (equiv ==> equiv ==> equiv) ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) sim_expr_inner.
  Proof.
    intros G1 G2 HG L1 L2 HL Φ Ψ HΦΨ π π' Hπ%leibniz_equiv e_t e_t' Ht%leibniz_equiv e_s e_s' Hs%leibniz_equiv.
    subst; rewrite /sim_expr_inner.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
  Qed.

  Local Instance least_def_body_mono (greatest_rec : (expr_rel -d> thread_id -d> expr_rel)) :
    NonExpansive (greatest_rec) →
    BiMonoPred (λ (least_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO -d> PROP), uncurry4 (sim_expr_inner greatest_rec (curry4 least_rec))).
  Proof.
    intros Hg; constructor.
    - intros L1 L2 HL1 HL2. iIntros "#H" (x).
      destruct x as (((Φ & π) & e_t) & e_s); simpl.
      iApply (sim_expr_inner_mono with "[] []"); iModIntro; clear.
      { iIntros (G π e_t e_s); unfold curry4; iApply "H". }
      iIntros (G π e_t e_s) "$".
    - intros l Hne n x y Heq.
      destruct x as (((Φ & π) & e_t) & e_s); simpl.
      destruct y as (((Ψ & π') & e_t') & e_s'); simpl.
      destruct Heq as [[[Heq1 Heq2] Heq3] Heq4]; simpl in Heq1, Heq2, Heq3, Heq4.
      eapply sim_expr_inner_ne; eauto.
      + intros ????? ->%leibnizO_leibniz. by eapply Hg.
      + intros ????????; rewrite /curry4. eapply Hne.
        repeat split; simpl; done.
  Qed.

  Definition least_def (greatest_rec : expr_rel -d> thread_id -d> expr_rel) : expr_rel -d> thread_id -d> expr_rel :=
    curry4 (bi_least_fixpoint (λ (least_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO → PROP), uncurry4 (sim_expr_inner greatest_rec (curry4 least_rec)))).


  Global Instance least_def_ne :
    NonExpansive4 least_def.
  Proof.
    rewrite /least_def; intros n x y Heq ??????????.
    rewrite {1 3}/curry4. apply least_fixpoint_ne; last by repeat split.
    intros ? [[[??]?] ?]; simpl.
    rewrite /sim_expr_inner. repeat f_equiv; apply Heq.
  Qed.

  Lemma least_def_mono R R' π Φ e_t e_s:
    NonExpansive (R': expr_rel -d> thread_id -d> expr_rel) →
    <pers> (∀ Φ π e_t e_s, R Φ π e_t e_s -∗ R' Φ π e_t e_s) -∗
    least_def R Φ π e_t e_s -∗ least_def R' Φ π e_t e_s.
  Proof.
    iIntros (Hne) "#Hmon". rewrite /least_def {1 3}/curry4.
    iIntros "Hleast".
    (* FIXME: this iApply takes like 4 seconds *)
    iApply (least_fixpoint_iter with "[] Hleast"); clear Φ π e_t e_s.
    iModIntro. iIntros ([[[Φ π] e_t] e_s]).
    erewrite least_fixpoint_unfold; last first.
    { eapply least_def_body_mono, _. }
    rewrite {1 3}/uncurry4.
    iApply (sim_expr_inner_mono with "[] []").
    { iModIntro. iIntros (Φ' π' e_t' e_s') "$". }
      iModIntro; iIntros (Φ' π' e_t' e_s'); by iApply "Hmon".
  Qed.

  Lemma least_def_unfold G π Φ e_t e_s:
    NonExpansive G →
    least_def G Φ π e_t e_s ≡ sim_expr_inner G (least_def G) Φ π e_t e_s.
  Proof.
    intros ?; rewrite {1}/least_def {1}/curry4 least_fixpoint_unfold {1}/uncurry4 //=.
  Qed.

  Instance greatest_def_body_mono :
    BiMonoPred (λ (greatest_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO → PROP), uncurry4 (least_def (curry4 greatest_rec))).
  Proof.
    constructor.
    - intros G1 G2 HG1 HG2. iIntros "#H" (x).
      destruct x as [[[Φ π] e_t] e_s]; rewrite /uncurry4.
      iApply least_def_mono.
      { (* FIXME: TC inference should solve this *) solve_proper. }
      iModIntro.
      iIntros (Φ' π' e_t' e_s'); iApply "H".
    - intros G Hne n x y Heq. rewrite /least_def !uncurry4_curry4.
      eapply least_fixpoint_ne'; last done.
      intros L HL m [[[Φ π] e_t] e_s] [[[Ψ π'] e_t'] e_s'] Heq'; simpl.
      eapply sim_expr_inner_ne; [| |eapply Heq'..].
      + solve_proper.
      + solve_proper.
  Qed.

  Definition greatest_def : expr_rel -d> thread_id -d> expr_rel :=
    curry4 (bi_greatest_fixpoint (λ (greatest_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO → PROP), uncurry4 (least_def (curry4 greatest_rec)))).

  Lemma greatest_def_unfold Φ π e_t e_s:
    greatest_def Φ π e_t e_s ≡ least_def greatest_def Φ π e_t e_s.
  Proof.
    rewrite {1}/greatest_def {1}/curry4 greatest_fixpoint_unfold {1}/uncurry4 //=.
  Qed.

  Global Instance greatest_def_ne: NonExpansive greatest_def.
  Proof. solve_proper. Qed.

  Global Instance greatest_def_proper: Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) greatest_def.
  Proof.
    intros Φ Ψ Heq π π' <-%leibniz_equiv e_t e_t' <-%leibniz_equiv e_s e_s' <-%leibniz_equiv.
    revert π e_t e_s. change (greatest_def Φ ≡ greatest_def Ψ).
    eapply ne_proper; first apply _. done.
  Qed.

  Lemma greatest_def_fixpoint Φ π e_t e_s:
    greatest_def Φ π e_t e_s ≡ sim_expr_inner greatest_def greatest_def Φ π e_t e_s.
  Proof.
    rewrite greatest_def_unfold least_def_unfold.
    eapply sim_expr_inner_proper; eauto.
    - solve_proper.
    - intros Φ' Ψ' Heq. intros ??? ??. rewrite -greatest_def_unfold.
      f_equiv; done.
  Qed.

  End sim_def.

  (** Instantiate Sim typeclasses. Instances are local, see hitn and comment at
  the bottom of this file. *)
  Definition sim_expr_aux : seal greatest_def.
  Proof. by eexists. Qed.
  Local Instance sim_expr_stutter : SimE PROP Λ := (sim_expr_aux).(unseal).
  Lemma sim_expr_eq : sim_expr = λ Φ π e_t e_s, @greatest_def Φ π e_t e_s.
  Proof. rewrite -sim_expr_aux.(seal_eq) //. Qed.

  Lemma lift_post_val Φ v_t v_s : Φ v_t v_s -∗ lift_post Φ (of_val v_t) (of_val v_s).
  Proof. iIntros "?"; iExists v_t, v_s; eauto using to_of_val. Qed.
  Definition sim_def (Φ : val Λ → val Λ → PROP) π e_t e_s  :=
    sim_expr (lift_post Φ) π e_t e_s.
  Local Instance sim_stutter : Sim PROP Λ := sim_def.

  Lemma sim_expr_fixpoint Φ π e_t e_s:
    sim_expr Φ π e_t e_s ⊣⊢ sim_expr_inner sim_expr sim_expr Φ π e_t e_s.
  Proof.
    rewrite sim_expr_eq greatest_def_fixpoint //.
  Qed.

  Lemma sim_expr_unfold Φ π e_t e_s:
    sim_expr Φ π e_t e_s ⊣⊢
    (∀ P_t σ_t P_s σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ -∗ |==>
      (* base case *)
      (∃ e_s' σ_s', ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t P_s σ_s' (<[π := fill K_s e_s']> T_s) ∗ Φ e_t e_s')

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ -∗ |==>
        (* stuttering *)
        (⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s T_s ∗ sim_expr Φ π e_t' e_s) ∨
        (* take a step *)
        (∃ e_s' e_s'' σ_s' σ_s'' efs_s,
          ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
          ⌜prim_step P_s e_s' σ_s' e_s'' σ_s'' efs_s⌝ ∗
          state_interp P_t σ_t' P_s σ_s'' (<[π := fill K_s e_s'']> T_s ++ efs_s) ∗
          sim_expr Φ π e_t' e_s'' ∗
          [∗ list] π'↦e_t; e_s ∈ efs_t; efs_s, sim_expr (lift_post (ext_rel (length T_s + π'))) (length T_s + π') e_t e_s))

      ∨ (* call case *)
      (∃ f K_t v_t K_s' v_s σ_s',
        ⌜e_t = fill K_t (of_call f v_t)⌝ ∗
        ⌜steps_no_fork P_s e_s σ_s (fill K_s' (of_call f v_s)) σ_s'⌝ ∗
        ext_rel π v_t v_s ∗ state_interp P_t σ_t P_s σ_s' (<[π := fill K_s (fill K_s' (of_call f v_s))]> T_s) ∗
        (∀ v_t v_s, ext_rel π v_t v_s -∗ sim_expr Φ π (fill K_t (of_val v_t)) (fill K_s' (of_val v_s))))
    )%I.
  Proof.
    rewrite sim_expr_fixpoint /sim_expr_inner //.
  Qed.

  Global Instance sim_expr_ne n:
    Proper
    ((pointwise_relation (expr Λ) (pointwise_relation (expr Λ) (dist n))) ==>
      eq ==>
      eq ==>
      eq ==>
      (dist n))
    (sim_expr).
  Proof.
    intros p1 p2 Heq2 π π' -> e e' -> e1 e1' ->.
    rewrite !sim_expr_eq. eapply greatest_def_ne; done.
  Qed.

  Global Instance sim_expr_proper:
    Proper ((pointwise_relation (expr Λ) (pointwise_relation (expr Λ) (≡))) ==> eq ==> eq ==> eq ==> (≡)) (sim_expr).
  Proof.
    intros p1 p2 Heq2 π π' -> e e' -> e1 e1' ->.
    rewrite !sim_expr_eq. eapply greatest_def_proper; done.
  Qed.

  Global Instance sim_ne n:
    Proper ((pointwise_relation (val Λ) (pointwise_relation (val Λ) (dist n))) ==> eq ==> eq ==> eq ==> (dist n)) (sim).
  Proof.
    intros ?? Hpost ??? ??? ???. apply sim_expr_ne; [|done..].
    rewrite /lift_post => ??. repeat f_equiv.
  Qed.

  Global Instance sim_proper:
    Proper ((pointwise_relation (val Λ) (pointwise_relation (val Λ) (≡))) ==> eq ==> eq ==> eq ==> (≡)) (sim).
  Proof.
    intros ?? Hpost ??? ??? ???. apply sim_expr_proper; [|done..].
    rewrite /lift_post => ??. repeat f_equiv.
  Qed.

  Existing Instances least_def_body_mono greatest_def_body_mono.
  (* any post-fixed point is included in the gfp *)
  Lemma sim_expr_strong_coind (F : expr_rel → thread_id -d> expr_rel) :
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ least_def (λ Φ π e_t e_s, F Φ π e_t e_s ∨ sim_expr Φ π e_t e_s) Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ sim_expr Φ π e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (Φ π e_t e_s) "HF".
    rewrite sim_expr_eq /greatest_def {3}/curry4.
    change (F Φ π e_t e_s) with (uncurry4 F (Φ, π, e_t, e_s)).
    remember (Φ, π, e_t, e_s) as p eqn:Heqp. rewrite -Heqp; clear Φ π e_t e_s Heqp.
    iApply (greatest_fixpoint_coind _ (uncurry4 F) with "[] HF").
    iModIntro. iIntros ([[[Φ π] e_t] e_s]); simpl.
    iApply ("HPre" $! Φ π e_t e_s).
  Qed.

  Lemma sim_expr_coind (F : expr_rel → thread_id -d> expr_rel) :
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ least_def F Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ sim_expr Φ π e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (Φ π e_t e_s) "HF".
    iApply (sim_expr_strong_coind with "[] HF"); clear Φ π e_t e_s.
    iModIntro; iIntros (Φ π e_t e_s) "HF".
    iDestruct ("HPre" with "HF") as "HF".
    iApply (least_def_mono with "[] HF"); first by solve_proper.
    iModIntro. clear Φ π e_t e_s. iIntros (Φ π e_t e_s) "HF". by iLeft.
  Qed.

  Lemma least_def_strong_ind (F R: expr_rel → thread_id -d> expr_rel):
    NonExpansive R →
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, sim_expr_inner R (λ Ψ π e_t e_s, F Ψ π e_t e_s ∧ least_def R Ψ π e_t e_s) Φ π e_t e_s -∗ F Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, least_def R Φ π e_t e_s -∗ F Φ π e_t e_s.
  Proof.
    iIntros (Hne1 Hne2) "#HPre". iIntros (Φ π e_t e_s) "HF".
    rewrite {2}/least_def {1}/curry4.
    change (F Φ π e_t e_s) with (uncurry4 F (Φ, π, e_t, e_s)).
    remember (Φ, π, e_t, e_s) as p eqn:Heqp. rewrite -Heqp; clear Φ π e_t e_s Heqp.
    iApply (least_fixpoint_ind _ (uncurry4 F) with "[] HF").
    iModIntro. iIntros ([[[Φ π] e_t] e_s]); simpl.
    rewrite {1}/curry4 {1}/uncurry4.
    iIntros "H". iApply "HPre". iExact "H".
  Qed.

  Lemma least_def_ind (F R: expr_rel → thread_id -d> expr_rel):
    NonExpansive R →
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, sim_expr_inner R F Φ π e_t e_s -∗ F Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, least_def R Φ π e_t e_s -∗ F Φ π e_t e_s.
  Proof.
    iIntros (Hne1 Hne2) "#HPre". iApply least_def_strong_ind.
    iModIntro. iIntros (Φ π e_t e_s) "Hsim".
    iApply "HPre". iApply (sim_expr_inner_mono with "[] [] Hsim"); last by auto.
    iModIntro. iIntros (Φ' π' e_t' e_s') "H". iApply bi.and_elim_l. iApply "H".
  Qed.

  (* we change the predicate beause at every recursive ocurrence,
     we give back ownership of the monotonicity assumption *)
  Lemma least_def_strong_mono (rec : expr_rel → thread_idO -d> expr_rel) Φ Φ' π e_t e_s:
    NonExpansive rec →
     (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗
     least_def rec Φ π e_t e_s -∗
     least_def (λ Ψ π e_t e_s, rec Φ π e_t e_s ∗ (∀ e_t e_s, Φ e_t e_s ==∗ Ψ e_t e_s) ∨ rec Ψ π e_t e_s) Φ' π e_t e_s.
  Proof.
    iIntros (Hne) "Hmon Hleast". iRevert (Φ') "Hmon".
    pose (rec' := (λ Φ Ψ π e_t e_s, rec Φ π e_t e_s ∗ (∀ e_t e_s, Φ e_t e_s ==∗ Ψ e_t e_s) ∨ rec Ψ π e_t e_s)%I).
    pose (F_ind := (λ Φ π e_t e_s, ∀ Φ', (∀ e_t e_s : expr Λ, Φ e_t e_s ==∗ Φ' e_t e_s) -∗ least_def (rec' Φ) Φ' π e_t e_s)%I).
    assert (NonExpansive2 (rec': expr_rel -d> expr_rel -d> thread_idO -d> expr_rel)) as Rne.
    { intros m Φ' Φ'' Heq1 Ψ Ψ' Heq2 ???; rewrite /rec'.
      solve_proper_core ltac:(fun x => f_equiv || apply Heq1 || apply Heq2). }
    assert (NonExpansive (F_ind: expr_rel -d> thread_idO -d> expr_rel)).
    { clear Φ π e_t e_s. intros n Φ Ψ Heq π e_t e_s.
      rewrite /F_ind; do 3 f_equiv; first (repeat f_equiv; by apply Heq).
      eapply least_def_ne; [ |done..]. intros ?. eapply (Rne n Φ Ψ Heq). done. }
    iApply (least_def_ind F_ind rec with "[] Hleast"); clear Φ π e_t e_s.
    iModIntro. iIntros (Φ π e_t e_s) "Hrec". iIntros (Φ') "Hmon".
    rewrite least_def_unfold /sim_expr_inner.

    iIntros (P_t σ_t P_s σ_s T_s K_s) "Ha".
    iMod ("Hrec" with "Ha") as "[Hval | [Hstep | Hcall]]".
    + iLeft. iDestruct "Hval" as (e_s' σ_s') "(Hnf & SI & HΦ)".
      iExists e_s', σ_s'. iFrame. by iApply "Hmon".
    + iModIntro; iRight; iLeft. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". rewrite /F_ind. iApply ("H1" with "Hmon"). }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame.
      iSplitL "H5 Hmon"; first by rewrite /rec'; iLeft; iFrame.
      iApply (big_sepL2_impl with "H6").
      iIntros "!>" (?????) "?"; by iRight.
    + iModIntro; iRight; iRight. iDestruct "Hcall" as (f K_t v_t K_s' v_s σ_s') "(H1& H2& H3& H4&H5)".
      iExists (f), (K_t), (v_t), (K_s'), (v_s), (σ_s'). iFrame.
      iIntros (? ?) "H1". iLeft. iFrame. iApply ("H5" with "H1").
  Qed.

  Lemma sim_expr_bupd_mono (Φ Φ' : expr_rel) π e_t e_s:
    (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗ e_t ⪯{π} e_s [{ Φ }] -∗ e_t ⪯{π} e_s [{ Φ' }].
  Proof.
    iIntros "Ha Hmon".
    iApply (sim_expr_strong_coind (λ Ψ π e_t e_s, e_t ⪯{π} e_s [{ Φ }] ∗ (∀ e_t e_s : expr Λ, Φ e_t e_s ==∗ Ψ e_t e_s))%I); last by iFrame.
    { solve_proper. }
    iModIntro. clear Φ' π e_t e_s. iIntros (Φ' π e_t e_s) "[Ha Hmon]".
    rewrite sim_expr_eq greatest_def_unfold.
    iApply (least_def_strong_mono with "Hmon Ha").
  Qed.

  Lemma sim_expr_mono (Φ Φ' : expr_rel) π e_t e_s:
    (∀ e_t e_s, Φ e_t e_s -∗ Φ' e_t e_s) -∗ e_t ⪯{π} e_s [{ Φ }] -∗ e_t ⪯{π} e_s [{ Φ' }].
  Proof.
    iIntros "Hmon Ha". iApply (sim_expr_bupd_mono with "[Hmon] Ha").
    iIntros (??) "?". iModIntro. by iApply "Hmon".
  Qed.


  Lemma sim_expr_inner_base G L Φ π e_t e_s :
    ⊢ (Φ e_t e_s) -∗ sim_expr_inner G L Φ π e_t e_s.
  Proof.
    iIntros "He". rewrite /sim_expr. iIntros (??????) "[Hstate [% %]]".
    iModIntro. iLeft. iExists e_s, _. rewrite list_insert_id //. iFrame. iPureIntro. constructor.
  Qed.

  Lemma sim_expr_base Φ e_t e_s π :
    ⊢ (Φ e_t e_s) -∗ sim_expr Φ π e_t e_s.
  Proof.
    iIntros "He". iApply sim_expr_fixpoint. by iApply sim_expr_inner_base.
  Qed.

  Lemma sim_expr_bupd Φ π e_t e_s:
    (e_t ⪯{π} e_s [{ λ e_t' e_s', |==> Φ e_t' e_s' }]) ⊢ e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "H". iApply (sim_expr_bupd_mono with "[] H").
    iIntros (??) "$".
  Qed.


  (* Bind Lemma *)
  Local Definition bind_coind_pred :=
    (λ Φ π e_t e_s, (∃ e_t' e_s' (K_t K_s : ectx Λ),
     ⌜e_t = fill K_t e_t'⌝ ∗ ⌜e_s = fill K_s e_s'⌝ ∗
     e_t' ⪯{π} e_s' [{ λ e_t'' e_s'', fill K_t e_t'' ⪯{π} fill K_s e_s'' [{ Φ }] }]))%I.

  Local Definition bind_coind_rec :=
    (λ Φ π e_t e_s, (∃ e_t' e_s' (K_t K_s : ectx Λ),
      ⌜e_t = fill K_t e_t'⌝ ∗ ⌜e_s = fill K_s e_s'⌝ ∗
      e_t' ⪯{π} e_s' [{ λ e_t'' e_s'', fill K_t e_t'' ⪯{π} fill K_s e_s'' [{ Φ }] }]) ∨ sim_expr Φ π e_t e_s)%I.

  Local Instance bind_coind_pred_ne: NonExpansive (bind_coind_pred : expr_rel → thread_idO -d> expr_rel).
  Proof. solve_proper. Qed.

  Local Instance bind_coind_rec_ne: NonExpansive (bind_coind_rec: expr_rel → thread_idO -d> expr_rel).
  Proof. solve_proper. Qed.

  Lemma sim_expr_bind K_t K_s e_t e_s Φ π :
    e_t ⪯{π} e_s [{ λ e_t' e_s', fill K_t e_t' ⪯{π} fill K_s e_s' [{ Φ }] }] ⊢
    fill K_t e_t ⪯{π} fill K_s e_s [{ Φ }].
  Proof.
    iIntros "H".
    iApply (sim_expr_strong_coind (bind_coind_pred)%I); last first.
    { iExists e_t, e_s, K_t, K_s; iFrame; iSplit; by iPureIntro. }
    iModIntro. clear Φ π e_t e_s K_t K_s.
    iIntros (Φ π e_t' e_s') "IH". change (least_def _ Φ π e_t' e_s') with (least_def bind_coind_rec Φ π e_t' e_s').
    iDestruct "IH" as (e_t e_s K_t K_s) "[-> [-> H]]".
    rewrite {1}sim_expr_eq greatest_def_unfold.
    pose (F := (λ Ψ π e_t e_s, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ sim_expr Φ π (fill K_t e_t) (fill K_s e_s)) -∗ least_def bind_coind_rec Φ π (fill K_t e_t) (fill K_s e_s))%I).
    assert (NonExpansive (F: expr_rel → thread_idO -d> expr_rel)) by solve_proper.
    iAssert (∀ Ψ π e_t e_s, least_def greatest_def Ψ π e_t e_s -∗ F Ψ π e_t e_s)%I as "Hgen"; last first.
    { iApply ("Hgen" with "H"). iIntros (??) "$". }
    clear Φ π e_t e_s. iIntros (Ψ π e_t e_s) "HL".
    iApply (least_def_ind with "[] HL"); clear Ψ π e_t e_s.
    iModIntro. iIntros (Ψ π e_t e_s) "Hinner".
    iIntros (Φ) "Hcont".
    rewrite least_def_unfold. rewrite /sim_expr_inner.
    iIntros (P_t σ_t P_s σ_s T_s K_s') "[Hs [%HT %Hnreach]]". iMod ("Hinner" with "[Hs]") as "H".
    { iFrame. iPureIntro. split; [|done]. by rewrite fill_comp in HT. }
    iDestruct "H" as "[Hval | [Hstep | Hcall]]".
    - iDestruct "Hval" as (e_s' σ_s') "(%Hstutter & Hstate & Hpost)".
      (* we prove that we can stutter the source and still end up at the right place *)
      iSpecialize ("Hcont" with "Hpost"). rewrite sim_expr_unfold.
      iMod ("Hcont" with "[$Hstate]") as "[Val|[Step|Call]]".
      + iPureIntro. rewrite -fill_comp list_lookup_insert_eq; [ | by apply: lookup_lt_Some].
        split; [done|]. apply: pool_safe_no_forks; [done..|].
        apply fill_no_forks. by apply fill_no_forks.
      + iModIntro. iLeft. iDestruct "Val" as (e_s'' σ_s'' Hnf') "[SI HΦ]".
        iExists e_s'', σ_s''. rewrite list_insert_insert_eq. iFrame. iPureIntro. eapply no_forks_trans, Hnf'.
        by eapply fill_no_forks.
      + iModIntro. iRight. iLeft.
        iDestruct "Step" as "($ & Step)".
        iIntros (e_t' efs_t σ_t' Hprim_t).
        iMod ("Step" with "[//]") as "[(-> & SI & Sim)|Step]".
        * destruct (no_forks_inv_r _ _ _ _ _ Hstutter) as [(-> & ->)|(e_s'' & σ_s'' & Hsteps & Hstep)].
          -- iModIntro. iLeft. rewrite -fill_comp list_insert_id //.
             iFrame. iSplit; first done.
             rewrite sim_expr_eq greatest_def_unfold.
             iApply (least_def_mono with "[] Sim").
             clear; iModIntro. iIntros (Φ π e_t e_s) "Hrec". iRight.
             by rewrite sim_expr_eq.
          -- iModIntro. iRight. rewrite -fill_comp.
             iExists (fill K_s e_s''), (fill K_s e_s'), σ_s'', σ_s', []. rewrite app_nil_r.
             iSplit; first by iPureIntro; eapply fill_no_forks.
             iSplit; first by iPureIntro; eapply fill_prim_step, Hstep.
             by iFrame.
        * iDestruct "Step" as (e_s'' e_s''' σ_s'' σ_s''' efs_s Hforks) "(Hprim & SI & Hsim & Hforks)".
          iModIntro. iRight. iExists e_s'', e_s''', σ_s'', σ_s''', efs_s.
          rewrite list_insert_insert_eq. iFrame.
          iSplit; first by iPureIntro; eauto using no_forks_trans, fill_no_forks.
          iApply (big_sepL2_impl with "Hforks"). clear.
          iIntros "!>" (π' e_t e_s ??) "H". rewrite length_insert. by iRight.
      + iModIntro. iRight. iRight. iDestruct "Call" as (f K_t' v_t K_s'' v_s σ_s'' Hfill Hnf) "(HΩ & SI & Hsim)".
        iExists f, K_t', v_t, K_s'', v_s, σ_s''.
        rewrite list_insert_insert_eq. iFrame.
        iSplit; first by iPureIntro.
        iSplit; first by iPureIntro; eauto using no_forks_trans, fill_no_forks.
        clear. iIntros (v_t v_s) "HΩ". iRight. by iApply "Hsim".
    - iModIntro. iRight; iLeft. iDestruct "Hstep" as "[%Hred Hstep]".
      iSplitR. { iPureIntro. by apply fill_reducible. }
      iIntros (e_t' efs σ_t') "%Hstep".
      destruct (fill_reducible_prim_step _ _ _ _ _ _ _ Hred Hstep) as (e_t'' & -> & Hstep').
      iMod ("Hstep" with "[]") as "Hstep". { iPureIntro. apply Hstep'. }
      iModIntro. iDestruct "Hstep" as "[(Hnf & Hstate & Hstutter) | Hstep]".
      + iLeft. iFrame. by iApply "Hstutter".
      + iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs') "(%Hnf & %Hstep'' & Hstate & Hrec & Hfrk)".
        iExists (fill K_s e_s'), (fill K_s e_s''), σ_s', σ_s'', efs'.
        rewrite -fill_comp. iFrame.
        iSplitR. { iPureIntro. by apply fill_no_forks. }
        iSplitR. { iPureIntro. by apply fill_prim_step. }
        iSplitL "Hcont Hrec".
        { iLeft. iExists e_t'', e_s'', K_t, K_s.
          do 2 (iSplitR; first done).
          iApply (sim_expr_mono with "Hcont"); by rewrite sim_expr_eq. }
        { iApply (big_sepL2_impl with "Hfrk").
          iIntros "!>" (?????) "?". iRight. by rewrite sim_expr_eq. }
    - iModIntro. iRight; iRight.
      iDestruct "Hcall" as (f K_t' v_t K_s'' v_s σ_s') "(-> & % & Hval & Hstate & Hrec)".
      iExists f, (comp_ectx K_t K_t'), v_t, (comp_ectx K_s K_s''), v_s, σ_s'.
      rewrite -!fill_comp. iFrame.
      iSplitR; first done.
      iSplitR. { iPureIntro. by apply fill_no_forks. }
      iIntros (v_t' v_s') "Hv". iSpecialize ("Hrec" with "Hv"). iLeft.
      iExists (fill K_t' (of_val v_t')), (fill K_s'' (of_val v_s')), K_t, K_s.
      rewrite -!fill_comp. iSplitR; first done. iSplitR; first done.
      iApply (sim_expr_mono with "Hcont").
      by rewrite sim_expr_eq.
  Qed.

  Lemma sim_expr_decompose e_t e_s Φ Ψ π:
    e_t ⪯{π} e_s [{ Ψ }] -∗
    (∀ e_t e_s, Ψ e_t e_s -∗ e_t ⪯{π} e_s [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "H1 H2".
    replace e_t with (fill empty_ectx e_t) at 2; last apply fill_empty.
    replace e_s with (fill empty_ectx e_s) at 2; last apply fill_empty.
    iApply (sim_expr_bind empty_ectx empty_ectx).
    iApply (sim_expr_mono with "[H2] H1").
    clear. iIntros (e_t e_s). by rewrite !fill_empty.
  Qed.


  Definition join_expr (F: expr_rel -d> thread_idO -d> expr_rel) : expr_rel -d> thread_idO -d> expr_rel :=
    λ Φ π, sim_expr (λ e_t e_s, F Φ π e_t e_s ∨ Φ e_t e_s)%I π.

  Global Instance join_expr_ne F:
    NonExpansive F →
    NonExpansive (join_expr F).
  Proof. solve_proper. Qed.

  Definition lock_step (Φ: expr_rel) π e_t e_s :=
    (∀ P_t σ_t P_s σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' σ_t' efs_t, ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
      ∃ e_s' σ_s', ⌜efs_t = []⌝ ∗ ⌜step_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
      state_interp P_t σ_t' P_s σ_s' (<[π := fill K_s e_s']> T_s) ∗ Φ e_t' e_s')%I.

  Lemma sim_expr_paco F Φ π e_t e_s:
    NonExpansive (F: expr_rel → thread_idO -d> expr_rel) →
    □ (∀ Φ π e_t e_s, F Φ π e_t e_s -∗ lock_step (join_expr F Φ π) π e_t e_s) -∗
    F Φ π e_t e_s -∗ e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros (Hne) "#Hlock_step HF".
    iApply (sim_expr_strong_coind (join_expr F)%I); last first.
    { rewrite /join_expr. iApply sim_expr_base. by iLeft. }
    iModIntro. clear Φ π e_t e_s. iIntros (Φ π e_t e_s) "Hs".
    rewrite {2}/join_expr sim_expr_eq greatest_def_unfold.
    pose (rec := (λ Φ π e_t e_s, join_expr F Φ π e_t e_s ∨ greatest_def Φ π e_t e_s)%I).
    assert (NonExpansive (rec: expr_rel → thread_idO -d> expr_rel)).
    { intros ??? Heq ???. solve_proper. }
    pose (Rec := (λ Ψ π e_t e_s, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ F Φ π e_t e_s ∨ Φ e_t e_s) -∗ least_def rec Φ π e_t e_s)%I).
    assert (NonExpansive (Rec: expr_rel → thread_idO -d> expr_rel)) by solve_proper.
    iApply (least_def_ind Rec with "[] Hs []"); last auto.
    iModIntro. clear Φ π e_t e_s. iIntros (Ψ π e_t e_s) "Hinner".
    iIntros (Φ) "Hmon". rewrite least_def_unfold.
    rewrite /sim_expr_inner.
    iIntros (P_t σ_t P_s σ_s T_s K_s) "[Hs [%HT %Hsafe]]". iMod ("Hinner" with "[$Hs //]") as "H".
    iDestruct "H" as "[Hval | [Hstep | Hcall]]".
    - iDestruct "Hval" as (e_s' σ_s') "(%Hstutter & Hstate & Hpost)".
      (* we prove that we can stutter the source and still end up at the right place *)
      iDestruct ("Hmon" with "Hpost") as "[HF|Hpost]"; last first.
      { iModIntro. iLeft. iExists _, _. iFrame. by iPureIntro. }
      iMod ("Hlock_step" with "HF [$Hstate ]") as "[Hred Hstep]".
      { iPureIntro. rewrite list_lookup_insert_eq; [ | by apply: lookup_lt_Some]. split; [done|].
        apply: pool_safe_no_forks; [done..|]. by apply fill_no_forks. }
      iModIntro. iRight. iLeft. iFrame.
      iIntros (e_t' efs_t σ_t' Hprim_t). iMod ("Hstep" with "[//]") as (e_s'' σ_s'' -> Hnfs) "[SI Hjoin]".
      iModIntro. iRight. rewrite list_insert_insert_eq. iExists e_s', e_s'', σ_s', σ_s'', []; simpl.
      rewrite app_nil_r. iFrame.
      by iPureIntro.
    - iModIntro. iRight; iLeft. iDestruct "Hstep" as "[%Hred Hstep]".
      iSplitR; first done.
      iIntros (e_t' efs σ_t') "%Hstep". iMod ("Hstep" with "[//]") as "[(Hnf & Hstate & Hstutter) | Hstep]".
      + iModIntro. iLeft. iFrame. rewrite /Rec. by iApply "Hstutter".
      + iModIntro. iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs') "(%Hnf & %Hstep'' & Hstate & Hrec' & Hfrk)".
        iExists e_s', e_s'', σ_s', σ_s'', efs'. iFrame.
        repeat (iSplit; first done).
        iSplitL "Hmon Hrec'".
        { iLeft. iApply (sim_expr_mono with "Hmon [Hrec']"); by rewrite sim_expr_eq. }
        iApply (big_sepL2_impl with "Hfrk").
        iIntros "!>" (?????) "?". by iRight.
    - iModIntro. iRight. iRight.
      iDestruct "Hcall" as (f K_t' v_t K_s' v_s σ_s') "(-> & % & Hval & Hstate & Hrec')".
      iExists f, K_t', v_t, K_s', v_s, σ_s'.
      iFrame.
      repeat (iSplitR; first done).
      iIntros (v_t' v_s') "Hv". iSpecialize ("Hrec'" with "Hv").
      iLeft. iApply (sim_expr_mono with "Hmon [Hrec']"); by rewrite sim_expr_eq.
  Qed.

  (* derived things about sim *)
  Lemma sim_value Φ π v_t v_s:
    ⊢ Φ v_t v_s -∗ of_val v_t ⪯{π} of_val v_s {{ Φ }}.
  Proof.
    iIntros "Hv". iApply sim_expr_base.
    iExists v_t, v_s. iFrame. iSplit; done.
  Qed.

  Lemma bupd_sim (Φ : expr_rel) π e_t e_s:
    ⊢ (|==> e_t ⪯{π} e_s [{ Φ }]) -∗ e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Hv". rewrite sim_expr_unfold. iIntros (??????) "H". iMod "Hv". iApply ("Hv" with "H").
  Qed.


  Lemma lift_post_mon Φ Φ' :
    (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) ⊢ (∀ e_t e_s, lift_post Φ e_t e_s -∗ lift_post Φ' e_t e_s).
  Proof.
    iIntros "Hmon" (e_t e_s). rewrite /lift_post. iIntros "He".
    iDestruct "He" as (v_t v_s) "(-> & -> & Hp)". iExists v_t, v_s. do 2 (iSplitR; first done).
    by iApply "Hmon".
  Qed.

  Lemma sim_mono Φ Φ' π :
    (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) ⊢
    ∀ e_s e_t : exprO, e_t ⪯{π} e_s {{ Φ }} -∗ e_t ⪯{π} e_s {{ Φ' }}.
  Proof.
    iIntros "Hmon" (e_s e_t) "Ha". iApply (sim_expr_mono with "[Hmon] Ha").
    by iApply lift_post_mon.
  Qed.

  Lemma sim_bupd Φ π e_t e_s :
    (e_t ⪯{π} e_s {{ λ v_t v_s, |==> Φ v_t v_s }}) ⊢ e_t ⪯{π} e_s {{ Φ }}.
  Proof.
    iIntros "Hv". iApply sim_expr_bupd.
    iApply (sim_expr_mono with "[] Hv").
    iIntros (e_t' e_s') "Ha". rewrite /lift_post.
    iDestruct "Ha" as (v_t v_s) "(-> & -> & >Ha)". iModIntro.
    iExists v_t, v_s. iFrame. iSplit; done.
  Qed.

  Lemma sim_bind e_t e_s K_t K_s Φ π :
    e_t ⪯{π} e_s {{ λ v_t v_s, fill K_t (of_val v_t) ⪯{π} fill K_s (of_val v_s) [{ Φ }] }} ⊢
    fill K_t e_t ⪯{π} fill K_s e_s [{ Φ }].
  Proof.
    iIntros "Ha". iApply sim_expr_bind.
    iApply (sim_expr_mono with "[] Ha").
    rewrite /lift_post.
    iIntros (e_t' e_s') "Hv". by iDestruct "Hv" as (v_t v_s) "(-> & -> & Hsim)".
  Qed.

  (** Corollaries *)
  Lemma sim_call_inline P_t P_s v_t v_s fn_t fn_s f Φ π :
    P_t !! f = Some fn_t →
    P_s !! f = Some fn_s →
    ⊢ progs_are P_t P_s -∗
      ext_rel π v_t v_s -∗
      (∀ v'_t v'_s, ext_rel π v'_t v'_s -∗
        (apply_func fn_t v'_t) ⪯{π} (apply_func fn_s v'_s) [{ Φ }]) -∗
      (of_call f v_t) ⪯{π} (of_call f v_s) [{ Φ }].
 Proof.
    intros Htgt Hsrc. iIntros "#Prog Val Sim".
    rewrite sim_expr_unfold. iIntros (P_t' σ_t P_s' σ_s T_s K_s') "[SI [% %]]".
    iModIntro. iRight. iLeft.
    rewrite /progs_are; iDestruct ("Prog" with "SI") as "[% %]"; subst P_t' P_s'; iClear "Prog".
    iSplit.
    - iPureIntro. eapply base_prim_reducible. eexists _, _, _.
      by eapply call_base_step_intro.
    - iIntros (e_t' efs σ_t' Hstep). iModIntro.
      pose proof (prim_step_call_inv P_t empty_ectx f v_t e_t' σ_t σ_t' efs) as (fn_t' & Heq & -> & -> & ->);
        first by rewrite fill_empty.
      rewrite fill_empty in Hstep. iRight.
      iExists _, _, _, _, _. iSplit; last iSplit; last iSplitL "SI".
      + iPureIntro. eapply no_forks_refl.
      + iPureIntro. eapply base_prim_step, call_base_step_intro, Hsrc.
      + rewrite app_nil_r. iApply (state_interp_pure_prim_step with "SI"); [done|]. intros ?.
        eapply fill_prim_step. eapply base_prim_step, call_base_step_intro, Hsrc.
      + rewrite fill_empty. assert (fn_t' = fn_t) as -> by naive_solver.
        iSpecialize ("Sim" with "Val"). simpl. iFrame.
  Qed.

  Lemma sim_frame_r e_t e_s R Φ π :
    e_t ⪯{π} e_s {{ Φ }} ∗ R ⊢ e_t ⪯{π} e_s {{λ v_t v_s, Φ v_t v_s ∗ R}}.
  Proof.
    iIntros "[Hsim HR]". iApply (sim_mono with "[HR] [Hsim//]"). iIntros (v_t v_s) "H". iFrame.
  Qed.

  Lemma sim_frame_l e_t e_s R Φ π :
    R ∗ e_t ⪯{π} e_s {{ Φ }} ⊢ e_t ⪯{π} e_s {{λ v_t v_s, R ∗ Φ v_t v_s}}.
  Proof.
    iIntros "[HR Hsim]". iApply (sim_mono with "[HR] [Hsim//]"). iIntros (v_t v_s) "H". iFrame.
  Qed.

  Lemma sim_wand e_t e_s Φ Ψ π:
    e_t ⪯{π} e_s {{ Φ }} -∗ (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) -∗ e_t ⪯{π} e_s {{ Ψ }}.
  Proof. iIntros "H Hv". iApply (sim_mono with "Hv H"). Qed.

  Lemma sim_wand_l e_t e_s Φ Ψ π:
    (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) ∗ e_t ⪯{π} e_s {{ Φ }} ⊢ e_t ⪯{π} e_s {{ Ψ }}.
  Proof. iIntros "[Hv H]". iApply (sim_wand with "H Hv"). Qed.

  Lemma sim_wand_r e_t e_s Φ Ψ π:
    e_t ⪯{π} e_s {{ Φ }} ∗ (∀ v_t v_s, Φ v_t v_s -∗ Ψ v_t v_s) ⊢ e_t ⪯{π} e_s {{ Ψ }}.
  Proof. iIntros "[H Hv]". iApply (sim_wand with "H Hv"). Qed.

  Lemma sim_expr_wand e_t e_s Φ Ψ π :
    e_t ⪯{π} e_s [{ Φ }] -∗ (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ e_t ⪯{π} e_s [{ Ψ }].
  Proof. iIntros "H Hv". iApply (sim_expr_mono with "Hv H"). Qed.

  (** Update the SI. Useful when we use the SI to encode invariants. *)
  Definition update_si_strong e_s π (P : PROP) : PROP :=
    (∀ P_t σ_t P_s σ_s T_s K_s,
        state_interp P_t σ_t P_s σ_s T_s -∗
        ⌜T_s !! π = Some (fill K_s e_s) ∧ pool_safe P_s T_s σ_s⌝ ==∗
        state_interp P_t σ_t P_s σ_s T_s ∗ P).
  Instance update_si_strong_proper e π : Proper ((≡) ==> (≡)) (update_si_strong e π).
  Proof. solve_proper. Qed.
  Lemma sim_update_si_strong e_t e_s Φ π :
    update_si_strong e_s π (e_t ⪯{π} e_s [{ Φ }]) -∗ e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Hupd". rewrite {2}(sim_expr_unfold Φ π e_t e_s).
    iIntros (??????) "[Hstate %Hnreach]". iMod ("Hupd" with "Hstate [//]") as "[Hstate Hsim]".
    rewrite {1}sim_expr_unfold. iApply "Hsim". by iFrame.
  Qed.

  Definition update_si (P : PROP) :=
    (∀ P_t σ_t P_s σ_s T_s, state_interp P_t σ_t P_s σ_s T_s ==∗ state_interp P_t σ_t P_s σ_s T_s ∗ P)%I.
  Instance update_si_proper : Proper ((≡) ==> (≡)) update_si.
  Proof. solve_proper. Qed.
  Lemma sim_update_si e_t e_s Φ π :
    update_si (e_t ⪯{π} e_s [{ Φ }]) -∗ e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Hupd". iApply sim_update_si_strong.
    iIntros (??????) "Hstate %". by iApply "Hupd".
  Qed.

  Lemma sim_step_source e_t e_s Φ π :
    (∀ P_s σ_s P_t σ_t T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
         ∃ e_s' σ_s', ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
                       state_interp P_t σ_t P_s σ_s' (<[π := fill K_s e_s']> T_s) ∗ e_t ⪯{π} e_s' [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
   rewrite sim_expr_unfold. iIntros "Hsource" (P_t σ_t P_s σ_s T_s K_s) "[Hstate [%HT %Hsafe]]".
    iMod ("Hsource" with "[$Hstate //]") as (e_s' σ_s') "(%Hexec & Hstate & Hsim)".
    rewrite {1}sim_expr_unfold.
    iMod ("Hsim" with "[Hstate]") as "Hsim".
    { iFrame. iPureIntro. rewrite list_lookup_insert_eq; [ | by apply: lookup_lt_Some]. split; [done|].
        apply: pool_safe_no_forks; [done..|]. by apply fill_no_forks. }
    iModIntro. iDestruct "Hsim" as "[Hval | [Hstep | Hcall]]".
    - iLeft. iDestruct "Hval" as (e_s'' σ_s'') "(% & Hstate & Hphi)".
      rewrite list_insert_insert_eq. iExists e_s'', σ_s''. iFrame. iPureIntro. by eapply no_forks_trans.
    - iDestruct "Hstep" as "(%&Hstep)". iRight; iLeft.
      iSplitR; first by iPureIntro.
      iIntros (e_t' efs_t σ_t') "Hprim". iMod ("Hstep" with "Hprim") as "[Hstutter | Hred]"; iModIntro.
      + (* which path we want to take depends on the rtc we have *)
        eapply no_forks_inv_r in Hexec as [(-> & ->)|(e_s'' & σ_s'' & Hnfs & Hnf)].
        { (* no step, just mirror the stuttering *) iLeft. by rewrite list_insert_id. }
        (* we have actually taken a source step *)
        iRight. iExists e_s'', e_s', σ_s'', σ_s', []. rewrite app_nil_r.
        iDestruct "Hstutter" as "(-> & SI & Hsim)"; simpl; iFrame.
        by iPureIntro.
      + iRight. iDestruct "Hred" as (e_s'' e_s''' σ_s'' σ_s''' efs_s) "(%Hnfs & Hstep & Hstate & Hsim & Hfrks)".
        rewrite list_insert_insert_eq length_insert.
        iExists e_s'', e_s''', σ_s'', σ_s''', efs_s. iFrame. iPureIntro.
        by eapply no_forks_trans.
    - iDestruct "Hcall" as (f K_t v_t K_s' v_s σ_s'') "(-> & % & Hv & Hstate & Hsim)".
      iRight; iRight. iExists f, K_t, v_t, K_s', v_s, σ_s''. rewrite list_insert_insert_eq. iFrame.
      iPureIntro. split; first done.
      by eapply no_forks_trans.
  Qed.

  (* the step case of the simulation relation, but the two cases are combined into an rtc in the source *)
  Lemma sim_step_target e_t e_s Φ π:
    (∀ P_t P_s σ_t σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
      ∃ e_s' σ_s', ⌜efs_t = []⌝ ∗ ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t' P_s σ_s' (<[π:=fill K_s e_s']>T_s) ∗ e_t' ⪯{π} e_s' [{ Φ }]) -∗
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Hsim". rewrite sim_expr_unfold. iIntros (??????) "[Hstate [% %]]".
    iMod ("Hsim" with "[$Hstate ]") as "[Hred Hsim]"; first done. iModIntro. iRight; iLeft.
    iFrame. iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hsim" with "Hstep") as (e_s' σ_s') "(-> & %Hs & ? & ?)".
    apply no_forks_inv_r in Hs as [ [-> ->] | (e_s'' & σ_s'' & Hstep & Hsteps)].
    - iLeft. rewrite list_insert_id //. by iFrame.
    - iRight; iExists e_s'', e_s', σ_s'', σ_s', []. rewrite app_nil_r. iModIntro; simpl; iFrame.
      by iPureIntro.
  Qed.

  (** ** source_red judgment *)
  (** source_red allows to focus the reasoning on the source expression
    (while being able to switch back and forth to the full simulation at any point) *)
  Definition source_red_rec (Ψ : expr Λ → PROP) π (rec : exprO → PROP) e_s :=
    (∀ P_t σ_t P_s σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      (∃ e_s' σ_s', ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t P_s σ_s' (<[π := fill K_s e_s']> T_s) ∗ rec e_s')
      ∨ (state_interp P_t σ_t P_s σ_s T_s ∗ Ψ e_s))%I.

  Lemma source_red_rec_mono Ψ π l1 l2 :
    □ (∀ e, l1 e -∗ l2 e) -∗ ∀ e, source_red_rec Ψ π l1 e -∗ source_red_rec Ψ π l2 e.
  Proof.
    iIntros "Hmon" (e) "Hl1". rewrite /source_red_rec.
    iIntros (??????) "Hstate". iMod ("Hl1" with "Hstate") as "[Hstep | Hstuck]".
    - iDestruct "Hstep" as (e_s' σ_s') "(?&?&?)". iModIntro. iLeft.
      iExists e_s', σ_s'. iFrame. by iApply "Hmon".
    - iModIntro; iRight. iFrame.
  Qed.

  Instance source_red_mon π Ψ : BiMonoPred (source_red_rec Ψ π).
  Proof.
    constructor.
    - iIntros (l1 l2 Hne Hne') "H". by iApply source_red_rec_mono.
    - intros l Hne n e1 e2 Heq. apply (discrete_iff _ _ _) in Heq as ->. done.
  Qed.

  Definition source_red_def Ψ π := bi_least_fixpoint (source_red_rec Ψ π).
  Lemma source_red_def_unfold Ψ π e_s : source_red_def Ψ π e_s ⊣⊢ source_red_rec Ψ π (source_red_def Ψ π) e_s.
  Proof. by rewrite /source_red_def least_fixpoint_unfold. Qed.

  Definition source_red_aux : seal (λ e π Ψ, source_red_def Ψ π e).
  Proof. by eexists. Qed.
  Definition source_red := source_red_aux.(unseal).
  Lemma source_red_eq : source_red = (λ e π Ψ, source_red_def Ψ π e).
  Proof. rewrite -source_red_aux.(seal_eq) //. Qed.

  Lemma source_red_strong_ind Ψ (Ψi : expr Λ → PROP) π :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO, source_red_rec Ψ π (λ e', Ψi e' ∧ source_red_def Ψ π e') e -∗ Ψi e) -∗
    ∀ e : exprO, source_red_def Ψ π e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /source_red_def.
    by iApply (@least_fixpoint_ind _ _ _ (source_red_rec Ψ π) _ Ψi).
  Qed.

  Lemma source_red_ind Ψ (Ψi : expr Λ → PROP) π :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO, source_red_rec Ψ π Ψi e -∗ Ψi e) -∗
    ∀ e : exprO, source_red_def Ψ π e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /source_red_def.
    by iApply (@least_fixpoint_iter _ _ _ (source_red_rec Ψ π) Ψi).
  Qed.

  Lemma source_red_unfold e_s π Ψ :
    source_red e_s π Ψ ⊣⊢
      ∀ P_t σ_t P_s σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s) ∧
          pool_safe P_s T_s σ_s⌝ ==∗
        (∃ e_s' σ_s', ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t P_s σ_s' (<[π := fill K_s e_s']> T_s) ∗ source_red e_s' π Ψ)
        ∨ (state_interp P_t σ_t P_s σ_s T_s ∗ Ψ e_s).
  Proof. rewrite source_red_eq /= source_red_def_unfold //. Qed.

  Lemma source_red_elim Ψ π e_s :
    source_red e_s π Ψ -∗
    ∀ P_t σ_t P_s σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ∃ e_s' σ_s', ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗ Ψ e_s' ∗ state_interp P_t σ_t P_s σ_s' (<[π:=fill K_s e_s']>T_s).
  Proof.
    iIntros "H". rewrite source_red_eq.
    iApply (source_red_ind _ (λ e_s, ∀ P_t σ_t P_s σ_s  T_s K_s,
       state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s) ∧ pool_safe P_s T_s σ_s⌝ ==∗
        ∃ e_s' σ_s', ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗ Ψ e_s' ∗ state_interp P_t σ_t P_s σ_s' (<[π:=fill K_s e_s']>T_s))%I);
    last done.
    clear e_s. iModIntro. iIntros (e_s) "IH". iIntros (P_t σ_t P_s σ_s T_s K_s) "[HSI [% %]]".
    rewrite /source_red_rec.
    iMod ("IH" with "[$HSI //]") as "IH".
    iDestruct "IH" as "[Hstep | [Hstate Hp]]"; first last.
    { iModIntro. iExists e_s, σ_s. rewrite list_insert_id //. iFrame. iPureIntro. eapply no_forks_refl. }
    iDestruct "Hstep" as (e_s' σ_s') "(% & Hstate & IH)".
    iMod ("IH" with "[$Hstate]") as (e_s'' σ_s'') "(% & Hp & Hs)".
    { iPureIntro. rewrite list_lookup_insert_eq; [ | by apply: lookup_lt_Some]. split; [done|].
      apply: pool_safe_no_forks; [done..|]. apply fill_no_forks. eauto using no_forks_step, no_forks_refl. }
    iModIntro. rewrite list_insert_insert_eq.
    iExists e_s'', σ_s''; iFrame. iPureIntro. by apply: no_forks_trans.
  Qed.

  Lemma source_red_base Ψ e_s π:
    (|==> Ψ e_s) ⊢ source_red e_s π Ψ.
  Proof.
    iIntros "Hpsi". rewrite source_red_unfold.
    iIntros (P_s σ_s P_t σ_t T_s K_s) "[Hstate %]". iRight. iMod ("Hpsi"). iModIntro. iFrame.
  Qed.

  Lemma source_red_step Ψ e_s π :
    (* FIXME: quantification order is inconsistent with simulation relation. *)
    (∀ P_t σ_t P_s σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      (∃ e_s' σ_s', ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t P_s σ_s' (<[π := fill K_s e_s']> T_s) ∗ source_red e_s' π Ψ)) -∗
    source_red e_s π Ψ.
  Proof.
    iIntros "Hstep". rewrite source_red_unfold.
    iIntros (P_t σ_t P_s σ_s T_s K_s) "Hstate". iLeft. iMod ("Hstep" with "Hstate"). iModIntro.
    iFrame.
  Qed.

  Lemma source_red_sim_expr e_s e_t Φ π :
    (source_red e_s π (λ e_s', e_t ⪯{π} e_s' [{ Φ }])) ⊢
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Hsource". iPoseProof (source_red_elim with "Hsource") as "Hsource".
    iApply sim_step_source. iIntros (??????) "Hstate".
    iMod ("Hsource" with "Hstate") as (e_s' σ_s') "(?&?&?)".
    iModIntro. iExists e_s', σ_s'. iFrame.
  Qed.

  Lemma source_red_update_si e_s Φ π :
    update_si (source_red e_s π Φ) ⊢ source_red e_s π Φ.
  Proof.
    iIntros "Hupd". iApply source_red_step.
    iIntros (??????) "[Hs [% _]]". iExists _, _. rewrite list_insert_id //.
    iMod ("Hupd" with "Hs") as "[$ $]". iPureIntro. apply: no_forks_refl.
  Qed.

  Lemma source_red_pool_reach_stuck e_s π Ψ :
    (∀ P_t σ_t P_s σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s -∗ ⌜T_s !! π = Some (fill K_s e_s)⌝ ==∗
        ⌜pool_reach_stuck P_s T_s σ_s⌝) -∗
    source_red e_s π Ψ.
  Proof.
    iIntros "Hstuck". rewrite source_red_unfold.
    iIntros (??????) "[Hstate [% %Hsafe]]". iMod ("Hstuck" with "Hstate [//]") as "%".
    exfalso; by eapply pool_reach_stuck_not_safe.
  Qed.

  Lemma source_red_reach_stuck e_s π Ψ :
    (∀ P_t σ_t P_s σ_s T_s, state_interp P_t σ_t P_s σ_s T_s ==∗ ⌜reach_stuck P_s e_s σ_s⌝) -∗
    source_red e_s π Ψ.
  Proof.
    iIntros "Hstuck". iApply source_red_pool_reach_stuck.
    iIntros (??????) "Hstate %HT". iMod ("Hstuck" with "Hstate") as "%". iPureIntro.
    apply: pool_reach_stuck_reach_stuck; [by apply: fill_reach_stuck| done].
  Qed.

  Lemma source_red_stuck e_s π Ψ :
    (∀ P_t σ_t P_s σ_s T_s, state_interp P_t σ_t P_s σ_s T_s ==∗ ⌜stuck P_s e_s σ_s⌝) ⊢
    source_red e_s π Ψ.
  Proof.
    iIntros "Hstuck". iApply source_red_reach_stuck.
    iIntros (?????) "SI". iMod ("Hstuck" with "SI") as "%Hstuck". iModIntro.
    iPureIntro. eexists [e_s], _, []. split; eauto using Pool_steps_refl.
    exists e_s, 0. split; done.
  Qed.

  Lemma source_red_bind e_s K_s π Ψ :
    source_red e_s π (λ e_s', source_red (fill K_s e_s') π Ψ) ⊢
    source_red (fill K_s e_s) π Ψ.
  Proof.
    iIntros "He".
    iApply (source_red_ind _ (λ e_s, source_red (fill K_s e_s) π Ψ)%I); last by rewrite source_red_eq /flip.
    iModIntro. clear e_s. iIntros (e_s) "IH". rewrite source_red_eq /flip source_red_def_unfold.
    iIntros (??????) "[Hstate [%HT %Hsafe]]". rewrite fill_comp in HT. iMod ("IH" with "[$Hstate]") as "IH".
    { done. }
    iDestruct "IH" as "[Hstep | [Hstate Hred]]".
    { iModIntro. iDestruct "Hstep" as (e_s' σ_s') "(%&?&?)". iLeft.
      iExists (fill K_s e_s'), σ_s'. rewrite fill_comp. iFrame. iPureIntro.
      by apply: fill_no_forks. }
    rewrite source_red_def_unfold. rewrite -fill_comp in HT.
    iMod ("Hred" with "[$Hstate//]") as "[Hstep | Hred]"; iModIntro; eauto.
  Qed.

  Lemma source_red_mono Φ Ψ :
    (∀ e_s, Φ e_s -∗ Ψ e_s) ⊢
    ∀ e_s π, source_red e_s π Φ -∗ source_red e_s π Ψ.
  Proof.
    iIntros "Hw" (e_s π) "Ht".
    iApply (source_red_ind _ (λ e_s, (∀ e_s', Φ e_s' -∗ Ψ e_s') -∗ source_red e_s π Ψ)%I with "[] [Ht] Hw"); last by rewrite source_red_eq /flip.
    iModIntro. clear e_s. iIntros (e_s) "IH Hw".
    rewrite source_red_unfold. iIntros (??????) "Hstate".
    iMod ("IH" with "Hstate") as  "[Hs | [Hstate Hphi]]"; iModIntro.
    - iDestruct "Hs" as (e_s' σ_s') "(Hs & Hstate & IH)".
      iLeft; iExists e_s', σ_s'. iFrame. by iApply "IH".
    - iRight. iFrame. by iApply "Hw".
  Qed.

  Lemma source_red_wand Φ Ψ π e_s :
    source_red e_s π Φ -∗ (∀ e_s', Φ e_s' -∗ Ψ e_s') -∗ source_red e_s π Ψ.
  Proof. iIntros "Ht Hw". iApply (source_red_mono with "Hw Ht"). Qed.

  (** ** same thing for target *)
  Definition target_red_rec (Ψ : expr Λ → PROP) (rec : exprO → PROP) e_t :=
    (∀ P_t σ_t P_s σ_s T_s, state_interp P_t σ_t P_s σ_s T_s ==∗
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t' efs_t, ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
        ⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s T_s ∗ rec e_t')
      ∨ (state_interp P_t σ_t P_s σ_s T_s ∗ Ψ e_t))%I.

  Lemma target_red_mon Ψ l1 l2 :
    □ (∀ e, l1 e -∗ l2 e) -∗ ∀ e, target_red_rec Ψ l1 e -∗ target_red_rec Ψ l2 e.
  Proof.
    iIntros "Hmon" (e) "Hl1". rewrite /source_red_rec.
    iIntros (?????) "Hstate". iMod ("Hl1" with "Hstate") as "[[Hred Hstep] | Hstuck]".
    - iModIntro. iLeft. iFrame.
      iIntros (e_t' σ_t' efs_t) "Hprim". iMod ("Hstep" with "Hprim") as "(Hnfs & Hstate & Hprim)".
      iModIntro. iFrame. by iApply "Hmon".
    - iModIntro; iRight. iFrame.
  Qed.

  Instance target_red_rec_mono Ψ : BiMonoPred (target_red_rec Ψ).
  Proof.
    constructor.
    - iIntros (l1 l2 Hn1 Hn2) "H". by iApply target_red_mon.
    - intros l Hne n e1 e2 Heq. apply (discrete_iff _ _ _) in Heq as ->. done.
  Qed.

  Definition target_red_def Ψ := bi_least_fixpoint (target_red_rec Ψ).
  Lemma target_red_def_unfold Ψ e_t : target_red_def Ψ e_t ⊣⊢ target_red_rec Ψ (target_red_def Ψ) e_t.
  Proof. by rewrite /target_red_def least_fixpoint_unfold. Qed.

  Definition target_red_aux : seal (flip target_red_def).
  Proof. by eexists. Qed.
  Definition target_red := target_red_aux.(unseal).
  Lemma target_red_eq : target_red = flip target_red_def.
  Proof. rewrite -target_red_aux.(seal_eq) //. Qed.

  Lemma target_red_strong_ind Ψ (Ψi : expr Λ → PROP) :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO, target_red_rec Ψ (λ e', Ψi e' ∧ target_red_def Ψ e') e -∗ Ψi e) -∗
    ∀ e : exprO, target_red_def Ψ e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /target_red_def.
    by iApply (@least_fixpoint_ind _ _ _ (target_red_rec Ψ) _ Ψi).
  Qed.

  Lemma target_red_unfold e_t Ψ :
    target_red e_t Ψ ⊣⊢
      ∀ P_t σ_t P_s σ_s T_s, state_interp P_t σ_t P_s σ_s T_s ==∗
        (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t' efs_t, ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
          ⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s T_s ∗ target_red e_t' Ψ)
        ∨ (state_interp P_t σ_t P_s σ_s T_s ∗ Ψ e_t).
  Proof. rewrite target_red_eq; simpl. by rewrite target_red_def_unfold. Qed.

  Lemma target_red_ind Ψ (Ψi : expr Λ → PROP) :
    Proper ((≡) ==> (≡)) Ψi →
    □ (∀ e : exprO, target_red_rec Ψ Ψi e -∗ Ψi e) -∗
    ∀ e : exprO, target_red_def Ψ e -∗ Ψi e.
  Proof.
    iIntros (Hproper) "H". rewrite /target_red_def.
    by iApply (@least_fixpoint_iter _ _ _ (target_red_rec Ψ) Ψi).
  Qed.

  Lemma target_red_base Ψ e_t :
    (|==> Ψ e_t) ⊢ target_red e_t Ψ.
  Proof.
    iIntros "Hpsi". rewrite target_red_unfold.
    iIntros (P_s σ_s P_t σ_t T_s) "Hstate". iRight. iMod ("Hpsi"). iModIntro. iFrame.
  Qed.

  Lemma target_red_step Ψ e_t :
    (∀ P_t σ_t P_s σ_s T_s, state_interp P_t σ_t P_s σ_s T_s ==∗
      (⌜ reducible P_t e_t σ_t⌝ ∗ ∀ e_t' σ_t' efs_t, ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
        ⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s T_s ∗ target_red e_t' Ψ)) -∗
    target_red e_t Ψ .
  Proof.
    iIntros "Hstep". rewrite target_red_unfold.
    iIntros (P_t σ_t P_s σ_s T_s) "Hstate". iLeft. iMod ("Hstep" with "Hstate"). iModIntro. iFrame.
  Qed.

  Lemma target_red_sim_expr e_s e_t Φ π:
    (target_red e_t (λ e_t', e_t' ⪯{π} e_s [{ Φ }])) ⊢
    e_t ⪯{π} e_s [{ Φ }].
  Proof.
    iIntros "Htarget". rewrite target_red_eq.
    iApply (target_red_ind _ (λ e_t, e_t ⪯{π} e_s [{ Φ }])%I); last by rewrite /flip.
    iModIntro. clear e_t. iIntros (e_t) "Htarget".
    rewrite sim_expr_unfold. iIntros (??????) "[Hstate Hnreach]".
    iMod ("Htarget" with "Hstate") as "[[Hred Hstep] | (Hstate & Hsim)]".
    - iModIntro. iRight; iLeft. iFrame. iIntros (e_t' efs_t σ_t') "Hprim".
      (* stuttering step *) iLeft.
      iMod ("Hstep" with "Hprim") as "Hstep". iModIntro; iFrame.
    - rewrite {1}sim_expr_unfold. by iMod ("Hsim" with "[$Hstate $Hnreach]").
  Qed.

  Lemma target_red_bind e_t K_t Ψ :
    target_red e_t (λ e_t', target_red (fill K_t e_t') Ψ) ⊢
    target_red (fill K_t e_t) Ψ.
  Proof.
    iIntros "He".
    iApply (target_red_ind _ (λ e_t, target_red (fill K_t e_t) Ψ)%I); last by rewrite target_red_eq /flip.
    iModIntro. clear e_t. iIntros (e_t) "IH". rewrite target_red_eq /flip target_red_def_unfold.
    iIntros (?????) "Hstate". iMod ("IH" with "Hstate") as "IH".
    iDestruct "IH" as "[[%Hred Hstep] | [Hstate Hred]]"; first last.
    - rewrite target_red_def_unfold.
      iMod ("Hred" with "Hstate") as "[Hstep | Hred]"; iModIntro; eauto.
    - iModIntro. iLeft. iSplitR; first by eauto using fill_reducible.
      iIntros (e_t' σ_t' efs_t) "%Hprim".
      eapply fill_reducible_prim_step in Hprim as (e_t'' & -> & H); last done.
      by iMod ("Hstep" with "[% //]").
  Qed.

  Lemma target_red_mono Φ Ψ :
    (∀ e_t, Φ e_t -∗ Ψ e_t) ⊢
    ∀ e_t, target_red e_t Φ -∗ target_red e_t Ψ.
  Proof.
    iIntros "Hw" (e_t) "Ht".
    iApply (target_red_ind _ (λ e_t, (∀ e_t', Φ e_t' -∗ Ψ e_t') -∗ target_red e_t Ψ)%I with "[] [Ht] Hw"); last by rewrite target_red_eq /flip.
    iModIntro. clear e_t. iIntros (e_t) "IH Hw".
    rewrite target_red_unfold. iIntros (?????) "Hstate".
    iMod ("IH" with "Hstate") as "[[%Hred IH] | [Hstate Hphi]]"; iModIntro.
    - iLeft; iSplitR; first done. iIntros (???) "Hprim".
      iMod ("IH" with "Hprim") as "(? & ? & IH)"; iModIntro; iFrame. by iApply "IH".
    - iRight. iFrame. by iApply "Hw".
  Qed.

  Lemma target_red_wand Φ Ψ e_t :
    target_red e_t Φ -∗ (∀ e_t', Φ e_t' -∗ Ψ e_t') -∗ target_red e_t Ψ.
  Proof. iIntros "Ht Hw". iApply (target_red_mono with "Hw Ht"). Qed.
End fix_lang.

Arguments lift_post : simpl never.

(** Coq gives up TC search prematurely for our Sim/SimE instances, so declare
them as hint extern instead. See <https://github.com/coq/coq/pull/13952>. *)
Global Hint Extern 0 (Sim _ _) => apply sim_stutter : typeclass_instances.
Global Hint Extern 0 (SimE _ _) => apply sim_expr_stutter : typeclass_instances.
