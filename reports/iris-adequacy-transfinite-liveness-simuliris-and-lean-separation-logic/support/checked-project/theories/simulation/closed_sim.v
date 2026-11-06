(** * Closed simulation (without the call case) *)
From iris.bi Require Import bi fixpoint_mono.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import language.
From simuliris.simulation Require Export simulation slsls gen_log_rel.
Import bi.


Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP, !BiPersistentlyForall PROP}.
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


  (** Global simulation relation with stuttering *)

  Section sim_def.
  Definition csim_expr_inner (greatest_rec : expr_rel -d> thread_id -d> expr_rel) (least_rec : expr_rel -d> thread_id -d> expr_rel) : expr_rel -d> thread_id -d> expr_rel :=
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
    )%I.

  Lemma csim_expr_inner_mono l1 l2 g1 g2:
    ⊢ □ (∀ Φ π e_t e_s, l1 Φ π e_t e_s -∗ l2 Φ π e_t e_s)
    → □ (∀ Φ π e_t e_s, g1 Φ π e_t e_s -∗ g2 Φ π e_t e_s)
    → ∀ Φ π e_t e_s, csim_expr_inner g1 l1 Φ π e_t e_s -∗ csim_expr_inner g2 l2 Φ π e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ π e_t e_s) "Hsim".
    rewrite /csim_expr_inner. iIntros (P_t σ_t P_s σ_s T_s K_s) "Ha".
    iMod ("Hsim" with "Ha") as "[Hval | Hstep]"; iModIntro.
    + iLeft. iApply "Hval".
    + iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". by iApply "Hleast". }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame.
      iSplitL "H5"; first by iApply "Hgreatest".
      iApply (big_sepL2_impl with "H6 []"); simpl.
      iIntros "!>" (?????). by iApply "Hgreatest".
  Qed.

  (* the strongest monotonicity lemma we can prove, allows for changing the post condition and recursive occurrences *)
  Lemma csim_expr_inner_strong_mono l1 l2 g1 g2:
    ⊢ □ (∀ Φ π Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, l1 Φ π e_t e_s -∗ l2 Ψ π e_t e_s)
    → □ (∀ Φ π Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, g1 Φ π e_t e_s -∗ g2 Ψ π e_t e_s)
    → ∀ Φ π Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, csim_expr_inner g1 l1 Φ π e_t e_s -∗ csim_expr_inner g2 l2 Ψ π e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ π Ψ) "HΦΨ". iIntros (e_t e_s) "Hsim".
    rewrite /csim_expr_inner. iIntros (P_t σ_t P_s σ_s T_s K_s) "Ha".
    iMod ("Hsim" with "Ha") as "[Hval | Hstep]"; iModIntro.
    + iLeft. iDestruct "Hval" as (e_s' σ_s') "(Hnf & SI & HΦ)".
      iExists e_s', σ_s'. iFrame. by iApply "HΦΨ".
    + iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". by iApply ("Hleast" with "HΦΨ H1"). }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame.
      iSplitL "H5 HΦΨ"; first by iApply ("Hgreatest" with "HΦΨ H5").
      iApply (big_sepL2_impl with "H6 []"); simpl.
      iIntros "!>" (?????) "Hg". iApply ("Hgreatest" with "[] Hg").
      by iIntros (??) "?".
  Qed.

  Instance csim_expr_inner_ne:
    ∀n, Proper ((dist n ==> dist n ==> dist n) ==> (dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n ==> dist n) csim_expr_inner.
  Proof.
    intros n G1 G2 HG L1 L2 HL Φ Ψ HΦΨ π π' Hπ%discrete_iff%leibniz_equiv e_t e_t' Ht%discrete_iff%leibniz_equiv e_s e_s' Hs%discrete_iff%leibniz_equiv; [|apply _..].
    subst; rewrite /csim_expr_inner.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
  Qed.

  Instance csim_expr_inner_proper:
    Proper ((equiv ==> equiv ==> equiv) ==> (equiv ==> equiv ==> equiv) ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) csim_expr_inner.
  Proof.
    intros G1 G2 HG L1 L2 HL Φ Ψ HΦΨ π π' Hπ%leibniz_equiv e_t e_t' Ht%leibniz_equiv e_s e_s' Hs%leibniz_equiv.
    subst; rewrite /csim_expr_inner.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
  Qed.

  Local Instance closed_least_def_body_mono greatest_rec :
    NonExpansive (greatest_rec) →
    BiMonoPred (λ (least_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO -d> PROP), uncurry4 (csim_expr_inner greatest_rec (curry4 least_rec))).
  Proof.
    intros Hg; constructor.
    - intros L1 L2 HL1 HL2. iIntros "#H" (x).
      destruct x as (((Φ & π) & e_t) & e_s); simpl.
      iApply (csim_expr_inner_mono with "[] []"); iModIntro; clear.
      { iIntros (G π e_t e_s); unfold curry4; iApply "H". }
      iIntros (G π e_t e_s) "$".
    - intros l Hne n x y Heq.
      destruct x as (((Φ & π) & e_t) & e_s); simpl.
      destruct y as (((Ψ & π') & e_t') & e_s'); simpl.
      destruct Heq as [[[Heq1 Heq2] Heq3] Heq4]; simpl in Heq1, Heq2, Heq3, Heq4.
      eapply csim_expr_inner_ne; eauto.
      + intros ?????->%leibnizO_leibniz. by eapply Hg.
      + intros ????????; rewrite /curry4. eapply Hne.
        repeat split; simpl; done.
  Qed.

  Definition closed_least_def (greatest_rec : expr_rel -d> thread_id -d> expr_rel) : expr_rel -d> thread_id -d> expr_rel :=
    curry4 (bi_least_fixpoint (λ (least_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO → PROP), uncurry4 (csim_expr_inner greatest_rec (curry4 least_rec)))).


  Global Instance closed_least_def_ne :
    NonExpansive2 closed_least_def.
  Proof.
    rewrite /closed_least_def; intros n x y Heq ??????.
    rewrite {1 3}/curry4. apply least_fixpoint_ne; last by repeat split.
    intros ? [[[??]?] ?]; simpl.
    rewrite /csim_expr_inner. repeat f_equiv; apply Heq.
  Qed.

  Lemma closed_least_def_mono R R' π Φ e_t e_s:
    NonExpansive (R': expr_rel -d> thread_id -d> expr_rel) →
    <pers> (∀ Φ π e_t e_s, R Φ π e_t e_s -∗ R' Φ π e_t e_s) -∗
    closed_least_def R Φ π e_t e_s -∗ closed_least_def R' Φ π e_t e_s.
  Proof.
    iIntros (Hne) "#Hmon". rewrite /closed_least_def {1 3}/curry4.
    iIntros "Hleast". iApply (least_fixpoint_iter with "[] Hleast"); clear Φ π e_t e_s.
    iModIntro. iIntros ([[[Φ π] e_t] e_s]).
    erewrite least_fixpoint_unfold; last first.
    { eapply closed_least_def_body_mono, _. }
    rewrite {1 3}/uncurry4.
    iApply (csim_expr_inner_mono with "[] []").
    { iModIntro. iIntros (Φ' π' e_t' e_s') "$". }
      iModIntro; iIntros (Φ' π' e_t' e_s'); by iApply "Hmon".
  Qed.

  Lemma closed_least_def_unfold G Φ π e_t e_s:
    NonExpansive G →
    closed_least_def G Φ π e_t e_s ≡ csim_expr_inner G (closed_least_def G) Φ π e_t e_s.
  Proof.
    intros ?; rewrite {1}/closed_least_def {1}/curry4 least_fixpoint_unfold {1}/uncurry4 //=.
  Qed.

  Instance closed_greatest_def_body_mono :
    BiMonoPred (λ (greatest_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO → PROP), uncurry4 (closed_least_def (curry4 greatest_rec))).
  Proof.
    constructor.
    - intros G1 G2 HG1 HG2. iIntros "#H" (x).
      destruct x as [[[Φ π] e_t] e_s]; rewrite /uncurry4.
      iApply closed_least_def_mono.
      { (* FIXME: TC inference should solve this *) solve_proper. }
      iModIntro.
      iIntros (Φ' π' e_t' e_s'); iApply "H".
    - intros G Hne n x y Heq. rewrite /least_def !uncurry4_curry4.
      eapply least_fixpoint_ne'; last done.
      intros L HL m [[[Φ π] e_t] e_s] [[[Ψ π'] e_t'] e_s'] Heq'; simpl.
      eapply csim_expr_inner_ne; [| |eapply Heq'..].
      + solve_proper.
      + solve_proper.
  Qed.

  Definition closed_greatest_def : expr_rel -d> thread_id -d> expr_rel :=
    curry4 (bi_greatest_fixpoint (λ (greatest_rec: prodO (prodO (prodO (exprO -d> exprO -d> PROP) thread_idO) exprO) exprO → PROP), uncurry4 (closed_least_def (curry4 greatest_rec)))).

  Lemma closed_greatest_def_unfold Φ π e_t e_s:
    closed_greatest_def Φ π e_t e_s ≡ closed_least_def closed_greatest_def Φ π e_t e_s.
  Proof.
    rewrite {1}/closed_greatest_def {1}/curry4 greatest_fixpoint_unfold {1}/uncurry4 //=.
  Qed.

  Global Instance closed_greatest_def_ne: NonExpansive closed_greatest_def.
  Proof. solve_proper. Qed.

  Global Instance closed_greatest_def_proper: Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) closed_greatest_def.
  Proof.
    intros Φ Ψ Heq π π' <-%leibniz_equiv e_t e_t' <-%leibniz_equiv e_s e_s' <-%leibniz_equiv.
    revert π e_t e_s. change (closed_greatest_def Φ ≡ closed_greatest_def Ψ).
    eapply ne_proper; first apply _. done.
  Qed.

  Lemma closed_greatest_def_fixpoint Φ π e_t e_s:
    closed_greatest_def Φ π e_t e_s ≡ csim_expr_inner closed_greatest_def closed_greatest_def Φ π e_t e_s.
  Proof.
    rewrite closed_greatest_def_unfold closed_least_def_unfold.
    eapply csim_expr_inner_proper; eauto.
    - solve_proper.
    - intros Φ' Ψ' Heq. intros ??? ??. rewrite -closed_greatest_def_unfold.
      f_equiv; done.
  Qed.

  End sim_def.

  Definition csim_expr_aux : seal closed_greatest_def.
  Proof. by eexists. Qed.
  Definition csim_expr := (csim_expr_aux).(unseal).
  Lemma csim_expr_eq : csim_expr = λ Φ π e_t e_s, @closed_greatest_def Φ π e_t e_s.
  Proof. rewrite -csim_expr_aux.(seal_eq) //. Qed.

  Lemma csim_expr_fixpoint Φ π e_t e_s:
    csim_expr Φ π e_t e_s ⊣⊢ csim_expr_inner csim_expr csim_expr Φ π e_t e_s.
  Proof.
    rewrite csim_expr_eq closed_greatest_def_fixpoint //.
  Qed.

  Lemma csim_expr_unfold Φ π e_t e_s:
    csim_expr Φ π e_t e_s ⊣⊢
    (∀ P_t σ_t P_s σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ -∗ |==>
      (* base case *)
      (∃ e_s' σ_s', ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
        state_interp P_t σ_t P_s σ_s' (<[π := fill K_s e_s']> T_s) ∗ Φ e_t e_s')

      ∨ (* step case *)
      (⌜reducible P_t e_t σ_t⌝ ∗ ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ -∗ |==>
        (* stuttering *)
        (⌜efs_t = []⌝ ∗ state_interp P_t σ_t' P_s σ_s T_s ∗ csim_expr Φ π e_t' e_s) ∨
        (* take a step *)
        (∃ e_s' e_s'' σ_s' σ_s'' efs_s,
          ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗
          ⌜prim_step P_s e_s' σ_s' e_s'' σ_s'' efs_s⌝ ∗
          state_interp P_t σ_t' P_s σ_s'' (<[π := fill K_s e_s'']> T_s ++ efs_s) ∗
          csim_expr Φ π e_t' e_s'' ∗
          [∗ list] π'↦e_t; e_s ∈ efs_t; efs_s, csim_expr (lift_post (ext_rel (length T_s + π'))) (length T_s + π') e_t e_s))
    )%I.
  Proof.
    rewrite csim_expr_fixpoint /csim_expr_inner //.
  Qed.

  Global Instance csim_expr_ne:
    NonExpansive4 (csim_expr: expr_rel → thread_id → expr_rel).
  Proof. rewrite csim_expr_eq. apply _. Qed.

  Global Instance csim_expr_proper:
    Proper ((pointwise_relation (expr Λ) (pointwise_relation (expr Λ) (≡))) ==> eq ==> eq ==> eq ==> (≡)) (csim_expr).
  Proof.
    intros p1 p2 Heq2 π π' -> e e' -> e1 e1' ->.
    rewrite !csim_expr_eq. eapply closed_greatest_def_proper; done.
  Qed.


  Existing Instances closed_least_def_body_mono closed_greatest_def_body_mono.
  (* any post-fixed point is included in the gfp *)
  Lemma csim_expr_strong_coind (F : expr_rel → thread_id -d> expr_rel) :
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ closed_least_def (λ Φ π e_t e_s, F Φ π e_t e_s ∨ csim_expr Φ π e_t e_s) Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ csim_expr Φ π e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (Φ π e_t e_s) "HF".
    rewrite csim_expr_eq /closed_greatest_def {3}/curry4.
    set (F_curry := uncurry4 F).
    assert (NonExpansive F_curry) as Hne by solve_proper.
    change (F Φ π e_t e_s) with (F_curry (Φ, π, e_t, e_s)).
    remember (Φ, π, e_t, e_s) as p eqn:Heqp. rewrite -Heqp; clear Φ π e_t e_s Heqp.
    iApply (greatest_fixpoint_coind _ F_curry with "[] HF").
    iModIntro. iIntros ([[[Φ π] e_t] e_s]); simpl.
    rewrite /F_curry.
    iApply ("HPre" $! Φ π e_t e_s).
  Qed.

  Lemma csim_expr_coind (F : expr_rel → thread_id -d> expr_rel) :
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ closed_least_def F Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, F Φ π e_t e_s -∗ csim_expr Φ π e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (Φ π e_t e_s) "HF".
    iApply (csim_expr_strong_coind with "[] HF"); clear Φ π e_t e_s.
    iModIntro; iIntros (Φ π e_t e_s) "HF".
    iDestruct ("HPre" with "HF") as "HF".
    iApply (closed_least_def_mono with "[] HF"); first by solve_proper.
    iModIntro. clear Φ π e_t e_s. iIntros (Φ π e_t e_s) "HF". by iLeft.
  Qed.

  Lemma closed_least_def_strong_ind (F R: expr_rel → thread_id -d> expr_rel):
    NonExpansive R →
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, csim_expr_inner R (λ Ψ π e_t e_s, F Ψ π e_t e_s ∧ closed_least_def R Ψ π e_t e_s) Φ π e_t e_s -∗ F Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, closed_least_def R Φ π e_t e_s -∗ F Φ π e_t e_s.
  Proof.
    iIntros (Hne1 Hne2) "#HPre". iIntros (Φ π e_t e_s) "HF".
    rewrite {2}/closed_least_def {1}/curry4.
    set (F_curry := uncurry4 F).
    assert (NonExpansive F_curry) by solve_proper.
    change (F Φ π e_t e_s) with (F_curry (Φ, π, e_t, e_s)).
    remember (Φ, π, e_t, e_s) as p eqn:Heqp. rewrite -Heqp; clear Φ π e_t e_s Heqp.
    iApply (least_fixpoint_ind _ F_curry with "[] HF").
    iModIntro. iIntros ([[[Φ π] e_t] e_s]); simpl.
    rewrite /F_curry {1}/curry4 {1}/uncurry4.
    iIntros "H". iApply "HPre". iExact "H".
  Qed.

  Lemma closed_least_def_ind (F R: expr_rel → thread_id -d> expr_rel):
    NonExpansive R →
    NonExpansive F →
    ⊢ (□ ∀ Φ π e_t e_s, csim_expr_inner R F Φ π e_t e_s -∗ F Φ π e_t e_s)
      -∗ ∀ Φ π e_t e_s, closed_least_def R Φ π e_t e_s -∗ F Φ π e_t e_s.
  Proof.
    iIntros (Hne1 Hne2) "#HPre". iApply closed_least_def_strong_ind.
    iModIntro. iIntros (Φ π e_t e_s) "Hsim".
    iApply "HPre". iApply (csim_expr_inner_mono with "[] [] Hsim"); last by auto.
    iModIntro. iIntros (Φ' π' e_t' e_s') "H". iApply bi.and_elim_l. iApply "H".
  Qed.

  (* we change the predicate beause at every recursive ocurrence,
     we give back ownership of the monotonicity assumption *)
  Lemma closed_least_def_strong_mono (rec : expr_rel → thread_idO -d> expr_rel) Φ Φ' π e_t e_s:
    NonExpansive rec →
     (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗
     closed_least_def rec Φ π e_t e_s -∗
     closed_least_def (λ Ψ π e_t e_s, rec Φ π e_t e_s ∗ (∀ e_t e_s, Φ e_t e_s ==∗ Ψ e_t e_s) ∨ rec Ψ π e_t e_s) Φ' π e_t e_s.
  Proof.
    iIntros (Hne) "Hmon Hleast". iRevert (Φ') "Hmon".
    pose (rec' := (λ Φ Ψ π e_t e_s, rec Φ π e_t e_s ∗ (∀ e_t e_s, Φ e_t e_s ==∗ Ψ e_t e_s) ∨ rec Ψ π e_t e_s)%I).
    pose (F_ind := (λ Φ π e_t e_s, ∀ Φ', (∀ e_t e_s : expr Λ, Φ e_t e_s ==∗ Φ' e_t e_s) -∗ closed_least_def (rec' Φ) Φ' π e_t e_s)%I).
    assert (NonExpansive2 (rec': expr_rel -d> expr_rel -d> thread_idO -d> expr_rel)) as Rne.
    { solve_proper. }
    assert (NonExpansive (F_ind: expr_rel -d> thread_idO -d> expr_rel)).
    { clear Φ π e_t e_s. intros n Φ Ψ Heq π e_t e_s.
      rewrite /F_ind; do 3 f_equiv; first (repeat f_equiv; by apply Heq).
      eapply closed_least_def_ne; [ |done..]. intros ?. eapply (Rne n Φ Ψ Heq). done. }
    iApply (closed_least_def_ind F_ind rec with "[] Hleast"); clear Φ π e_t e_s.
    iModIntro. iIntros (Φ π e_t e_s) "Hrec". iIntros (Φ') "Hmon".
    rewrite closed_least_def_unfold /csim_expr_inner.

    iIntros (P_t σ_t P_s σ_s T_s K_s) "Ha".
    iMod ("Hrec" with "Ha") as "[Hval | Hstep]".
    + iLeft. iDestruct "Hval" as (e_s' σ_s') "(Hnf & SI & HΦ)".
      iExists e_s', σ_s'. iFrame. by iApply "Hmon".
    + iModIntro; iRight. iDestruct "Hstep" as "[Hred Hr]"; iFrame "Hred".
      iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hr" with "Hstep") as "[Hstay | Hstep]"; iModIntro.
      { iLeft. iDestruct "Hstay" as "[$ [$ H1]]". rewrite /F_ind. iApply ("H1" with "Hmon"). }
      iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs_s) "(H1 & H2 & H4 & H5 & H6)".
      iExists (e_s'), e_s'', σ_s', σ_s'', efs_s. iFrame.
      iSplitL "H5 Hmon"; first by rewrite /rec'; iLeft; iFrame.
      iApply (big_sepL2_impl with "H6").
      iIntros "!>" (?????) "?"; by iRight.
  Qed.

  Lemma csim_expr_bupd_mono Φ Φ' π e_t e_s:
    (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗ csim_expr Φ π e_t e_s -∗ csim_expr Φ' π e_t e_s.
  Proof.
    iIntros "Ha Hmon".
    iApply (csim_expr_strong_coind (λ Ψ π e_t e_s, csim_expr Φ π e_t e_s ∗ (∀ e_t e_s : expr Λ, Φ e_t e_s ==∗ Ψ e_t e_s))%I); last by iFrame.
    { solve_proper. }
    iModIntro. clear Φ' π e_t e_s. iIntros (Φ' π e_t e_s) "[Ha Hmon]".
    rewrite csim_expr_eq closed_greatest_def_unfold.
    iApply (closed_least_def_strong_mono with "Hmon Ha").
  Qed.

  Lemma csim_expr_mono Φ Φ' π e_t e_s:
    (∀ e_t e_s, Φ e_t e_s -∗ Φ' e_t e_s) -∗ csim_expr Φ π e_t e_s -∗ csim_expr Φ' π e_t e_s.
  Proof.
    iIntros "Hmon Ha". iApply (csim_expr_bupd_mono with "[Hmon] Ha").
    iIntros (??) "?". iModIntro. by iApply "Hmon".
  Qed.


  Lemma csim_expr_inner_base G L Φ π e_t e_s :
    ⊢ (Φ e_t e_s) -∗ csim_expr_inner G L Φ π e_t e_s.
  Proof.
    iIntros "He". rewrite /csim_expr. iIntros (??????) "[Hstate [% %]]".
    iModIntro. iLeft. iExists e_s, _. rewrite list_insert_id //. iFrame. iPureIntro. constructor.
  Qed.

  Lemma csim_expr_base Φ π e_t e_s :
    ⊢ (Φ e_t e_s) -∗ csim_expr Φ π e_t e_s.
  Proof.
    iIntros "He". iApply csim_expr_fixpoint. by iApply csim_expr_inner_base.
  Qed.

  Lemma csim_expr_bupd Φ π e_t e_s:
    (csim_expr (λ e_t' e_s', |==> Φ e_t' e_s') π e_t e_s) -∗ csim_expr Φ π e_t e_s.
  Proof.
    iIntros "H". iApply (csim_expr_bupd_mono with "[] H").
    iIntros (??) "$".
  Qed.


  (* Bind Lemma *)
  Local Definition bind_coind_pred :=
    (λ Φ π e_t e_s, (∃ e_t' e_s' (K_t K_s : ectx Λ),
     ⌜e_t = fill K_t e_t'⌝ ∗ ⌜e_s = fill K_s e_s'⌝ ∗
     csim_expr (λ e_t'' e_s'', csim_expr Φ π (fill K_t e_t'') (fill K_s e_s'')) π e_t' e_s'))%I.

  Local Definition bind_coind_rec :=
    (λ Φ π e_t e_s, (∃ e_t' e_s' (K_t K_s : ectx Λ),
      ⌜e_t = fill K_t e_t'⌝ ∗ ⌜e_s = fill K_s e_s'⌝ ∗
      csim_expr (λ e_t'' e_s'', csim_expr Φ π (fill K_t e_t'') (fill K_s e_s'')) π e_t' e_s') ∨ csim_expr Φ π e_t e_s)%I.

  Local Instance bind_coind_pred_ne: NonExpansive (bind_coind_pred: expr_rel → thread_idO -d> expr_rel).
  Proof.
    rewrite /bind_coind_pred. solve_proper_prepare; repeat f_equiv.
    intros ??; by f_equiv.
  Qed.

  Local Instance bind_coind_rec_ne: NonExpansive (bind_coind_rec: expr_rel → thread_idO -d> expr_rel).
  Proof.
    rewrite /bind_coind_pred. solve_proper_prepare; repeat f_equiv; last done.
    intros ??; by f_equiv.
  Qed.


  Lemma csim_expr_bind K_t K_s e_t e_s Φ π :
    csim_expr (λ e_t' e_s', csim_expr Φ π (fill K_t e_t') (fill K_s e_s')) π e_t e_s -∗
    csim_expr Φ π (fill K_t e_t) (fill K_s e_s).
  Proof.
    iIntros "H".
    iApply (csim_expr_strong_coind (bind_coind_pred)%I); last first.
    { iExists e_t, e_s, K_t, K_s; iFrame; iSplit; by iPureIntro. }
    iModIntro. clear Φ π e_t e_s K_t K_s.
    iIntros (Φ π e_t' e_s') "IH". change (closed_least_def _ Φ π e_t' e_s') with (closed_least_def (bind_coind_rec) Φ π e_t' e_s').
    iDestruct "IH" as (e_t e_s K_t K_s) "[-> [-> H]]".
    rewrite {1}csim_expr_eq closed_greatest_def_unfold.
    pose (F := (λ Ψ π e_t e_s, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ csim_expr Φ π (fill K_t e_t) (fill K_s e_s)) -∗ closed_least_def (bind_coind_rec) Φ π (fill K_t e_t) (fill K_s e_s))%I).
    assert (NonExpansive (F: expr_rel → thread_idO -d> expr_rel)) by solve_proper.
    iAssert (∀ Ψ π e_t e_s, closed_least_def (closed_greatest_def) Ψ π e_t e_s -∗ F Ψ π e_t e_s)%I as "Hgen"; last first.
    { iApply ("Hgen" with "H"). iIntros (??) "$". }
    clear Φ π e_t e_s. iIntros (Ψ π e_t e_s) "HL".
    iApply (closed_least_def_ind with "[] HL"); clear Ψ π e_t e_s.
    iModIntro. iIntros (Ψ π e_t e_s) "Hinner".
    iIntros (Φ) "Hcont".
    rewrite closed_least_def_unfold. rewrite /csim_expr_inner.
    iIntros (P_t σ_t P_s σ_s T_s K_s') "[Hs [%HT %Hnreach]]". iMod ("Hinner" with "[Hs]") as "H".
    { iFrame. iPureIntro. split; [|done]. by rewrite fill_comp in HT. }
    iDestruct "H" as "[Hval | Hstep]".
    - iDestruct "Hval" as (e_s' σ_s') "(%Hstutter & Hstate & Hpost)".
      (* we prove that we can stutter the source and still end up at the right place *)
      iSpecialize ("Hcont" with "Hpost"). rewrite csim_expr_unfold.
      iMod ("Hcont" with "[$Hstate]") as "[Val|Step]".
      + iPureIntro. rewrite -fill_comp list_lookup_insert_eq; [ | by apply: lookup_lt_Some].
        split; [done|]. apply: pool_safe_no_forks; [done..|].
        apply fill_no_forks. by apply fill_no_forks.
      + iModIntro. iLeft. iDestruct "Val" as (e_s'' σ_s'' Hnf') "[SI HΦ]".
        iExists e_s'', σ_s''. rewrite list_insert_insert_eq. iFrame. iPureIntro. eapply no_forks_trans, Hnf'.
        by eapply fill_no_forks.
      + iModIntro. iRight.
        iDestruct "Step" as "($ & Step)".
        iIntros (e_t' efs_t σ_t' Hprim_t).
        iMod ("Step" with "[//]") as "[(-> & SI & Sim)|Step]".
        * destruct (no_forks_inv_r _ _ _ _ _ Hstutter) as [(-> & ->)|(e_s'' & σ_s'' & Hsteps & Hstep)].
          -- iModIntro. iLeft. rewrite -fill_comp list_insert_id //.
             iFrame. iSplit; first done.
             rewrite csim_expr_eq closed_greatest_def_unfold.
             iApply (closed_least_def_mono with "[] Sim").
             clear; iModIntro. iIntros (Φ π e_t e_s) "Hrec". iRight.
             by rewrite csim_expr_eq.
          -- iModIntro. iRight. rewrite -fill_comp.
             iExists (fill K_s e_s''), (fill K_s e_s'), σ_s'', σ_s', []. rewrite app_nil_r.
             iSplit; first by iPureIntro; eapply fill_no_forks.
             iSplit; first by iPureIntro; eapply fill_prim_step, Hstep.
             by iFrame.
        * iDestruct "Step" as (e_s'' e_s''' σ_s'' σ_s''' efs_s Hforks) "(Hprim & Hlen & SI & Hforks)".
          iModIntro. iRight. iExists e_s'', e_s''', σ_s'', σ_s''', efs_s.
          rewrite list_insert_insert_eq. iFrame.
          iSplit; first by iPureIntro; eauto using no_forks_trans, fill_no_forks.
          iApply (big_sepL2_impl with "Hforks"). clear.
          iIntros "!>" (π' e_t e_s ??) "H". rewrite length_insert. by iRight.
    - iModIntro. iRight;  iDestruct "Hstep" as "[%Hred Hstep]".
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
          iApply (csim_expr_mono with "Hcont"); by rewrite csim_expr_eq. }
        { iApply (big_sepL2_impl with "Hfrk").
          iIntros "!>" (?????) "?". iRight. by rewrite csim_expr_eq. }
  Qed.

  Lemma csim_expr_decompose e_t e_s π Φ Ψ:
    csim_expr Ψ π e_t e_s -∗
    (∀ e_t e_s, Ψ e_t e_s -∗ csim_expr Φ π e_t e_s) -∗
    csim_expr Φ π e_t e_s.
  Proof.
    iIntros "H1 H2".
    rewrite -{2}(fill_empty e_t) -{2}(fill_empty e_s).
    iApply (csim_expr_bind empty_ectx empty_ectx).
    iApply (csim_expr_mono with "[H2] H1").
    clear. iIntros (e_t e_s). by rewrite !fill_empty.
  Qed.


  Definition cjoin_expr (F: expr_rel -d> thread_idO -d> expr_rel) : expr_rel -d> thread_idO -d> expr_rel :=
    λ Φ π, csim_expr (λ e_t e_s, F Φ π e_t e_s ∨ Φ e_t e_s)%I π.

  Global Instance cjoin_expr_ne F:
    NonExpansive F →
    NonExpansive (cjoin_expr F).
  Proof.
    intros ???? Heq ???. rewrite /cjoin_expr. f_equiv.
    intros ??. repeat f_equiv; by apply Heq.
  Qed.
  Lemma csim_expr_paco F Φ π e_t e_s:
    NonExpansive (F: expr_rel → thread_idO -d> expr_rel) →
    □ (∀ Φ π e_t e_s, F Φ π e_t e_s -∗ lock_step (cjoin_expr F Φ π) π e_t e_s) -∗
    F Φ π e_t e_s -∗ csim_expr Φ π e_t e_s.
  Proof.
    iIntros (Hne) "#Hlock_step HF".
    iApply (csim_expr_strong_coind (cjoin_expr F)%I); last first.
    { rewrite /cjoin_expr. iApply csim_expr_base. by iLeft. }
    iModIntro. clear Φ π e_t e_s. iIntros (Φ π e_t e_s) "Hs".
    rewrite {2}/cjoin_expr csim_expr_eq closed_greatest_def_unfold.
    pose (rec := (λ Φ π e_t e_s, cjoin_expr F Φ π e_t e_s ∨ closed_greatest_def Φ π e_t e_s)%I).
    assert (NonExpansive (rec: expr_rel → thread_idO -d> expr_rel)).
    { intros ??? Heq ???. solve_proper. }
    pose (Rec := (λ Ψ π e_t e_s, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ F Φ π e_t e_s ∨ Φ e_t e_s) -∗ closed_least_def rec Φ π e_t e_s)%I).
    assert (NonExpansive (Rec: expr_rel → thread_idO -d> expr_rel)) by solve_proper.
    iApply (closed_least_def_ind Rec with "[] Hs []"); last auto.
    iModIntro. clear Φ π e_t e_s. iIntros (Ψ π e_t e_s) "Hinner".
    iIntros (Φ) "Hmon". rewrite closed_least_def_unfold.
    rewrite /csim_expr_inner.
    iIntros (P_t σ_t P_s σ_s T_s K_s) "[Hs [%HT %Hsafe]]". iMod ("Hinner" with "[$Hs //]") as "H".
    iDestruct "H" as "[Hval | Hstep]".
    - iDestruct "Hval" as (e_s' σ_s') "(%Hstutter & Hstate & Hpost)".
      (* we prove that we can stutter the source and still end up at the right place *)
      iDestruct ("Hmon" with "Hpost") as "[HF|Hpost]"; last first.
      { iModIntro. iLeft. iExists _, _. iFrame. by iPureIntro. }
      iMod ("Hlock_step" with "HF [$Hstate ]") as "[Hred Hstep]".
      { iPureIntro. rewrite list_lookup_insert_eq; [ | by apply: lookup_lt_Some]. split; [done|].
        apply: pool_safe_no_forks; [done..|]. by apply fill_no_forks. }
      iModIntro. iRight. iFrame.
      iIntros (e_t' efs_t σ_t' Hprim_t). iMod ("Hstep" with "[//]") as (e_s'' σ_s'' -> Hnfs) "[SI Hjoin]".
      iModIntro. iRight. rewrite list_insert_insert_eq. iExists e_s', e_s'', σ_s', σ_s'', []; simpl.
      rewrite app_nil_r. iFrame.
      by iPureIntro.
    - iModIntro. iRight. iDestruct "Hstep" as "[%Hred Hstep]".
      iSplitR; first done.
      iIntros (e_t' efs σ_t') "%Hstep". iMod ("Hstep" with "[//]") as "[(Hnf & Hstate & Hstutter) | Hstep]".
      + iModIntro. iLeft. iFrame. rewrite /Rec. by iApply "Hstutter".
      + iModIntro. iRight. iDestruct "Hstep" as (e_s' e_s'' σ_s' σ_s'' efs') "(%Hnf & %Hstep'' & Hstate & Hrec' & Hfrk)".
        iExists e_s', e_s'', σ_s', σ_s'', efs'. iFrame.
        repeat (iSplit; first done).
        iSplitL "Hmon Hrec'".
        { iLeft. iApply (csim_expr_mono with "Hmon [Hrec']"); by rewrite csim_expr_eq. }
        iApply (big_sepL2_impl with "Hfrk").
        iIntros "!>" (?????) "?". by iRight.
  Qed.

  Lemma bupd_csim_expr Φ π e_t e_s:
    ⊢ (|==> csim_expr Φ π e_t e_s) -∗ csim_expr Φ π e_t e_s.
  Proof.
    iIntros "Hv". rewrite csim_expr_unfold. iIntros (??????) "H". iMod "Hv". iApply ("Hv" with "H").
  Qed.


  Lemma csim_step_source e_t e_s Φ π :
    (∀ P_s σ_s P_t σ_t T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ∃ e_s' σ_s', ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t P_s σ_s' (<[π:=fill K_s e_s']>T_s) ∗ csim_expr Φ π e_t e_s') -∗
      csim_expr Φ π e_t e_s.
  Proof.
    rewrite csim_expr_unfold. iIntros "Hsource" (P_t σ_t P_s σ_s T_s K_s) "[Hstate [%HT %Hsafe]]".
    iMod ("Hsource" with "[$Hstate //]") as (e_s' σ_s') "(%Hexec & Hstate & Hsim)".
    rewrite {1}csim_expr_unfold.
    iMod ("Hsim" with "[Hstate]") as "Hsim".
    { iFrame. iPureIntro. rewrite list_lookup_insert_eq; [ | by apply: lookup_lt_Some]. split; [done|].
        apply: pool_safe_no_forks; [done..|]. by apply fill_no_forks. }
    iModIntro. iDestruct "Hsim" as "[Hval | Hstep]".
    - iLeft. iDestruct "Hval" as (e_s'' σ_s'') "(% & Hstate & Hphi)". rewrite list_insert_insert_eq.
      iExists e_s'', σ_s''. iFrame. iPureIntro. by eapply no_forks_trans.
    - iDestruct "Hstep" as "(%&Hstep)". iRight.
      iSplitR; first by iPureIntro.
      iIntros (e_t' efs_t σ_t') "Hprim". iMod ("Hstep" with "Hprim") as "[Hstutter | Hred]"; iModIntro.
      + (* which path we want to take depends on the rtc we have *)
        eapply no_forks_inv_r in Hexec as [(-> & ->)|(e_s'' & σ_s'' & Hnfs & Hnf)].
        { (* no step, just mirror the stuttering *) iLeft. rewrite list_insert_id //. }
        (* we have actually taken a source step *)
        iRight. iExists e_s'', e_s', σ_s'', σ_s', []. rewrite app_nil_r.
        iDestruct "Hstutter" as "(-> & SI & Hsim)"; simpl; iFrame.
        by iPureIntro.
      + iRight. iDestruct "Hred" as (e_s'' e_s''' σ_s'' σ_s''' efs_s) "(%Hnfs & Hstep & Hstate & Hsim & Hfrks)".
        rewrite list_insert_insert_eq length_insert.
        iExists e_s'', e_s''', σ_s'', σ_s''', efs_s. iFrame. iPureIntro.
        by eapply no_forks_trans.
  Qed.

  (* the step case of the simulation relation, but the two cases are combined into an rtc in the source *)
  Lemma csim_step_target e_t e_s Φ π:
    (∀ P_t P_s σ_t σ_s T_s K_s, state_interp P_t σ_t P_s σ_s T_s ∗ ⌜T_s !! π = Some (fill K_s e_s)
        ∧ pool_safe P_s T_s σ_s⌝ ==∗
      ⌜reducible P_t e_t σ_t⌝ ∗
      ∀ e_t' efs_t σ_t', ⌜prim_step P_t e_t σ_t e_t' σ_t' efs_t⌝ ==∗
      ∃ e_s' σ_s', ⌜efs_t = []⌝ ∗ ⌜steps_no_fork P_s e_s σ_s e_s' σ_s'⌝ ∗ state_interp P_t σ_t' P_s σ_s' (<[π:=fill K_s e_s']>T_s) ∗ csim_expr Φ π e_t' e_s') -∗
    csim_expr Φ π e_t e_s.
  Proof.
    iIntros "Hsim". rewrite csim_expr_unfold. iIntros (??????) "[Hstate [% %]]".
    iMod ("Hsim" with "[$Hstate ]") as "[Hred Hsim]"; first done. iModIntro. iRight.
    iFrame. iIntros (e_t' efs_t σ_t') "Hstep". iMod ("Hsim" with "Hstep") as (e_s' σ_s') "(-> & %Hs & ? & ?)".
    apply no_forks_inv_r in Hs as [ [-> ->] | (e_s'' & σ_s'' & Hstep & Hsteps)].
    - iLeft. rewrite list_insert_id //. by iFrame.
    - iRight; iExists e_s'', e_s', σ_s'', σ_s', []. rewrite app_nil_r. iModIntro; simpl; iFrame.
      by iPureIntro.
  Qed.


  (** We show that the open simulation for all functions in the program implies the closed simulation *)
  Lemma open_to_closed P_t P_s Φ e_t e_s π:
    prog_rel P_t P_s -∗
    progs_are P_t P_s -∗
    sim_expr Φ π e_t e_s -∗
    csim_expr Φ π e_t e_s.
  Proof.
    rewrite /prog_rel; iIntros "#Hloc #Hprog Hsim".
    assert (NonExpansive (sim_expr : expr_rel → thread_id -d> expr_rel)).
    { solve_proper. }
    iApply (csim_expr_coind (sim_expr) with "[] Hsim"); clear Φ π e_t e_s.
    iModIntro. iIntros (Φ π e_t e_s).
    rewrite {1}sim_expr_eq greatest_def_unfold.
    iIntros "H". iApply (least_def_ind (closed_least_def (sim_expr)) with "[] H"); clear Φ π e_t e_s.
    iModIntro. iIntros (Φ π e_t e_s) "Hsim".
    rewrite closed_least_def_unfold.
    iIntros (P_t' σ_t P_s' σ_s T_s K_s) "[Hstate [% %]]".
    rewrite /progs_are; iDestruct ("Hprog" with "Hstate") as "[% %]"; subst P_t' P_s'.
    iMod ("Hsim" with "[$Hstate //]") as "[Hsim|[Hsim|Hsim]]"; iModIntro; [ eauto | rewrite sim_expr_eq; eauto | ].
    iDestruct "Hsim" as (f K_t v_t K_s' v_s σ_s') "(% & %Hnfs & Hval & Hstate & Hcont)".
    subst e_t. iRight.
    (* the function is in the source table *)
    edestruct (@safe_call_in_prg Λ) as (fn_s & Hdef_s); [ |done|].
    { eapply fill_safe. by eapply pool_safe_threads_safe. }

    (* we prove reducibility and the step case *)
    iSplit.
    - iAssert (∃ fn_t, ⌜P_t !! f = Some fn_t⌝)%I as (fn_t) "%".
      { iDestruct ("Hloc" $! _ _ Hdef_s) as (fn_t) "[% _]"; by eauto. }
      iPureIntro. eexists _, _, _.
      by apply fill_prim_step, base_prim_step, call_base_step_intro.
    - iIntros (e_t' efs_t σ_t' Hstep).
      apply prim_step_call_inv in Hstep as (fn_t & Hdef & -> & -> & ->).
      iModIntro. iRight.
      iExists (fill K_s' (of_call f v_s)), (fill K_s' (apply_func fn_s v_s)), σ_s', σ_s', [].
      iFrame. iSplit; first done. iSplit.
      { iPureIntro. by apply fill_prim_step, base_prim_step, call_base_step_intro. }
      iSplitL "Hstate".
      { rewrite app_nil_r. iPoseProof (state_interp_pure_prim_step with "Hstate") as "Hstate".
        { apply list_lookup_insert_eq. by eapply lookup_lt_Some. }
        2: { rewrite list_insert_insert_eq. iFrame. }
        intros σ_s''. eapply fill_prim_step, fill_prim_step. by eapply base_prim_step, call_base_step_intro.
      }
      simpl; iSplit; last done.
      iApply sim_expr_bind. iDestruct ("Hloc" $! _ _ Hdef_s) as (fn_t') "[% Hectx]".
      replace fn_t' with fn_t by naive_solver.
      iApply (sim_expr_mono with "[Hcont] [Hectx Hval]"); last by iApply "Hectx".
      iIntros (e_t' e_s'). iDestruct 1 as (v_t' v_s' -> ->) "Hval".
      rewrite sim_expr_eq. by iApply "Hcont".
  Qed.

  Lemma open_to_closed_call P_t P_s f v_t v_s π:
    is_Some (P_s !! f) →
    prog_rel P_t P_s -∗
    progs_are P_t P_s -∗
    ext_rel π v_t v_s -∗
    csim_expr (lift_post (ext_rel π)) π (of_call f v_t) (of_call f v_s).
  Proof.
    iIntros ([fn_s Hlook]) "#Hloc #Hprogs Hval".
    iApply (open_to_closed with "Hloc Hprogs").
    rewrite /prog_rel.
    iDestruct "Hloc" as "#Hloc".
    iDestruct ("Hloc" $! _ _ Hlook) as (fn_t) "[% Hsim]".
    iApply (sim_call_inline with "[$] Hval"); eauto.
    iIntros (??) "Hrel". iApply "Hsim". done.
  Qed.
End fix_lang.
