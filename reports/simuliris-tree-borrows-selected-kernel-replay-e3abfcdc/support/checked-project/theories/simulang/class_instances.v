From stdpp Require Import gmap.
From simuliris.simulation Require Import language lifting.
From simuliris.simulang Require Export lang.
From simuliris.simulang Require Import tactics.

(** * Instances of the [SafeImplies] class *)

Section safe_implies.
  Implicit Types (e : expr) (v : val) (σ : state).

  (* [to_val] has a better computational behavior around calls *)
  Lemma language_to_val_eq e :
    language.to_val e = to_val e.
  Proof.
    rewrite /language.to_val /language.to_class; cbn.
    destruct (to_val e) eqn:Heq.
    - by rewrite (to_val_class _ _ Heq).
    - destruct to_class as [ [] | ] eqn:Heq';
        [ by rewrite (to_class_val _ _ Heq') in Heq | done | done].
  Qed.
End safe_implies.

Ltac solve_sub_redexes_are_values :=
  let K := fresh "K" in
  let e' := fresh "e'" in
  let Heq := fresh "Heq" in
  let Hv := fresh "Hv" in
  let IH := fresh "IH" in
  let Ki := fresh "Ki" in
  let Ki' := fresh "Ki'" in
  intros K e' Heq Hv;
  destruct K as [ | Ki K]; first (done);
  exfalso; induction K as [ | Ki' K IH] in e', Ki, Hv, Heq |-*;
  [destruct Ki; inversion Heq; subst; cbn in *; congruence
  | eapply IH; first (by rewrite Heq);
    rewrite language_to_val_eq; apply fill_item_val_none;
      by rewrite -language_to_val_eq].

Section safe_implies.
  Implicit Types (e : expr) (v : val) (σ : state).

  (* Slightly hacky proof tactic for proving [SafeImplies] goals.
    Basically the same proof script works for all these proofs, but there don't seem to be nice more general lemmas. *)
  Ltac prove_safe_implies :=
    let Hsafe := fresh in
    let Hval := fresh in
    let Hred := fresh in
    let Hhead := fresh in
    intros Hsafe; specialize (Hsafe _ _ _ (Pool_steps_refl _ _ _) _ 0 ltac:(done)) as [Hval | Hred];
    [ rewrite language_to_val_eq in Hval; simpl in Hval; destruct Hval as [? [=]] |
      destruct Hred as (? & ? & ? & Hhead%prim_base_step);
      [ (* this need not complete the proof and may generate a proof obligation *)
        inversion Hhead; subst; try by eauto
      | solve_sub_redexes_are_values] ].

  Global Instance irred_unless_match v x1 e1 x2 e2 P σ :
    SafeImplies (∃ v', v = InjLV v' ∨ v = InjRV v') P (Match (Val v) x1 e1 x2 e2) σ.
  Proof. prove_safe_implies. Qed.

  (** for operators, we provide specialized instances for each operator. *)
  Ltac solve_binop v1 v2 :=
    unfold bin_op_eval in *;
    case_decide; try congruence;
    destruct v1 as [[] | | |]; destruct v2 as [[] | | |]; cbn in *;
        try congruence;
        repeat match goal with
        | H: _ ∨ _ |- _ => destruct H
        | H : _ ∧ _ |- _ => destruct H
        end; eauto 8.
  Ltac solve_unop v :=
    unfold un_op_eval in *;
    try congruence;
    destruct v as [[] | | |]; cbn in *;
        try congruence;
        repeat match goal with
        | H: _ ∨ _ |- _ => destruct H
        | H : _ ∧ _ |- _ => destruct H
        end; eauto 8.

  Global Instance safe_implies_plus v1 v2 P σ :
    SafeImplies ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp PlusOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies; solve_binop v1 v2. Qed.
  Global Instance safe_implies_minus v1 v2 P σ :
    SafeImplies ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp MinusOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies; solve_binop v1 v2. Qed.
  Global Instance safe_implies_rem v1 v2 P σ :
    SafeImplies ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n ∧ n ≠ 0%Z))%V
      P (BinOp RemOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. naive_solver. Qed.
  Global Instance safe_implies_mult v1 v2 P σ :
    SafeImplies ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V P (BinOp MultOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. Qed.
  Global Instance safe_implies_quot v1 v2 P σ :
    SafeImplies ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n ∧ n ≠ 0%Z))%V
      P (BinOp QuotOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. naive_solver. Qed.

  Global Instance safe_implies_and v1 v2 P σ :
    SafeImplies (((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n)) ∨ ((∃ b, v1 = LitV $ LitBool b) ∧ ∃ b, v2 = LitV $ LitBool b))%V
      P (BinOp AndOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. Qed.
  Global Instance safe_implies_or v1 v2 P σ :
    SafeImplies (((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n)) ∨ ((∃ b, v1 = LitV $ LitBool b) ∧ ∃ b, v2 = LitV $ LitBool b))%V
      P (BinOp OrOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. Qed.
  Global Instance safe_implies_xor v1 v2 P σ :
    SafeImplies (((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n)) ∨ ((∃ b, v1 = LitV $ LitBool b) ∧ ∃ b, v2 = LitV $ LitBool b))%V
      P (BinOp XorOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. Qed.

  Global Instance safe_implies_shiftl v1 v2 P σ :
    SafeImplies ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp ShiftLOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. Qed.
  Global Instance safe_implies_shiftr v1 v2 P σ :
    SafeImplies ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp ShiftROp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. Qed.

  Global Instance safe_implies_le v1 v2 P σ :
    SafeImplies ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp LeOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. Qed.
  Global Instance safe_implies_ge v1 v2 P σ :
    SafeImplies ((∃ n, v1 = LitV $ LitInt n) ∧ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp LtOp (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. Qed.

  Global Instance safe_implies_offset v1 v2 P σ :
    SafeImplies ((∃ l, v1 = LitV $ LitLoc l) ∧ (∃ n, v2 = LitV $ LitInt n))%V
      P (BinOp OffsetOp  (Val v1) (Val v2)) σ.
  Proof. prove_safe_implies. solve_binop v1 v2. Qed.

  Global Instance safe_implies_eq v1 v2 P σ :
    SafeImplies (vals_compare_safe v1 v2)%V
      P (BinOp EqOp (Val v1) (Val v2)) σ.
  Proof.
    prove_safe_implies.
    unfold bin_op_eval in *;
    case_decide; last congruence.
    case_decide; congruence.
  Qed.

  Global Instance safe_implies_neg v P σ :
    SafeImplies ((∃ n, v = LitV $ LitInt n) ∨ (∃ b, v = LitV $ LitBool b)) P (UnOp NegOp (Val v)) σ.
  Proof. prove_safe_implies. solve_unop v. Qed.
  Global Instance safe_implies_un_minus v P σ :
    SafeImplies (∃ n, v = LitV $ LitInt n) P (UnOp MinusUnOp (Val v)) σ.
  Proof. prove_safe_implies. solve_unop v. Qed.

  Global Instance safe_implies_var (x : string) P σ :
    SafeImplies False P (Var x) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_global_var (x : string) P σ :
    SafeImplies (x ∈ σ.(globals)) P (GlobalVar x) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_call v v2 P σ :
    SafeImplies (∃ fn, v = LitV $ LitFn fn) P (Call (Val v) (Val v2)) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_if v e1 e2 P σ :
    SafeImplies (∃ b, v = LitV $ LitBool b) P (If (Val v) e1 e2) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_fst v P σ :
    SafeImplies (∃ v1 v2, v = PairV v1 v2) P (Fst (Val v)) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_snd v P σ :
    SafeImplies (∃ v1 v2, v = PairV v1 v2) P (Snd (Val v)) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_loadSc σ v_l P :
    SafeImplies (∃ l v n, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt n, v)) P (Load ScOrd $ Val v_l) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_loadNa1 σ v_l P :
    SafeImplies (∃ l v n, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt n, v)) P (Load Na1Ord $ Val v_l) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_loadNa2 σ v_l P :
    SafeImplies (∃ l v n, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt (S n), v)) P (Load Na2Ord $ Val v_l) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_storeSc σ v_l P (v : val) :
    SafeImplies (∃ l v, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt 0, v)) P (Store ScOrd (Val $ v_l) (Val v)) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_storeNa1 σ v_l P (v : val) :
    SafeImplies (∃ l v, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt 0, v)) P (Store Na1Ord (Val $ v_l) (Val v)) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_storeNa2 σ v_l P (v : val) :
    SafeImplies (∃ l v, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (WSt, v)) P (Store Na2Ord (Val $ v_l) (Val v)) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_freeN σ v_l v_n P :
    SafeImplies (∃ l n, v_l = LitV $ LitLoc l ∧ v_n = LitV $ LitInt n ∧ (0 < n)%Z ∧ block_is_dyn l.(loc_block) ∧
                       (∀ m : Z, is_Some (heap σ !! (l +ₗ m)) ↔ (0 ≤ m < n)%Z))
      P (FreeN (Val v_n) (Val v_l)) σ.
  Proof. prove_safe_implies. eauto 8. Qed.

  Global Instance safe_implies_allocN σ v_n v P :
    SafeImplies (∃ n, v_n = LitV $ LitInt n ∧ (0 < n)%Z) P (AllocN (Val v_n) (Val v)) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_storeScNa1 o σ v_l P (v : val) `{!TCFastDone (o ≠ Na2Ord)} :
    SafeImplies (∃ l v, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt 0, v)) P (Store o (Val $ v_l) (Val v)) σ.
  Proof. unfold TCFastDone in *. destruct o; try done; apply _. Qed.
  Global Instance safe_implies_loadScNa1 o σ v_l P `{!TCFastDone (o ≠ Na2Ord)}:
    SafeImplies (∃ l v n, v_l = LitV $ LitLoc l ∧ heap σ !! l = Some (RSt n, v)) P (Load o $ Val v_l) σ.
  Proof. unfold TCFastDone in *. destruct o; try done; apply _. Qed.

  (** for the usual use case with [sim_irred_unless], we will not actually have the state and program
    in context, thus the application of the above instances will fail.
    Therefore, we provide weaker instances for these cases.
   *)
  Global Instance safe_implies_load_weak σ v_l o P :
    SafeImplies (∃ l, v_l = LitV $ LitLoc l) P (Load o $ Val v_l) σ | 10.
  Proof. destruct o; (eapply safe_implies_weaken; last by apply _);
      intros (l & v & ? & ? &?); eauto.
  Qed.
  Global Instance safe_implies_store_weak σ v_l o P (v : val) :
    SafeImplies (∃ l, v_l = LitV $ LitLoc l) P (Store o (Val $ v_l) (Val v)) σ | 10.
  Proof.
    destruct o; (eapply safe_implies_weaken; last (by apply _));
      intros (l & ? & ? & ?); eauto.
  Qed.
  Global Instance safe_implies_freeN_weak σ v_l v_n P :
    SafeImplies (∃ l n, v_l = LitV $ LitLoc l ∧ v_n = LitV $ LitInt n ∧ (0 < n)%Z ∧ block_is_dyn l.(loc_block)) P (FreeN (Val v_n) (Val v_l)) σ | 10.
  Proof.
    eapply safe_implies_weaken; last apply safe_implies_freeN.
    intros (l & ? & ? & ? &? &? &?); eauto 8.
  Qed.
End safe_implies.


(** * Instances of the [PureExec] class *)
Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_base_step.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_base_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_pairc (v1 v2 : val) :
    PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injlc (v : val) :
    PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injrc (v : val) :
    PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_iota x (e2 : expr) (v1 : val) :
    PureExec True 1 (Let x (Val v1) e2) (subst' x v1 e2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
  Proof. solve_pure_exec. Qed.
  (* Higher-priority instance for [EqOp]. *)
  Global Instance pure_eqop v1 v2 :
    PureExec (vals_compare_safe v1 v2) 1
      (BinOp EqOp (Val v1) (Val v2))
      (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
  Proof.
    intros Hcompare.
    cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
    { intros. revert Hcompare. solve_pure_exec. }
    rewrite /bin_op_eval /= decide_True //.
  Qed.

  Global Instance pure_if_true e1 e2 :
    PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.
  Global Instance pure_if_false e1 e2 :
    PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.
  Lemma pure_while e0 e1 :
    PureExec True 1 (While e0 e1) (If e0 (e1 ;; While e0 e1) (Val $ LitV $ LitUnit)).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst v1 v2 :
    PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_snd v1 v2 :
    PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_match_inl v x1 e1 x2 e2 :
    PureExec True 1 (Match (Val $ InjLV v) x1 e1 x2 e2) (subst' x1 v e1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_match_inr v x1 e1 x2 e2 :
    PureExec True 1 (Match (Val $ InjRV v) x1 e1 x2 e2) (subst' x2 v e2).
  Proof. solve_pure_exec. Qed.
End pure_exec.
