From simuliris.simulation Require Import language slsls lifting.
From simuliris.stacked_borrows Require Export lang.
From simuliris.stacked_borrows Require Import tactics.

Local Open Scope Z_scope.

(** * Instances of the [PureExec] class *)
Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; do 2 econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; inv_base_step; try done.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_base_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].


  (*pure_expr_step*)
  Global Instance pure_iota_val x (e2 : expr) (v1 : value) :
    PureExec True 1 (Let x (Val v1) e2) (subst' x (Val v1) e2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_iota_place x (e2 : expr) l t T :
    PureExec True 1 (Let x (Place l t T) e2) (subst' x (PlaceR l t T) e2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_iota_result x (e2 : expr) (r : result) :
    PureExec True 1 (Let x (of_result r) e2) (subst' x (of_result r) e2).
  Proof. solve_pure_exec. rewrite to_of_result. eauto. Qed.

  (* We do not have a general instance for BinOp as evaluation of EqOp for locations is not pure *)
  Global Instance pure_add z1 z2  :
    PureExec True 1 (BinOp AddOp (#[ScInt z1]) (#[ScInt z2])) (#[ScInt (z1 + z2)]).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_sub z1 z2  :
    PureExec True 1 (BinOp SubOp (#[ScInt z1]) (#[ScInt z2])) (#[ScInt (z1 - z2)]).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_le z1 z2 :
    PureExec True 1 (BinOp LeOp (#[ScInt z1]) (#[ScInt z2])) (#[bool_decide (z1 ≤ z2)]).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_lt z1 z2 :
    PureExec True 1 (BinOp LtOp (#[ScInt z1]) (#[ScInt z2])) (#[bool_decide (z1 < z2)]).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_offset l t z :
    PureExec True 1 (BinOp OffsetOp (#[ScPtr l t]) (#[ScInt z])) (#[ScPtr (l +ₗ z) t]).
  Proof. solve_pure_exec. Qed.

  (* TODO: figure out something useful for EqOp *)
  (*Global Instance pure_eq_refl sc1 sc2 :*)
    (*PureExec 1 (BinOp EqOp (#[sc1]) (#[sc2])) (#[false]).*)

  Global Instance pure_proj (v : value) i s :
    PureExec (0 ≤ i ∧ v !! (Z.to_nat i) = Some s) 1 (Proj (Val v) (#[ScInt i])) (#[s]).
  Proof.
    solve_pure_exec. destruct_and!.
    match goal with H1: ?t = Some _, H2: ?t = Some _ |- _ => rewrite H1 in H2 end.
    naive_solver.
  Qed.
  Global Instance pure_conc v1 v2 :
    PureExec True 1 (Conc #v1 #v2) (#(v1 ++ v2)).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_ref l t T :
    PureExec True 1 (Ref (Place l t T)) (#[ScPtr l t]).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_deref l t T :
    PureExec True 1 (Deref (#[ScPtr l t]) T) (Place l t T).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_case i el e :
    PureExec (0 ≤ i ∧ el !! Z.to_nat i = Some e) 1 (Case #[i] el) e.
  Proof. solve_pure_exec; naive_solver. Qed.

  (* not an instance as we usually don't want it to reduce in order to apply coinduction lemmas *)
  Lemma pure_while e1 e2 :
    PureExec True 1 (while: e1 do e2 od) (if: e1 then e2;; while: e1 do e2 od else #[☠]).
  Proof. solve_pure_exec. Qed.

End pure_exec.

(** SafeReach *)

Section safe_reach.
  Implicit Types (e : expr) (v : value) (r : result) (σ : state).

  Lemma language_to_val_eq e :
    language.to_val e = to_result e.
  Proof.
    rewrite /language.to_val /language.to_class; cbn.
    destruct (to_result e) eqn:Heq.
    - by rewrite (to_result_class _ _ Heq).
    - destruct to_class as [ [] | ] eqn:Heq';
        [ by rewrite (to_class_result _ _ Heq') in Heq | done | done].
  Qed.

  Lemma of_result_value r v : of_result r = Val v → r = ValR v.
  Proof. destruct r; simpl; [by inversion 1|done]. Qed.
  Lemma of_result_place r l tg T : of_result r = Place l tg T → r = PlaceR l tg T.
  Proof. destruct r; simpl; [done|by inversion 1]. Qed.
  Lemma to_val_of_result r : to_val (of_result r) = Some r.
  Proof. by rewrite /to_val /= /to_class to_of_result. Qed.

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
    [destruct Ki; inversion Heq; subst; cbn in *;
      try rewrite to_val_of_result in Hv; congruence
    | eapply IH; first (by rewrite Heq);
      rewrite language_to_val_eq; apply fill_item_no_result;
        by rewrite -language_to_val_eq].

  (* Slightly hacky proof tactic for proving [SafeImplies] goals.
    Basically the same proof script works for all these proofs, but there don't seem to be nice more general lemmas. *)
  Ltac prove_safe_implies :=
    let Hsafe := fresh in
    let Hval := fresh in
    let Hred := fresh in
    let Hhead := fresh in
    intros Hsafe; specialize (Hsafe _ _ _ (Pool_steps_refl _ _ _) _ 0%nat ltac:(done)) as [Hval | Hred];
    [ rewrite language_to_val_eq in Hval; simpl in Hval; destruct Hval as [? [=]] |
      destruct Hred as (? & ? & ? & Hhead%prim_base_step);
      [ (* this need not complete the proof and may generate a proof obligation *)
        inv_base_step; subst; try by eauto 10 using of_result_value, of_result_place
      | solve [solve_sub_redexes_are_values]] ].


  Global Instance safe_implies_match_val r el P σ  :
    SafeImplies (∃ i e, r = ValR [ScInt i] ∧ 0 ≤ i ∧ el !! Z.to_nat i = Some e) P (Case r el) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_match_place l t T el P σ  :
    SafeImplies False P (Case (Place l t T) el) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_add r1 r2 P σ :
    SafeImplies (∃ z1 z2, r1 = ValR [ScInt z1] ∧ r2 = ValR [ScInt z2]) P (BinOp AddOp r1 r2) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_sub r1 r2 P σ :
    SafeImplies (∃ z1 z2, r1 = ValR [ScInt z1] ∧ r2 = ValR [ScInt z2]) P (BinOp SubOp r1 r2) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_lt r1 r2 P σ :
    SafeImplies (∃ z1 z2, r1 = ValR [ScInt z1] ∧ r2 = ValR [ScInt z2]) P (BinOp LtOp r1 r2) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_le r1 r2 P σ :
    SafeImplies (∃ z1 z2, r1 = ValR [ScInt z1] ∧ r2 = ValR [ScInt z2]) P (BinOp LeOp r1 r2) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_offset r1 r2 P σ :
    SafeImplies (∃ l t z, r1 = ValR [ScPtr l t] ∧ r2 = ValR [ScInt z]) P (BinOp OffsetOp r1 r2) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_eq r1 r2 P σ :
    SafeImplies (∃ sc1 sc2, r1 = ValR [sc1] ∧ r2 = ValR [sc2] ∧ (scalar_eq σ.(shp) sc1 sc2 ∨ scalar_neq sc1 sc2)) P (BinOp EqOp r1 r2) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance irred_proj r r2 P σ :
    SafeImplies (∃ v i s, r = ValR v ∧ r2 = ValR [ScInt i] ∧ 0 ≤ i ∧ v !! Z.to_nat i = Some s) P (Proj r r2) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance irred_proj_val v v2 P σ :
    SafeImplies (∃ i s, v2 = [ScInt i] ∧ 0 ≤ i ∧ v !! Z.to_nat i = Some s) P (Proj (Val v) (Val v2)) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance irred_proj_place l t T v2 P σ :
    SafeImplies False P (Proj (Place l t T) (Val v2)) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance irred_conc r1 r2 P σ :
    SafeImplies (∃ v1 v2, r1 = ValR v1 ∧ r2 = ValR v2) P (Conc r1 r2) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance irred_ref_val r P σ :
    SafeImplies (∃ l tg T, r = PlaceR l tg T) P (Ref r) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance irred_deref_place l t T T' P σ :
    SafeImplies False P (Deref (Place l t T) T') σ.
  Proof. prove_safe_implies. Qed.
  Global Instance irred_deref r T P σ :
    SafeImplies (∃ l t, r = ValR [ScPtr l t]) P (Deref r T) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_call r r2 P σ :
    SafeImplies (∃ fn, r = ValR [ScFnPtr fn]) P (Call r r2) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_call_val v v2 P σ :
    SafeImplies (∃ fn, v = [ScFnPtr fn]) P (Call (Val v) (Val v2)) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_call_place r l t T P σ :
    SafeImplies (∃ fn, r = ValR [ScFnPtr fn]) P (Call r (Place l t T)) σ.
  Proof. prove_safe_implies. Qed.


  Global Instance safe_implies_endcall P σ v :
    SafeImplies (∃ c, v = [ScCallId c] ∧ c ∈ σ.(scs)) P (EndCall (Val v)) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_endcall_result_weak P σ r :
    SafeImplies (∃ c, r = ValR [ScCallId c]) P (EndCall r) σ.
  Proof.
    prove_safe_implies.
    rename select (to_value _ = _) into Eqr. apply Val_to_value in Eqr.
    eauto using of_result_value.
  Qed.

  Global Instance safe_implies_retag P σ v v' pk T rk :
    SafeImplies (∃ c ot l, v = [ScPtr l ot] ∧ v' = [ScCallId c] ∧ c ∈ σ.(scs) ∧
      is_Some (retag σ.(sst) σ.(snp) σ.(scs) c l ot rk pk T)) P (Retag v v' pk T rk) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_retag_result P σ r r' pk T rk :
    SafeImplies (∃ c ot l, r = ValR [ScPtr l ot] ∧ r' = ValR [ScCallId c] ∧ c ∈ σ.(scs) ∧
      is_Some (retag σ.(sst) σ.(snp) σ.(scs) c l ot rk pk T)) P (Retag r r' pk T rk) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_retag_place_l P σ l t T T' v pk rk :
    SafeImplies False P (Retag (Place l t T) (Val v) pk T' rk) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_retag_place_r P σ l t T T' v pk rk :
    SafeImplies False P (Retag (Val v) (Place l t T) pk T' rk) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_retag_place_r2 P σ l t T T' l' t' T'' pk rk :
    SafeImplies False P (Retag (Place l' t' T'') (Place l t T) pk T' rk) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_copy_val P σ r :
    SafeImplies (∃ l t T, r = PlaceR l t T) P (Copy r) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_copy_place P σ l t T :
    SafeImplies ((∃ v, read_mem l (tsize T) σ.(shp) = Some v ∧ is_Some (memory_read σ.(sst) σ.(scs) l t (tsize T))) ∨ memory_read σ.(sst) σ.(scs) l t (tsize T) = None) P (Copy (Place l t T)) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_write_val_left1 P σ v v' :
    SafeImplies False P (Write (Val v) (Val v')) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_write_val_left2 P σ v l t T :
    SafeImplies False P (Write (Val v) (Place l t T)) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_write_place_right P σ l' t' T' l t T :
    SafeImplies False P (Write (Place l' t' T') (Place l t T)) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_write P σ l t T v :
    SafeImplies ((∀ (i: nat), (i < length v)%nat → l +ₗ i ∈ dom σ.(shp)) ∧ is_Some (memory_written σ.(sst) σ.(scs) l t (tsize T)) ∧ length v = tsize T) P (Write (Place l t T) (Val v)) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_write_result P σ r r' :
    SafeImplies (∃ l tg T v, r = PlaceR l tg T ∧ r' = ValR v) P (Write r r') σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_free_val P σ r :
    SafeImplies (∃ l tg T, r = PlaceR l tg T) P (Free r) σ.
  Proof. prove_safe_implies. Qed.
  Global Instance safe_implies_free P σ l t T :
    SafeImplies ((∀ m, is_Some (σ.(shp) !! (l +ₗ m)) ↔ 0 ≤ m < tsize T) ∧ is_Some (memory_deallocated σ.(sst) σ.(scs) l t (tsize T))) P (Free (Place l t T)) σ.
  Proof. prove_safe_implies. Qed.

  Global Instance safe_implies_write_weak P σ l t T v :
    SafeImplies (length v = tsize T) P (Write (Place l t T) (Val v)) σ | 10.
  Proof.
    eapply safe_implies_weaken; last apply safe_implies_write. tauto.
  Qed.
  Global Instance safe_implies_retag_weak P σ v v' pk T rk :
    SafeImplies (∃ c ot l, v = [ScPtr l ot] ∧ v' = [ScCallId c]) P (Retag v v' pk T rk) σ | 10.
  Proof.
    eapply safe_implies_weaken; last apply safe_implies_retag.
    intros (c & ot & l & -> & -> & _). eauto.
  Qed.
  Global Instance safe_implies_retag_weak_result P σ r r' pk T rk :
    SafeImplies (∃ c ot l, r = ValR [ScPtr l ot] ∧ r' = ValR [ScCallId c]) P (Retag r r' pk T rk) σ | 10.
  Proof.
    eapply safe_implies_weaken; last apply safe_implies_retag_result.
    intros (c & ot & l & -> & -> & _). eauto.
  Qed.
End safe_reach.
