From stdpp Require Export gmap.
From iris.prelude Require Import prelude.
From simuliris.stacked_borrows Require Import expr_semantics.


(** Definitions and proofs mostly yoinked from https://gitlab.mpi-sws.org/FP/stacked-borrows/-/blob/master/theories/lang/subst_map.v *)

(** Induction scheme for expressions *)
Lemma expr_ind (P : expr → Prop):
  (∀ v, P (Val v)) →
  (∀ x, P (Var x)) →
  (∀ e1 e2, P e1 → P e2 → P (Call e1 e2)) →
  (P (InitCall)) →
  (∀ e, P e → P (EndCall e)) →
  (∀ l tg ty, P (Place l tg ty)) →
  (∀ o e1 e2, P e1 → P e2 → P (BinOp o e1 e2)) →
  (∀ e1 e2, P e1 → P e2 → P (Proj e1 e2)) →
  (∀ e1 e2, P e1 → P e2 → P (Conc e1 e2)) →
  (∀ e ty, P e → P (Deref e ty)) →
  (∀ e, P e → P (Ref e)) →
  (∀ e, P e → P (Copy e)) →
  (∀ e1 e2, P e1 → P e2 → P (Write e1 e2)) →
  (∀ ty, P (Alloc ty)) →
  (∀ e, P e → P (Free e)) →
  (∀ e1 e2 pk T rk, P e1 → P e2 → P (Retag e1 e2 pk T rk)) →
  (∀ b e1 e2, P e1 → P e2 → P (Let b e1 e2)) →
  (∀ e el, P e → Forall P el → P (Case e el)) →
  (∀ e1 e2, P e1 → P e2 → P (While e1 e2)) →
  (∀ e, P e → P (Fork e)) →
  ∀ e, P e.
Proof.
  intros Hvl Hvr HC HIC HE HP HBi HPr HCo HD HR HCopy HW HA HF HRT HL HCA HWHL HFo.
  fix REC 1. intros []; try
  (* Find head symbol, then find lemma for that symbol.
     We have to be this smart because we can't use the unguarded [REC]! *)
  match goal with
  | |- P (?head _ _ _ _ _) =>
    match goal with H : context[head] |- _ => apply H; try done end
  | |- P (?head _ _ _ _) =>
    match goal with H : context[head] |- _ => apply H; try done end
  | |- P (?head _ _ _) =>
    match goal with H : context[head] |- _ => apply H; try done end
  | |- P (?head _ _) =>
    match goal with H : context[head] |- _ => apply H; try done end
  | |- P (?head _) =>
    match goal with H : context[head] |- _ => apply H; try done end
  | |- P (?head) =>
    match goal with H : context[head] |- _ => apply H; try done end
  end.
  (* remaining case: The [Forall]. *)
  match goal with |- Forall _ ?el => induction el; eauto using Forall end.
Qed.

(** * Parallel substitution*)

Fixpoint subst_map (xs : gmap string result) (e : expr) : expr :=
  match e with
  | Var y => if xs !! y is Some v then of_result v else Var y
  | Val v => Val v
  | Let x1 e1 e2 => Let x1 (subst_map xs e1) (subst_map (binder_delete x1 xs) e2)
  | Call e1 e2 => Call (subst_map xs e1) (subst_map xs e2)
  | InitCall => InitCall
  | EndCall e => EndCall (subst_map xs e)
  | Place l tag T => Place l tag T
  | BinOp op e1 e2 => BinOp op (subst_map xs e1) (subst_map xs e2)
  | Proj e1 e2 => Proj (subst_map xs e1) (subst_map xs e2)
  | Conc e1 e2 => Conc (subst_map xs e1) (subst_map xs e2)
  | Copy e => Copy (subst_map xs e)
  | Write e1 e2 => Write (subst_map xs e1) (subst_map xs e2)
  | Alloc T => Alloc T
  | Free e => Free (subst_map xs e)
  | Deref e T => Deref (subst_map xs e) T
  | Ref e => Ref (subst_map xs e)
  | Retag e1 e2 pk T kind => Retag (subst_map xs e1) (subst_map xs e2) pk T kind
  | Case e el => Case (subst_map xs e) (fmap (subst_map xs) el)
  | While e0 e1 => While (subst_map xs e0) (subst_map xs e1)
  | Fork e => Fork (subst_map xs e)
  end.

Lemma subst_map_empty e :
  subst_map ∅ e = e.
Proof.
  induction e using expr_ind; simpl; f_equal; eauto.
  - match goal with |- context[binder_delete ?x ∅] => destruct x; first done end.
    simpl; rewrite delete_empty; done.
  - match goal with H : Forall _ _ |- _ =>
      induction H; first done; simpl; by f_equal
    end.
Qed.

Lemma subst_map_subst map x (r : result) (e : expr) :
  subst_map map (subst x r e) = subst_map (<[x:=r]>map) e.
Proof.
  revert x r map; induction e using expr_ind; intros xx r map; simpl;
  try (f_equal; eauto).
  - case_bool_decide.
    + simplify_eq/=. rewrite lookup_insert_eq. destruct r; done.
    + rewrite lookup_insert_ne //.
  - match goal with |- context[binder_delete ?x _] => destruct x; simpl; first done end.
    case_bool_decide as NEq.
    + rewrite delete_insert_ne //. intros ?. apply NEq. f_equal. done.
    + simplify_eq/=. rewrite delete_insert_eq //.
  - match goal with H : Forall _ _ |- _ =>
      induction H; first done; simpl; by f_equal
    end.
Qed.

Lemma subst_subst_map x (r : result) map e :
  subst x r (subst_map (delete x map) e) =
  subst_map (<[x:=r]>map) e.
Proof.
  revert map r x; induction e using expr_ind; intros map v0 xx; simpl;
  try (f_equal; eauto).
  - match goal with |- context[delete _ _ !! ?x] =>
      destruct (decide (xx=x)) as [->|Hne]
    end.
    + rewrite lookup_delete_eq // lookup_insert_eq //. simpl.
      rewrite bool_decide_true //.
    + rewrite lookup_delete_ne // lookup_insert_ne //.
      destruct (map !! _) as [rr|].
      * by destruct rr.
      * simpl. rewrite bool_decide_false //.
  - match goal with |- context[binder_delete ?x _] => destruct x; simpl; first by auto end.
    case_bool_decide.
    + rewrite delete_insert_ne //; last congruence. rewrite delete_delete. eauto.
    + simplify_eq. rewrite delete_delete_eq delete_insert_eq. done.
  - match goal with H : Forall _ _ |- _ =>
      induction H; first done; simpl; by f_equal
    end.
Qed.

Lemma subst_map_singleton x (r : result) e :
  subst_map {[x:=r]} e = subst x r e.
Proof. rewrite -subst_map_subst subst_map_empty //. Qed.

Lemma subst'_subst_map b (r : result) map e :
  subst' b r (subst_map (binder_delete b map) e) =
  subst_map (binder_insert b r map) e.
Proof.
  destruct b; first done.
  exact: subst_subst_map.
Qed.

Lemma subst_map_subst_map xs ys e :
  subst_map xs (subst_map ys e) = subst_map (ys ∪ xs) e.
Proof.
  revert e.
  induction ys as [|x v ys HNone IH] using map_ind => e.
  { by rewrite left_id subst_map_empty. }
  by rewrite -insert_union_l -[in X in _ = X]subst_map_subst -IH subst_map_subst.
Qed.

Lemma subst_map_of_result map (r : result) :
  subst_map map (of_result r) = of_result r.
Proof. by destruct r. Qed.

(** "Free variables" and their interaction with subst_map *)
Local Definition binder_to_ctx (x : binder) : gset string :=
  if x is BNamed s then {[s]} else ∅.

Fixpoint free_vars (e : expr) : gset string :=
  match e with
  | Val v => ∅
  | Var x => {[x]}
  | Let x e1 e2 => free_vars e1 ∪ (free_vars e2 ∖ binder_to_ctx x)
  | InitCall | Place _ _ _ | Alloc _ => ∅
  | Fork e | Copy e | Free e | Deref e _ | Ref e | EndCall e =>
     free_vars e
  | Call e1 e2 | While e1 e2 | BinOp _ e1 e2 | Proj e1 e2 | Conc e1 e2
    | Write e1 e2 | Retag e1 e2 _ _ _ =>
     free_vars e1 ∪ free_vars e2
  | Case e el =>
    (free_vars e) ∪ foldr (λ ei s, s ∪ free_vars ei) ∅ el
  end.

Local Lemma binder_delete_eq x y (xs1 xs2 : gmap string result) :
  (if y is BNamed s then s ≠ x → xs1 !! x = xs2 !! x else xs1 !! x = xs2 !! x) →
  binder_delete y xs1 !! x = binder_delete y xs2 !! x.
Proof.
  destruct y as [|s]; first done. simpl.
  destruct (decide (s = x)) as [->|Hne].
  - rewrite !lookup_delete_eq //.
  - rewrite !lookup_delete_ne //. eauto.
Qed.

Lemma free_vars_case_1 e el :
  free_vars e ⊆ free_vars (Case e el).
Proof. rewrite /=. set_solver. Qed.

Lemma free_vars_case_2 e el e' :
  e' ∈ el → free_vars e' ⊆ free_vars (Case e el).
Proof.
  revert e'. induction el as [|e1 el IH] => e'.
  - by intros ?%not_elem_of_nil.
  - intros [<-|Inel]%elem_of_cons.
    + rewrite {2}/free_vars -/free_vars. set_solver.
    + etrans; first by apply (IH _ Inel).
      rewrite {2}/free_vars -/free_vars. set_solver.
Qed.

Lemma free_vars_result (r : result) :
  free_vars r = ∅.
Proof. by destruct r. Qed.

Lemma subst_map_free_vars (xs1 xs2 : gmap string result) (e : expr) :
  (∀ x, x ∈ free_vars e → xs1 !! x = xs2 !! x) →
  subst_map xs1 e = subst_map xs2 e.
Proof.
  revert xs1 xs2; induction e using expr_ind=>/= xs1 xs2 Heq;
  try solve [
    (* trivial cases *)
    done
  | (* variable case *)
    rewrite Heq; [done|set_solver]
  | (* recursive cases *)
    f_equal;
    repeat lazymatch goal with x : binder |- _ => destruct x end;
    intuition eauto using binder_delete_eq with set_solver
  ].
  f_equal.
  - match goal with IH : ∀ _ _ _, subst_map _ _ = _ |- _ =>
      apply IH => x Ine
    end.
    apply Heq. set_solver+Ine.
  - match goal with FA : Forall _ _ |- _ =>
      induction FA as [|? ? H' FA' IH]; first done; simpl; f_equal
    end.
    + apply H' => x' Ine'. apply Heq. set_solver+Ine'.
    + apply IH => x' Ine'. apply Heq. set_solver+Ine'.
Qed.

Lemma subst_map_closed xs e :
  free_vars e = ∅ →
  subst_map xs e = e.
Proof.
  intros Hclosed.
  trans (subst_map ∅ e).
  - apply subst_map_free_vars. rewrite Hclosed. done.
  - apply subst_map_empty.
Qed.

Lemma subst_free_vars x (v : result) e :
  x ∉ free_vars e →
  subst x v e = e.
Proof.
  intros Hfree.
  rewrite -(subst_map_empty (subst x v e)).
  rewrite subst_map_subst.
  rewrite (subst_map_free_vars _ ∅); first by apply subst_map_empty.
  intros y ?. rewrite lookup_insert_ne //. set_solver.
Qed.

Lemma free_vars_subst x (r : result) e :
  free_vars (subst x r e) = free_vars e ∖ {[x]}.
Proof.
  induction e using expr_ind=>/=; repeat case_decide; try set_solver.
  { subst. rewrite bool_decide_true //. destruct r; set_solver. }
  match goal with IH : free_vars _ = _ |- _ => rewrite IH difference_union_distr_l_L end.
  f_equal.
  match goal with FA : Forall _ _ |- _ => induction FA end.
  { set_solver-. }
  rewrite fmap_cons /= difference_union_distr_l_L. by f_equal.
Qed.

Lemma free_vars_subst_map xs e :
  free_vars (subst_map xs e) = free_vars e ∖ (dom xs).
Proof.
  induction xs as [| x v xs HNone IH] using map_ind.
  - rewrite subst_map_empty. set_solver.
  - rewrite -subst_subst_map delete_id // free_vars_subst IH. set_solver.
Qed.
