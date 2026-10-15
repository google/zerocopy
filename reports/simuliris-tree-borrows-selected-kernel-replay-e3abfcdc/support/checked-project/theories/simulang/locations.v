From iris.prelude Require Export prelude.
From stdpp Require Import countable numbers gmap strings.
From simuliris.simulang Require Export base.
(* partly adapted from lambda rust *)

Definition dyn_block := positive.
Inductive block :=
  | DynBlock (b : dyn_block)
  | GlobalBlock (name : string).
Record loc := Loc { loc_block : block; loc_idx : Z }.
Add Printing Constructor loc.

Global Instance block_eq_decision : EqDecision block.
Proof. solve_decision. Qed.
Global Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Qed.

Global Instance block_inhabited : Inhabited block := populate (DynBlock 1%positive).
Global Instance loc_inhabited : Inhabited loc := populate {|loc_block := inhabitant; loc_idx := 0 |}.

Global Instance block_countable : Countable block.
Proof.
  by apply (inj_countable'
           (λ b, match b with | DynBlock b => inl b | GlobalBlock n => inr n end)
           (λ b, match b with | inl b => DynBlock b | inr n => GlobalBlock n end)
           ); intros [].
Qed.
Global Instance loc_countable : Countable loc.
Proof. by apply (inj_countable' (λ l, (loc_block l, loc_idx l)) (λ '(i, j), {| loc_block := i; loc_idx := j |})); intros []. Qed.

Global Program Instance block_infinite : Infinite block :=
  inj_infinite DynBlock (λ b, if b is DynBlock b then Some b else None) _.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Global Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ '(i, j), {| loc_block := i; loc_idx := j |}) (λ l, Some ((loc_block l, loc_idx l))) _.
Next Obligation. intros []. done. Qed.

Definition block_is_dyn (b : block) : bool := if b is DynBlock _ then true else false.
Definition block_is_global (b : block) : bool := if b is GlobalBlock _ then true else false.

Definition dyn_loc (b : dyn_block) : loc := Loc (DynBlock b) 0.
Definition global_loc (n : string) : loc := Loc (GlobalBlock n) 0.

Global Instance dyn_loc_inj : Inj (=) (=) dyn_loc.
Proof. by move => ?? []. Qed.
Global Instance global_loc_inj : Inj (=) (=) global_loc.
Proof. by move => ?? []. Qed.

Definition loc_add (l : loc) (off : Z) : loc :=
  Loc (loc_block l) (loc_idx l + off).

Notation "l +ₗ off" :=
  (loc_add l off) (at level 50, left associativity) : stdpp_scope.

Lemma loc_add_assoc l i j : l +ₗ i +ₗ j = l +ₗ (i + j).
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

Lemma loc_add_0 l : l +ₗ 0 = l.
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.
Lemma loc_add_block l n : loc_block (l +ₗ n) = loc_block l.
Proof. done. Qed.

Global Instance loc_add_inj l : Inj eq eq (loc_add l).
Proof. destruct l; rewrite /Inj /loc_add /=; intros; simplify_eq; lia. Qed.

Lemma loc_eta l : (Loc (loc_block l) (loc_idx l)) = l.
Proof.  by destruct l. Qed.
Lemma Loc_add b i : Loc b 0 +ₗ i = Loc b i.
Proof. done. Qed.
