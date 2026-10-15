(** Internal representation of memory.
    We opt for a view in which a location is composed of
    an allocation id and an offset into that allocation. *)

From iris.prelude Require Import prelude.
From stdpp Require Import countable numbers gmap.
Local Open Scope Z_scope.

Declare Scope loc_scope.
Delimit Scope loc_scope with L.

(** Locations *)
Definition block : Set := positive.
Notation loc' := Z (only parsing).
Definition loc : Set := block * loc'.

Definition range' : Set := loc' * nat.
Definition range : Set := block * range'.

Bind Scope loc_scope with loc.
Global Open Scope loc_scope.

Global Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Qed.
Global Instance loc_inhabited : Inhabited loc := populate (1%positive, 0).
Global Instance loc_countable : Countable loc.
Proof. by apply (inj_countable' (λ l, l) (λ '(i, j), (i, j))); intros []. Qed.
Global Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ '(i, j), (i, j)) (λ l, Some l) _.
Next Obligation. intros []. done. Qed.

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).

Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.

(** Shifting for locations *)
Lemma shift_loc_assoc l n n' : l +ₗ n +ₗ n' = l +ₗ (n + n').
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0 l : l +ₗ 0 = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Lemma shift_loc_assoc_nat l (n n' : nat) : l +ₗ n +ₗ n' = l +ₗ (n + n')%nat.
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0_nat l : l +ₗ 0%nat = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Global Instance shift_loc_inj l : Inj (=) (=) (shift_loc l).
Proof. destruct l as [b o]; intros n n' [=]; lia. Qed.

Lemma shift_loc_block l n : (l +ₗ n).1 = l.1.
Proof. done. Qed.

