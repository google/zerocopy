From iris.prelude Require Import prelude options.
From simuliris.tree_borrows Require Export lang_base.

Coercion of_result : result >-> expr.
Coercion Var : string >-> expr.

Coercion Val : value >-> expr.
Coercion ValR : value >-> result.

Notation "[ ]" := (@nil binder) : binder_scope.
Notation "a :: b" := (@cons binder a%binder b%binder)
  (at level 60, right associativity) : binder_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons binder x1%binder (@cons binder x2%binder
        (..(@cons binder xn%binder (@nil binder))..))) : binder_scope.
Notation "[ x ]" := (@cons binder x%binder (@nil binder)) : binder_scope.

(** Function arguments *)
Notation "[ ]" := (@nil expr) : expr_scope.
Notation "[ x ]" := (@cons expr x%E (@nil expr)) : expr_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons expr x1%E (@cons expr x2%E
        (..(@cons expr xn%E (@nil expr))..))) : expr_scope.

(** Values *)
Notation "#[ ]" := (Val (@nil scalar)) : expr_scope.
Notation "#[ x1 ; .. ; xn ]" :=
  (Val (@cons scalar x1%S
        (..(@cons scalar xn%S (@nil scalar))..))) : expr_scope.

Notation "#[ ]" := (Val (@nil scalar)) : val_scope.
Notation "#[ x1 ; .. ; xn ]" :=
  (Val (@cons scalar x1%S 
        (..(@cons scalar xn%S (@nil scalar))..))) : val_scope.


Notation "# v" := (ValR v%V%R%L) (at level 8, format "# v") : result_scope.
Notation "# v" := (Val v%V%R%L) (at level 8, format "# v") : expr_scope.

(** Pointer operations *)
Notation "& e" := (Ref e%E) (at level 8, format "& e") : expr_scope.
Notation "*{ ptrk } e" := (Deref (Copy e%E) ptrk)
  (at level 9, format "*{ ptrk }  e") : expr_scope.

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)

Notation "'case:' e0 'of' el" := (Case e0%E el%E)
  (at level 102, e0, el at level 150) : expr_scope.
Notation "'if:' e0 'then' e1 'else' e2" := (Case e0%E [e2%E;e1%E])
  (only parsing, at level 102, e0, e1, e2 at level 150) : expr_scope.
Notation "'while:' e1 'do' e2 'od'" := (While e1%E e2%E)
  (at level 0, e1, e2 at level 150) : expr_scope.
Notation "☠" := ScPoison : sc_scope.

(* Notation "! e" := (Read e%E) (at level 9, format "! e") : expr_scope. *)

(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Write e1%E e2%E)
  (at level 80) : expr_scope.

Notation "e1 + e2" := (BinOp AddOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 - e2" := (BinOp SubOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E)
  (at level 70) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E)
  (at level 70) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E)
  (at level 70) : expr_scope.
Notation "e1 +ₗ e2" := (BinOp OffsetOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.

Notation "'let:' x := e1 'in' e2" := (Let x%binder e1%E e2%E)
  (at level 102, x at level 1, e1, e2 at level 150) : expr_scope.
Notation "e1 ;; e2" := (let: <> := e1 in e2)%E
  (at level 100, e2 at level 200, format "e1  ;;  e2") : expr_scope.
Notation Skip := (#[☠] ;; #[☠])%E.

(* These are not actually results, but we want them to be pretty-printed. *)
Notation "'let:' x := e1 'in' e2" := (Let x%binder e1%E e2%E)
  (at level 102, x at level 1, e1, e2 at level 150) : result_scope.
Notation "e1 ;; e2" := (let: <> := e1 in e2)%R
  (at level 100, e2 at level 200, format "e1  ;;  e2") : result_scope.


Ltac solve_closed :=
  match goal with
  | |- Closed ?X ?e =>
      (vm_compute; exact I) || (rewrite /= bool_decide_true; set_solver)
  end.
#[global]
Hint Extern 0 (Closed _ _) => solve_closed : typeclass_instances.
