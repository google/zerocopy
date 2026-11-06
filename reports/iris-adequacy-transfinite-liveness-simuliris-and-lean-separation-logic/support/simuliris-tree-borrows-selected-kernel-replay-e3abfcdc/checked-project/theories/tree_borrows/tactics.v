From simuliris.tree_borrows Require Import lang.
From stdpp Require Import fin_maps.


(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _                               => tac K e
    | Call ?e (Val ?v)                => add_item (CallLEctx (ValR v)) K e
    | Call ?e (of_result ?v)          => add_item (CallLEctx v) K e
    | Call ?e (Place ?l ?t ?T)        => add_item (CallLEctx (PlaceR l t T)) K e
    | Call ?e1 ?e2                    => add_item (CallREctx e1) K e2
    | EndCall ?e                      => add_item (EndCallEctx) K e
    | Proj ?e1 (Val ?v)               => add_item (ProjLEctx (ValR v)) K e1
    | Proj ?e1 (of_result ?v)         => add_item (ProjLEctx v) K e1
    | Proj ?e1 (Place ?l ?t ?T)       => add_item (ProjLEctx (PlaceR l t T)) K e1
    | Proj ?e1 ?e2                    => add_item (ProjREctx e1) K e2
    | Conc ?e1 (Val ?v)               => add_item (ConcLEctx (ValR v)) K e1
    | Conc ?e1 (of_result ?v)         => add_item (ConcLEctx v) K e1
    | Conc ?e1 (Place ?l ?t ?T)       => add_item (ConcLEctx (PlaceR l t T)) K e1 
    | Conc ?e1 ?e2                    => add_item (ConcREctx e1) K e2
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLEctx op (ValR v)) K e
    | BinOp ?op ?e (of_result ?v)     => add_item (BinOpLEctx op v) K e
    | BinOp ?op ?e (Place ?l ?t ?T)   => add_item (BinOpLEctx op (PlaceR l t T)) K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpREctx op e1) K e2
    | Deref ?e ?T                     => add_item (DerefEctx T) K e
    | Ref ?e                          => add_item RefEctx K e
    | Copy ?e                         => add_item CopyEctx K e
    | Write ?e (Val ?v)               => add_item (WriteLEctx (ValR v)) K e
    | Write ?e (of_result ?v)         => add_item (WriteLEctx v) K e
    | Write ?e (Place ?l ?t ?T)       => add_item (WriteLEctx (PlaceR l t T)) K e
    | Write ?e1 ?e2                   => add_item (WriteREctx e1) K e2 
    | Free ?e                         => add_item FreeEctx K e
    | Retag ?e (Val ?v) ?pk ?im ?T ?rk => add_item (RetagLEctx (ValR v) pk im T rk) K e
    | Retag ?e (of_result ?v) ?pk ?im ?T ?rk => add_item (RetagLEctx v pk im T rk) K e
    | Retag ?e (Place ?l ?t ?T) ?pk ?im ?T ?rk => add_item (RetagLEctx (PlaceR l t T) pk im T rk) K e
    | Retag ?e1 ?e2 ?pk ?im ?T ?rk    => add_item (RetagREctx e1 pk im T rk) K e2
    | Let ?x ?e1 ?e2                  => add_item (LetEctx x e2) K e1
    | Case ?e ?el                     => add_item (CaseEctx el) K e 
    end
  with add_item Ki K e :=
      go (Ki :: K) e
  in
  go (@nil ectx_item) e.

Ltac inv_base_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : base_step _ ?e _ _ _ _ |- _  =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H ; subst; clear H
  | H : mem_expr_step _ _ _ _ _ _ |- _ =>
      inversion H ; subst; clear H
  | H : pure_expr_step _ _ _ _ _ |- _ =>
      inversion H ; subst; clear H
  | H : bor_step _ _ _ _ _ _ _ _ _ |- _ =>
      inversion H ; subst; clear H
  | H : bin_op_eval _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  end.

Create HintDb base_step.
Global Hint Extern 0 (base_reducible _ _ _) => eexists _, _, _; simpl : base_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (base_step _ _ _ _ _ _) => econstructor : base_step.
