From stdpp Require Import fin_maps fin_map_dom.
From simuliris.simulang Require Import lang notation.


(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | _                               => tac K e
    | Let ?x ?e1 ?e2                  => add_item (LetEctx x e2) K e1
    | Call ?e (Val ?v)                => add_item (CallLEctx v) K e
    | Call ?e1 ?e2                    => add_item (CallREctx e1) K e2
    | UnOp ?op ?e                     => add_item (UnOpEctx op) K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLEctx op v) K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpREctx op e1) K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfEctx e1 e2) K e0
    | Pair ?e (Val ?v)                => add_item (PairLEctx v) K e
    | Pair ?e1 ?e2                    => add_item (PairREctx e1) K e2
    | Fst ?e                          => add_item FstEctx K e
    | Snd ?e                          => add_item SndEctx K e
    | InjL ?e                         => add_item InjLEctx K e
    | InjR ?e                         => add_item InjREctx K e
    | Match ?e0 ?x1 ?e1 ?x2 ?e2       => add_item (MatchEctx x1 e1 x2 e2) K e0
    | AllocN ?e (Val ?v)              => add_item (AllocNLEctx v) K e
    | AllocN ?e1 ?e2                  => add_item (AllocNREctx e1) K e2
    | FreeN ?e1 (Val ?v)              => add_item (FreeNLEctx v) K e1
    | FreeN ?e1 ?e2                   => add_item (FreeNREctx e1) K e2
    | Load ?o ?e                      => add_item (LoadEctx o) K e
    | Store ?o ?e (Val ?v)            => add_item (StoreLEctx o v) K e
    | Store ?o ?e1 ?e2                => add_item (StoreREctx o e1) K e2
(*    | CmpXchg ?e0 (Val ?v1) (Val ?v2) => add_item (CmpXchgLEctx v1 v2) K e0
    | CmpXchg ?e0 ?e1 (Val ?v2)       => add_item (CmpXchgMEctx e0 v2) K e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgREctx e0 e1) K e2
    | FAA ?e (Val ?v)                 => add_item (FaaLEctx v) K e
    | FAA ?e1 ?e2                     => add_item (FaaREctx e1) K e2 *)
    end
  with add_item Ki K e :=
      go (Ki :: K) e
  in
  go (@nil ectx_item) e.

(** The tactic [inv_base_step] performs inversion on hypotheses of the shape
[base_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_base_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : base_step ?P ?e ?σ ?e2 ?σ2 ?efs |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.

Create HintDb base_step.
Global Hint Extern 0 (base_reducible _ _ _) => eexists _, _, _; simpl : base_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (base_step _ _ _ _ _ _) => econstructor : base_step.
(*Global Hint Extern 0 (base_step _ (CmpXchg _ _ _) _ _ _ _) => eapply CmpXchgS : base_step.*)
Global Hint Extern 0 (base_step _ (AllocN _ _) _ _ _ _) => apply alloc_fresh : base_step.

Module W.
  (** A version of [expr] that allows computing substitutions and
  whether an expression is closed even for expressions containing
  unknown code. *)
  Inductive expr :=
  (** Unknown expression e *)
  | Expr (e : simp_lang.expr)
  (** Unknown expression e with known set of free variables *)
  | ClosedExpr (f : list string) (e : simp_lang.expr) (Hfree : free_vars e ⊆ list_to_set f)
  (** [subst_map xs e] *)
  | SubstMap (xs : list (string * val)) (e : expr)

  | Val (v : val)
  | Var (x : string)
  | GlobalVar (x : string)
  | Let (x : binder) (e1 e2 : expr)
  | Call (e1 : expr) (e2 : expr)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | While (e0 e1 : expr)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  | InjL (e : expr)
  | InjR (e : expr)
  | Match (e0 : expr) (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr)
  | Fork (e : expr)
  | AllocN (e1 e2 : expr)
  | FreeN (e1 e2 : expr)
  | Load (o : order) (e : expr)
  | Store (o : order) (e1 : expr) (e2 : expr)
(*  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr)
  | FAA (e1 : expr) (e2 : expr) *)
  .
  Fixpoint to_expr (e : expr) : simp_lang.expr :=
    match e with
    | Expr e => e
    | ClosedExpr f e Hfree => e
    | SubstMap xs e => subst_map (list_to_map xs) (to_expr e)
    | Val v => simp_lang.Val v
    | Var x => simp_lang.Var x
    | GlobalVar x => simp_lang.GlobalVar x
    | Let x e1 e2 => simp_lang.Let x (to_expr e1) (to_expr e2)
    | Call e1 e2 => simp_lang.Call (to_expr e1) (to_expr e2)
    | UnOp op e => simp_lang.UnOp op (to_expr e)
    | BinOp op e1 e2 => simp_lang.BinOp op (to_expr e1) (to_expr e2)
    | If e0 e1 e2 => simp_lang.If (to_expr e0) (to_expr e1) (to_expr e2)
    | While e0 e1 => simp_lang.While (to_expr e0) (to_expr e1)
    | Pair e1 e2 => simp_lang.Pair (to_expr e1) (to_expr e2)
    | Fst e => simp_lang.Fst (to_expr e)
    | Snd e => simp_lang.Snd (to_expr e)
    | InjL e => simp_lang.InjL (to_expr e)
    | InjR e => simp_lang.InjR (to_expr e)
    | Match e0 x1 e1 x2 e2 => simp_lang.Match (to_expr e0) x1 (to_expr e1) x2 (to_expr e2)
    | Fork e => simp_lang.Fork (to_expr e)
    | AllocN e1 e2 => simp_lang.AllocN (to_expr e1) (to_expr e2)
    | FreeN e1 e2 => simp_lang.FreeN (to_expr e1) (to_expr e2)
    | Load o e => simp_lang.Load o (to_expr e)
    | Store o e1 e2 => simp_lang.Store o (to_expr e1) (to_expr e2)
(*    | CmpXchg e0 e1 e2 => simp_lang.CmpXchg (to_expr e0) (to_expr e1) (to_expr e2)
    | FAA e1 e2 => simp_lang.FAA (to_expr e1) (to_expr e2) *)
    end.

  (** [of_expr e] expects [e] to be a simpl_lang.expr and returns a reified [expr] for it. *)
  Ltac of_expr e :=
  lazymatch e with

  | subst_map ?xs ?e =>
    let e := of_expr e in constr:(SubstMap (map_to_list xs) e)
  | simp_lang.Val ?x => constr:(Val x)
  | simp_lang.Var ?x => constr:(Var x)
  | simp_lang.GlobalVar ?x => constr:(GlobalVar x)
  | simp_lang.Let ?x ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Let x e1 e2)
  | simp_lang.Call ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Call e1 e2)
  | simp_lang.UnOp ?op ?e =>
    let e := of_expr e in constr:(UnOp op e)
  | simp_lang.BinOp ?op ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op e1 e2)
  | simp_lang.If ?e1 ?e2 ?e3 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in let e3 := of_expr e3 in constr:(If e1 e2 e3)
  | simp_lang.While ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(While e1 e2)
  | simp_lang.Pair ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Pair e1 e2)
  | simp_lang.Fst ?e =>
    let e := of_expr e in constr:(Fst e)
  | simp_lang.Snd ?e =>
    let e := of_expr e in constr:(Snd e)
  | simp_lang.InjL ?e =>
    let e := of_expr e in constr:(InjL e)
  | simp_lang.InjR ?e =>
    let e := of_expr e in constr:(InjR e)
  | simp_lang.Match ?e1 ?x1 ?e2 ?x2 ?e3 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in let e3 := of_expr e3 in constr:(Match e1 x1 e2 x2 e3)
  | simp_lang.Fork ?e =>
    let e := of_expr e in constr:(Fork e)
  | simp_lang.AllocN ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(AllocN e1 e2)
  | simp_lang.FreeN ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(FreeN e1 e2)
  | simp_lang.Load ?o ?e =>
    let e := of_expr e in constr:(Load o e)
  | simp_lang.Store ?o ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Store o e1 e2)
(*  | simp_lang.CmpXchg ?e1 ?e2 ?e3 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in let e3 := of_expr e3 in constr:(CmpXchg e1 e2 e3)
  | simp_lang.FAA ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(FAA e1 e2) *)

  | _ =>
    lazymatch goal with
    | H : free_vars e ⊆ list_to_set ?f |- _ => constr:(ClosedExpr f e H)
    | _ => constr:(Expr e)
    end
  end.

  Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
    match e with
    | Expr e => (SubstMap [(x, v)]) (Expr e)
    | ClosedExpr f e Hfree =>
      if bool_decide (x ∈ f) then (SubstMap ([(x, v)]) (ClosedExpr f e Hfree)) else ClosedExpr f e Hfree
    | SubstMap xs e => if bool_decide (x ∈ xs.*1) then SubstMap xs e else
                        SubstMap xs (subst x v e)
    | Val v => Val v
    | GlobalVar n => GlobalVar n
    | Var y => if bool_decide (x = y) then Val v else Var y
    | Let y e1 e2 =>
      Let y (subst x v e1) (if bool_decide (BNamed x ≠ y) then subst x v e2 else e2)
    | Call e1 e2 => Call (subst x v e1) (subst x v e2)
    | UnOp op e => UnOp op (subst x v e)
    | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
    | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
    | While e0 e1 => While (subst x v e0) (subst x v e1)
    | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
    | Fst e => Fst (subst x v e)
    | Snd e => Snd (subst x v e)
    | InjL e => InjL (subst x v e)
    | InjR e => InjR (subst x v e)
    | Match e0 x1 e1 x2 e2 => Match (subst x v e0) x1 (if bool_decide (BNamed x ≠ x1) then subst x v e1 else e1)
                                   x2 (if bool_decide (BNamed x ≠ x2) then subst x v e2 else e2)
    | Fork e => Fork (subst x v e)
    | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
    | FreeN e1 e2 => FreeN (subst x v e1) (subst x v e2)
    | Load o e => Load o (subst x v e)
    | Store o e1 e2 => Store o (subst x v e1) (subst x v e2)
(*    | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
    | FAA e1 e2 => FAA (subst x v e1) (subst x v e2) *)
    end.

  Lemma to_expr_subst x v e :
    to_expr (subst x v e) = simp_lang.subst x v (to_expr e).
  Proof.
    elim: e; simpl; intros.
    all: (repeat case_decide => //=); f_equal; eauto.
    - by rewrite -subst_map_subst subst_map_empty.
    - by rewrite -subst_map_subst subst_map_empty.
    - rewrite subst_free_vars //. set_solver.
    - rewrite subst_free_vars // free_vars_subst_map dom_list_to_map. set_solver.
    - revert select (to_expr _ = _) => ->.
      rewrite subst_map_subst -subst_subst_map delete_id //.
      apply/not_elem_of_dom. rewrite dom_list_to_map. set_solver.
  Qed.

  Lemma tac_to_expr_subst x v e (P : _ → Prop) e' e'':
    (e = to_expr e') →
    (subst x v e' = e'') →
    P (to_expr e'') →
    P (simp_lang.subst x v e).
  Proof. move => -> <-. by rewrite to_expr_subst. Qed.

  Definition add_substmap (xs : list (string * val)) (e : expr) : expr :=
    match xs with
    | [] => e
    | _ => SubstMap xs e
    end.
  Lemma to_expr_add_substmap xs e :
    to_expr (add_substmap xs e) = subst_map (list_to_map xs) (to_expr e).
  Proof. destruct xs => //=. by rewrite subst_map_empty. Qed.

  (** This function collapses multiple consecutive [SubstMap] which
  can arise after [subst] on closed expressions. *)
  Fixpoint combine_subst_map (xs : list (string * val)) (e : expr)  : expr :=
    match e with
    | SubstMap ys e => combine_subst_map (ys ++ xs) e
    | Expr e => add_substmap xs $ Expr e
    | ClosedExpr f e Hfree => add_substmap xs $ ClosedExpr f e Hfree
    | Val v => add_substmap xs $ Val v
    | Var y => add_substmap xs $ Var y
    | GlobalVar y => add_substmap xs $ GlobalVar y
    | Let y e1 e2 => add_substmap xs $
      Let y (combine_subst_map [] e1) (combine_subst_map [] e2)
    | Call e1 e2 => add_substmap xs $ Call (combine_subst_map [] e1) (combine_subst_map [] e2)
    | UnOp op e => add_substmap xs $ UnOp op (combine_subst_map [] e)
    | BinOp op e1 e2 => add_substmap xs $ BinOp op (combine_subst_map [] e1) (combine_subst_map [] e2)
    | If e0 e1 e2 => add_substmap xs $ If (combine_subst_map [] e0) (combine_subst_map [] e1) (combine_subst_map [] e2)
    | While e0 e1 => add_substmap xs $ While (combine_subst_map [] e0) (combine_subst_map [] e1)
    | Pair e1 e2 => add_substmap xs $ Pair (combine_subst_map [] e1) (combine_subst_map [] e2)
    | Fst e => add_substmap xs $ Fst (combine_subst_map [] e)
    | Snd e => add_substmap xs $ Snd (combine_subst_map [] e)
    | InjL e => add_substmap xs $ InjL (combine_subst_map [] e)
    | InjR e => add_substmap xs $ InjR (combine_subst_map [] e)
    | Match e0 x1 e1 x2 e2 => add_substmap xs $ Match (combine_subst_map [] e0) x1 (combine_subst_map [] e1)
                                   x2 (combine_subst_map [] e2)
    | Fork e => add_substmap xs $ Fork (combine_subst_map [] e)
    | AllocN e1 e2 => add_substmap xs $ AllocN (combine_subst_map [] e1) (combine_subst_map [] e2)
    | FreeN e1 e2 => add_substmap xs $ FreeN (combine_subst_map [] e1) (combine_subst_map [] e2)
    | Load o e => add_substmap xs $ Load o (combine_subst_map [] e)
    | Store o e1 e2 => add_substmap xs $ Store o (combine_subst_map [] e1) (combine_subst_map [] e2)
(*    | CmpXchg e0 e1 e2 => add_substmap xs $ CmpXchg (combine_subst_map [] e0) (combine_subst_map [] e1) (combine_subst_map [] e2)
    | FAA e1 e2 => add_substmap xs $ FAA (combine_subst_map [] e1) (combine_subst_map [] e2) *)
    end.

  Lemma to_expr_combine_subst_map xs e :
    to_expr (combine_subst_map xs e) = subst_map (list_to_map xs) (to_expr e).
  Proof.
    elim: e xs; simpl; intros; rewrite ?to_expr_add_substmap //=.
    { revert select (∀ xs, _) => ->. by rewrite list_to_map_app subst_map_subst_map. }
    all: do 2 f_equal.
    all: repeat match goal with | H : ∀ xs, _ |- _ => specialize (H []) end.
    all: etrans; [eassumption|] => /=; by rewrite subst_map_empty.
  Qed.

  Lemma to_expr_combine_subst_map_empty e :
    to_expr (combine_subst_map [] e) = to_expr e.
  Proof. by rewrite to_expr_combine_subst_map subst_map_empty. Qed.

  Lemma tac_to_expr_combine_subst_map e (P : _ → Prop) e':
    (combine_subst_map [] e = e') →
    P (to_expr e') →
    P (to_expr e).
  Proof. move => <-. by rewrite to_expr_combine_subst_map_empty. Qed.

  (** This function computes the free variables of [e]. Note that this
  function returns too few free variables for unknown expressions [Expr
  e]. Thus, we don't have a soundness proof like in the other cases,
  but this function is still useful for the [log_rel] tactic. *)
  Fixpoint free_vars (e : expr) : list string :=
  match e with
  | Expr _ => [] (* bogus but we don't care *)
  | ClosedExpr f _ _ => f
  | SubstMap xs e => (filter (λ v, v ∉ xs.*1) (free_vars e))
  | Val v => []
  | Var x => [x]
  | GlobalVar x => []
  | Let x e1 e2 => free_vars e1 ++ (filter (λ v, v ∉ binder_list x) (free_vars e2))
  | Match e0 x1 e1 x2 e2 =>
    free_vars e0 ++
    (filter (λ v, v ∉ binder_list x1) (free_vars e1)) ++
    (filter (λ v, v ∉ binder_list x2) (free_vars e2))
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Load _ e =>
     free_vars e
  | Call e1 e2 | While e1 e2 | BinOp _ e1 e2 | Pair e1 e2
  | AllocN e1 e2 | FreeN e1 e2 | Store _ e1 e2 =>
     free_vars e1 ++ free_vars e2
  | If e0 e1 e2 =>
     free_vars e0 ++ free_vars e1 ++ free_vars e2
  end.

  Fixpoint is_closed (free : list string) (e : expr) : bool :=
  match e with
  | Expr _ => false
  | ClosedExpr f _ _ => bool_decide (f ⊆+ free)
  | SubstMap xs e => is_closed (xs.*1 ++ free) e
  | Val v => true
  | Var x => bool_decide (x ∈ free)
  | GlobalVar x => true
  | Let x e1 e2 => is_closed free e1 && is_closed (binder_list x ++ free) e2
  | Match e0 x1 e1 x2 e2 =>
    is_closed free e0 &&
    is_closed (binder_list x1 ++ free) e1 &&
    is_closed (binder_list x2 ++ free) e2
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Load _ e =>
     is_closed free e
  | Call e1 e2 | While e1 e2 | BinOp _ e1 e2 | Pair e1 e2
  | AllocN e1 e2 | FreeN e1 e2 | Store _ e1 e2 =>
     is_closed free e1 && is_closed free e2
  | If e0 e1 e2 =>
     is_closed free e0 && is_closed free e1 && is_closed free e2
  end.

  Lemma to_expr_is_closed xs e:
    is_closed xs e → simp_lang.free_vars (to_expr e) ⊆ list_to_set xs.
  Proof.
    elim: e xs; simpl; try done; intros.
    all: destruct_and?.
    all: repeat match goal with | H : (∀ xs, _) |- _ => specialize (H _ ltac:(done)) end.
    { etrans; [eassumption|]. set_unfold => ??. by apply: elem_of_submseteq. }
    { revert select (_ ⊆ _). rewrite free_vars_subst_map list_to_set_app dom_list_to_map. set_solver. }
    all: repeat match goal with | x : binder |- _ => destruct x end; set_solver.
  Qed.

  Lemma to_expr_is_closed_empty e:
    is_closed [] e → simp_lang.free_vars (to_expr e) = ∅.
  Proof. move => /to_expr_is_closed. set_solver. Qed.

End W.

Ltac simpl_subst :=
  repeat match goal with
    | |- context C [apply_func ?fn ?v] =>
      (* Unfold [apply_func] if the function's components are available *)
      let arg := open_constr:(_ : string) in
      let body := open_constr:(_ : expr) in
      unify fn (arg, body);
      change (apply_func fn v) with (subst arg v body)
    end;
  repeat match goal with
    | |- context C [subst ?x ?v ?e] =>
      lazymatch e with
      | subst _ _ _ => fail
      | _ => idtac
      end;
      pattern (subst x v e);
      let e' := W.of_expr e in
      simple refine (W.tac_to_expr_subst _ _ _ _ e' _ _ _ _); [ shelve
      | simpl; rewrite ?list_to_map_to_list; reflexivity
      | vm_compute W.subst; reflexivity
      |];
      simple refine (W.tac_to_expr_combine_subst_map _ _ _ _ _); [ shelve
      | vm_compute W.combine_subst_map; reflexivity
      | ];
      simpl
    end.
Arguments subst : simpl never.

Ltac solve_is_closed :=
  lazymatch goal with
  (* Recognize both aliases of [free_vars] *)
  | |- simp_lang.free_vars ?e = ∅ =>
    let e' := W.of_expr e in
    apply (W.to_expr_is_closed_empty e');
    compute_done
  | |- language.free_vars ?e = ∅ =>
    let e' := W.of_expr e in
    apply (W.to_expr_is_closed_empty e');
    compute_done
  end.
