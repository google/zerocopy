From iris.prelude Require Import prelude.
From simuliris.stacked_borrows Require Import lang.

(** * "Well-formed" values and expressions.
These definitions basically form our type system. Their main job is to
exclude programs that contain literal locations.  *)

Definition scalar_wf (s : scalar) : Prop :=
  match s with
  | ScPoison | ScInt _ | ScFnPtr _ => True
  | ScPtr _ _  | ScCallId _ => False (* no literal locations or call ids allowed *)
  end.

Definition value_wf (v : value) : Prop := Forall scalar_wf v.

(** This defines a re-usable notion of well-formedness for expressions,
evaluation contexts, and general contexts that can be tweaked by
adjusting [expr_head_wf]. *)
Section expr_wf.

  Context (expr_head_wf : expr_head → Prop).

  (** Lift [expr_head_wf] to expressions. *)
  Fixpoint gen_expr_wf (e : expr) : Prop :=
    expr_head_wf (expr_split_head e).1 ∧
    match e with
    (** [value_wf v] should be part of [expr_head_wf (Val v)] because
        [log_rel_structural] only provides [expr_head_wf]. *)
    | Val v => True
    | Var x => True
    | Let b e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Call e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | BinOp op e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Proj e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Conc e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Copy e => gen_expr_wf e
    | Write e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Alloc T => True
    | Free e => gen_expr_wf e
    | Deref e T => gen_expr_wf e
    | Ref e => gen_expr_wf e
    | Retag e1 e2 pk T k => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Case e branches => gen_expr_wf e ∧ Forall id (fmap gen_expr_wf branches)
    | While e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Fork e => gen_expr_wf e
    (* These should have been handled by [expr_head_wf]. *)
    | EndCall e => gen_expr_wf e
    | InitCall => True (* administrative *)
    | Place _ _ _ => True (* literal pointers *)
    end.

  (** Lift [expr_head_wf] to evaluation contexts. *)
  Definition gen_ectxi_wf (Ki : ectx_item) : Prop :=
    let head := ectxi_split_head Ki in
    expr_head_wf head.1 ∧ Forall gen_expr_wf head.2.
  Definition gen_ectx_wf : ectx → Prop := Forall gen_ectxi_wf.

  Lemma gen_ectx_wf_cons C Ci :
    gen_ectx_wf (Ci :: C) ↔ gen_ectxi_wf Ci ∧ gen_ectx_wf C.
  Proof. rewrite /gen_ectx_wf Forall_cons //. Qed.
  Lemma gen_ectx_wf_app C1 C2 :
    gen_ectx_wf (C1 ++ C2) ↔ gen_ectx_wf C1 ∧ gen_ectx_wf C2.
  Proof. apply Forall_app. Qed.
  Lemma gen_ectx_wf_snoc C Ci :
    gen_ectx_wf (C ++ [Ci]) ↔ gen_ectx_wf C ∧ gen_ectxi_wf Ci.
  Proof. rewrite gen_ectx_wf_app /gen_ectx_wf Forall_singleton //. Qed.

  (** Lift [expr_head_wf] to contexts. *)
  Definition gen_ctxi_wf (Ci : ctx_item) : Prop :=
    let head := ctxi_split_head Ci in
    expr_head_wf head.1 ∧ Forall gen_expr_wf head.2.
  Definition gen_ctx_wf : ctx → Prop := Forall gen_ctxi_wf.

  Lemma gen_ctx_wf_cons C Ci :
    gen_ctx_wf (Ci :: C) ↔ gen_ctxi_wf Ci ∧ gen_ctx_wf C.
  Proof. rewrite /gen_ctx_wf Forall_cons //. Qed.
  Lemma gen_ctx_wf_app C1 C2 :
    gen_ctx_wf (C1 ++ C2) ↔ gen_ctx_wf C1 ∧ gen_ctx_wf C2.
  Proof. apply Forall_app. Qed.
  Lemma gen_ctx_wf_snoc C Ci :
    gen_ctx_wf (C ++ [Ci]) ↔ gen_ctx_wf C ∧ gen_ctxi_wf Ci.
  Proof. rewrite gen_ctx_wf_app /gen_ctx_wf Forall_singleton //. Qed.

  Lemma expr_gen_egen_ctx_wf_fill e Ks :
    gen_expr_wf (fill Ks e) ↔ gen_expr_wf e ∧ gen_ectx_wf Ks.
  Proof.
    elim: Ks e => /=.
    { unfold gen_ectx_wf. naive_solver. }
    move => K Ks IH e. rewrite IH gen_ectx_wf_cons /gen_ectxi_wf.
    destruct K => /=; rewrite ?Forall_cons ?Forall_nil ?Forall_fmap /=; naive_solver.
  Qed.
  Lemma expr_gen_ctx_wf_fill e Cs :
    gen_expr_wf (fill_ctx Cs e) ↔ gen_expr_wf e ∧ gen_ctx_wf Cs.
  Proof.
    elim: Cs e => /=.
    { unfold gen_ctx_wf. naive_solver. }
    move => C Cs IH e. rewrite IH gen_ctx_wf_cons /gen_ctxi_wf.
    destruct C => /=; rewrite ?Forall_cons ?Forall_nil ?Forall_fmap /=; try naive_solver.
    rewrite ?Forall_app ?Forall_cons. naive_solver.
  Qed.
End expr_wf.
