From simuliris.simulang Require Import lang.

(** * "Well-formed" values and expressions.
These definitions basically form our type system. Their main job is to
exclude programs that contain literal locations.  *)

Fixpoint val_wf (v : val) : Prop :=
  match v with
  | LitV (LitLoc l) => False (* no literal locations allowed *)
  | LitV _ => True
  | PairV v1 v2 => val_wf v1 ∧ val_wf v2
  | InjLV v => val_wf v
  | InjRV v => val_wf v
  end.

(** This defines a re-usable notion of well-formedness for expressions,
evaluation contexts, and general contexts that can be tweaked by
adjusting [expr_head_wf]. *)
Section expr_wf.

  Context (expr_head_wf : expr_head → Prop).

  (** Lift [expr_head_wf] to expressions. *)
  Fixpoint gen_expr_wf (e : expr) : Prop :=
    expr_head_wf (expr_split_head e).1 ∧
    match e with
    (** [val_wf v] should be part of [expr_head_wf (Val v)] because
        [log_rel_structural] only provides [expr_head_wf]. *)
    | Val v => True
    | Var x => True
    | GlobalVar x => True
    | Let b e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Call e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | UnOp op e => gen_expr_wf e
    | BinOp op e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | If e1 e2 e3 => gen_expr_wf e1 ∧ gen_expr_wf e2 ∧ gen_expr_wf e3
    | While e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Pair e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Fst e => gen_expr_wf e
    | Snd e => gen_expr_wf e
    | InjL e => gen_expr_wf e
    | InjR e => gen_expr_wf e
    | Match e x1 e1 x2 e2 => gen_expr_wf e ∧ gen_expr_wf e1 ∧ gen_expr_wf e2
    | Fork e => gen_expr_wf e
    | AllocN e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | FreeN e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
    | Load o e => gen_expr_wf e
    | Store o e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2
(*    | CmpXchg e1 e2 e3 => gen_expr_wf e1 ∧ gen_expr_wf e2 ∧ gen_expr_wf e3
    | FAA e1 e2 => gen_expr_wf e1 ∧ gen_expr_wf e2 *)
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
    destruct K => /=; rewrite ?Forall_cons ?Forall_nil /=; naive_solver.
  Qed.
  Lemma expr_gen_ctx_wf_fill e Cs :
    gen_expr_wf (fill_ctx Cs e) ↔ gen_expr_wf e ∧ gen_ctx_wf Cs.
  Proof.
    elim: Cs e => /=.
    { unfold gen_ctx_wf. naive_solver. }
    move => C Cs IH e. rewrite IH gen_ctx_wf_cons /gen_ctxi_wf.
    destruct C => /=; rewrite ?Forall_cons ?Forall_nil /=; naive_solver.
  Qed.
End expr_wf.
