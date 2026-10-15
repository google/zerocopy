From stdpp Require Import gmap.
From iris.prelude Require Import prelude.
From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import behavior.
From simuliris.simulang Require Import lang notation wf gen_val_rel.


(** Define "observable behavior" and contextual refinement. *)

(** We currently don't allow global variables that initially contain
pointers. However, this is not a real restriction as [main] can
store pointers in global variables. (In fact, it would be good
enough to 0-initialize all global variables.) *)
Definition init_state (σ_t σ_s : state) : Prop :=
  ∃ gs, map_Forall (λ _ v, val_wf v) gs ∧ σ_t = state_init gs ∧ σ_s = state_init gs.

Fixpoint obs_val (v_t v_s : val) {struct v_s} : Prop :=
  match v_t, v_s with
  | LitV (LitLoc l_t), LitV (LitLoc l_s) =>
    True (* the details of locations are not observable *)
  | LitV l_t, LitV l_s =>
    l_t = l_s
  | PairV v1_t v2_t, PairV v1_s v2_s =>
    obs_val v1_t v1_s ∧ obs_val v2_t v2_s
  | InjLV v_t, InjLV v_s =>
    obs_val v_t v_s
  | InjRV v_t, InjRV v_s =>
    obs_val v_t v_s
  | _,_ => False
  end.

(** The simulang instance of [prog_ref]. *)
Definition prog_ref := prog_ref init_state "main" #() obs_val.

Global Instance obs_val_refl : Reflexive obs_val.
Proof.
  intros v. induction v as [ [ | | | | | ] | | | ]; naive_solver.
Qed.
Global Instance obs_val_trans : Transitive obs_val.
Proof.
  intros v1 v2 v3 H1 H2.
  induction v3 as [ [ | | | | | ] | v31 IH1 v32 IH2 | v3 IH | v3 IH] in v1, v2, H1, H2 |-*.
  all: destruct v2 as [ [ | | | | | ] | | | ]; simpl in H2; try inversion H2; subst.
  all: destruct v1 as [ [ | | | | | ] | | | ]; simpl in H1; try inversion H1; subst; naive_solver.
Qed.

Lemma prog_ref_refl : Reflexive prog_ref.
Proof.
  apply prog_ref_refl; last apply obs_val_refl.
  intros ?? (g & ? & ? & ?). subst. done.
Qed.
Lemma prog_ref_trans : Transitive prog_ref.
Proof.
  apply prog_ref_trans; last apply obs_val_trans.
  intros ?? (g & ? & ? & ?). subst. done.
Qed.


(** Default well-formedness for SimuLang. *)
Definition simulang_wf (e : expr_head) : Prop :=
  match e with
  | ValHead v => val_wf v
  (* Na2Ord is an intermediate (administrative) ordering that should only
       arise during execution and programs should not use it directly. *)
  | LoadHead o => o ≠ Na2Ord
  | StoreHead o => o ≠ Na2Ord
  | _ => True
  end.

Notation expr_wf := (gen_expr_wf simulang_wf).
Notation ectx_wf := (gen_ectx_wf simulang_wf).
Notation ctx_wf := (gen_ctx_wf simulang_wf).

(** Contextual refinement. *)
Definition ctx_ref (e_t e_s : expr) :=
  ∀ (C : ctx) (fname x : string) (p : prog),
    (* The other functions need to be well-formed and closed *)
    map_Forall (λ _ '(arg, body), expr_wf body ∧ free_vars body ⊆ {[arg]}) p →
    (* The context needs to be well-formed *)
    ctx_wf C →
    (* The context needs to close our expressions *)
    free_vars (fill_ctx C e_t) ∪ free_vars (fill_ctx C e_s) ⊆ {[x]} →
    (* Then we demand [prog_ref] if putting our expressions into a context to
       obtain a whole function and that function into a program *)
    prog_ref (<[fname := (x, fill_ctx C e_t)]> p) (<[fname := (x, fill_ctx C e_s)]> p).

Lemma ctx_ref_refl :
  Reflexive ctx_ref.
Proof.
  intros e C fname x p Hbodies Hctx Hfv.
  apply prog_ref_refl.
Qed.
