From stdpp Require Import gmap.
From iris.prelude Require Import prelude.
From simuliris.simulation Require Import behavior.
From simuliris.stacked_borrows Require Import defs wf.

(** Define "observable behavior" and contextual refinement. *)

(** Force initial state to be empty *)
Definition init_state (σ_t σ_s : state) : Prop :=
  σ_t = init_state ∧ σ_s = init_state.

Definition obs_scalar (sc_t sc_s : scalar) :=
  match sc_t, sc_s with
  | ScPtr l1 t1, ScPtr l2 t2 => True (* the details of locations are not observable *)
  | ScInt z1, ScInt z2 => z1 = z2
  | ScFnPtr f1, ScFnPtr f2 => f1 =f2
  | ScCallId c1, ScCallId c2 => c1 = c2
  | _, ScPoison => True (* anything is compatibl with "poison" in the source *)
  | _, _ => False
  end
.
Definition obs_value (v_t v_s : value) : Prop := Forall2 obs_scalar v_t v_s.
Definition obs_result (r_t r_s : val bor_lang) : Prop :=
  match r_t, r_s with
  | PlaceR _ _ _, PlaceR _ _ _ =>
    True (* the details of locations are not observable *)
  | ValR v_t, ValR v_s => obs_value v_t v_s
  | _, _ => False
  end.

(** The Stacked Borrows instance of [prog_ref]. *)
Definition prog_ref := prog_ref init_state "main" (ValR [ScPoison]) obs_result.

(** Default well-formedness for Stacked Borrows *)
Definition stackedborrows_wf (e : expr_head) : Prop :=
  match e with
  | ValHead v => value_wf v
  | PlaceHead _ _ _ => False (* no literal pointers *)
  | _ => True
  end.

Notation expr_wf := (gen_expr_wf stackedborrows_wf).
Notation ectx_wf := (gen_ectx_wf stackedborrows_wf).
Notation ctx_wf := (gen_ctx_wf stackedborrows_wf).

(** Contextual refinement *)
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
