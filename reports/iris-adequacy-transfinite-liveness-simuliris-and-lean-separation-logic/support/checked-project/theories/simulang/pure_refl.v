From simuliris.simulation Require Import slsls lifting gen_log_rel.
From simuliris.simulang Require Import proofmode tactics.
From simuliris.simulang Require Import primitive_laws gen_val_rel log_rel_structural wf gen_refl globalbij.

(** * Reflexivity theorem for pure expressions
This file defines a notion of pure expressions and proves a
reflexivity theorem for them. *)

Section log_rel.
  Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Context (loc_rel : loc → loc → iProp Σ) {Hpers : ∀ l_t l_s, Persistent (loc_rel l_t l_s)}.
  Context (thread_own : thread_id → iProp Σ).
  Local Notation val_rel := (gen_val_rel loc_rel).
  Local Notation log_rel := (gen_log_rel val_rel thread_own).

  (** [pure_expr_head_wf] characterizes pure expressions. Note that
  [GlobalVar] is considered pure even though it reads the [globals]
  field of the state and thus [pure_log_rel_structural] requires the
  [sheap_inv_contains_globalbij] precondition. *)
  Definition pure_expr_head_wf (e : expr_head) : Prop :=
    match e with
    | ValHead v => val_wf v
    | VarHead _ | GlobalVarHead _ | LetHead _ | UnOpHead _ | BinOpHead _ | IfHead | WhileHead
    | PairHead | FstHead | SndHead | InjLHead | InjRHead | MatchHead _ _ => True
    | _ => False
    end.

  Theorem pure_log_rel_structural :
    loc_rel_func_law loc_rel →
    loc_rel_inj_law loc_rel →
    loc_rel_offset_law loc_rel →
    sheap_inv_contains_globalbij loc_rel →
    log_rel_structural loc_rel thread_own pure_expr_head_wf.
  Proof using Hpers.
    intros ???? e_t e_s head_t head_s Hwf Hs. iIntros "IH".
    destruct e_t; simpl in Hs; destruct e_s => //=; simpl in Hs; simplify_eq.
    all: try iDestruct "IH" as "[IH IH1]".
    all: try iDestruct "IH1" as "[IH1 IH2]".
    all: try iDestruct "IH2" as "[IH2 IH3]".
    - (* Val *) iApply log_rel_val. by iApply val_wf_sound.
    - (* Var *) by iApply log_rel_var.
    - (* GlobalVar *) by iApply log_rel_global_var.
    - (* Let *) by iApply (log_rel_let with "IH IH1").
    - (* UnOp *) by iApply (log_rel_unop with "IH").
    - (* BinOp *) by iApply (log_rel_binop with "IH IH1").
    - (* If *) by iApply (log_rel_if with "IH IH1 IH2").
    - (* While *) by iApply (log_rel_while with "IH IH1").
    - (* Pairs *) by iApply (log_rel_pair with "IH IH1").
    - (* Fst *) by iApply (log_rel_fst with "IH").
    - (* Snd *) by iApply (log_rel_snd with "IH").
    - (* InjL *) by iApply (log_rel_injl with "IH").
    - (* InjR *) by iApply (log_rel_injr with "IH").
    - (* Match *) by iApply (log_rel_match with "IH IH1 IH2").
  Qed.
End log_rel.
