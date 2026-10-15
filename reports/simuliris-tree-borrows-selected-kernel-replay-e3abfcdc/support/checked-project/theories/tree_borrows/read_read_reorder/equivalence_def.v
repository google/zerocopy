From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.tree_borrows Require Import defs lang_base lang notation bor_semantics tree tactics class_instances.
From simuliris.tree_borrows.read_read_reorder Require Import low_level.

(* [nsteps ... n] says that one can transition from one state to the other in exactly [n]
primitive steps. *)
(* This is similar to stdpp's [nsteps], except that this one computes more nicely for fixed [n]. *)
Fixpoint nsteps P (e : expr) σ e'' σ'' n : Prop := match n with
  0 => e = e'' ∧ σ = σ''
| S n => ∃ e' σ', prim_step P e σ e' σ' nil ∧ nsteps P e' σ' e'' σ'' n end.

(* This says that after n steps, any state reachable in from e_1 in σ must be reachable from e_2 in σ.
   This is just a helper definition used for [eventually_equal]; on its own it is not very meaningful. *)
Definition identical_states_after P e1 e2 σ n := 
  ∀ e' σ', nsteps P e1 σ e' σ' n → nsteps P e2 σ e' σ' n.

(* This says that the program will not terminate within a number of steps.
   It can, in that time, only make progress or have UB *)
Inductive no_termination_within P : expr → state → nat → Prop := 
  | no_steps_left e σ : no_termination_within P e σ 0
  | no_termination_now e σ n :
     to_result e = None →
    (∀ e' σ', prim_step P e σ e' σ' nil → no_termination_within P e' σ' n) →
    no_termination_within P e σ (S n).

(* Two programs are eventually equal if there exists an n such that they
   both do not terminate with n steps,
  and after n steps, they are equal. *)
Definition eventually_equal P e1 e2 :=
  ∃ n, ∀ σ, state_wf σ →
    no_termination_within P e1 σ n ∧
    no_termination_within P e2 σ n ∧
    identical_states_after P e1 e2 σ n ∧
    identical_states_after P e2 e1 σ n.
