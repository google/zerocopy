(** Notational typeclasses for simulation relations. *)

From iris.bi Require Import bi.
From simuliris.simulation Require Import language.
Import bi.

(** Typeclass for the simulation relation so we can use the definitions with
   greatest+least fp (stuttering) or just greatest fp (no stuttering). *)
Class Sim {SI : sidx} (PROP : bi) (Λ : language) :=
  sim : (val Λ → val Λ → PROP) → thread_id → expr Λ → expr Λ → PROP.
(* We assume only one instance is ever in scope, hence no mode *)

Class SimE {SI : sidx} (PROP : bi) (Λ : language) :=
  sim_expr : (expr Λ → expr Λ → PROP) → thread_id → expr Λ → expr Λ → PROP.
(* We assume only one instance is ever in scope, hence no mode *)

(* FIXME what are good levels for et, es? *)
(* (see https://github.com/rocq-prover/rocq/issues/21916) *)
#[warnings="-postfix-notation-not-level-1"]
Notation "et '⪯{' π '}' es {{ Φ }}" := (sim Φ π et es) (at level 70, Φ at level 200,
  format "'[hv' et  '/' '⪯{' π '}'  '/' es  '/' {{  '[ ' Φ  ']' }} ']'") : bi_scope.

(* FIXME: the notation with binder doesn't work; left-factoring seems to fail.
Notation "et  '⪯'  es  {{  v_t  v_s ,  P  }}" := (sim et es (λ v_t v_s, P)) (at level 40, v_t, v_s at level 200, P at level 200) : bi_scope. *)

(* TODO: different symbols (no brackets) for expr thing *)
#[warnings="-postfix-notation-not-level-1"]
Notation "et '⪯{' π '}' es [{ Φ }]" := (sim_expr Φ π et es) (at level 70, Φ at level 200,
  format "'[hv' et  '/' '⪯{' π '}'  '/' es  '/' [{  '[ ' Φ  ']' }] ']'") : bi_scope.
