From iris Require Import bi.bi.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import lang notation tactics
  proofmode log_rel_structural wf behavior.
From simuliris.simulang.simple_inv Require Export inv.

(** Define (very basic) Hoare triple notations *)

Section fix_bi.
 Context `{!sheapGS Σ} `{!sheapInv Σ}.
  Definition hoareSim P e_t e_s π Φ : iProp Σ := □ (P -∗ sim_expr Φ π e_t e_s).
  Definition hoareTgt P e_t Ψ : iProp Σ := □ (P -∗ target_red e_t Ψ).
  Definition hoareSrc P e_s π Ψ : iProp Σ := □ (P -∗ source_red e_s π Ψ).
End fix_bi.

(* I do not know why they need to be level 10/20, but otherwise [simple_inv/examples/derived.v] no longer works *)
#[warnings="-closed-notation-not-level-0"]
Notation "'{{{'  P  '}}}'  e_t  ⪯[  π  ] e_s   '{{{'  Φ  '}}}'" := (hoareSim P e_t e_s π Φ) (at level 10) : bi_scope.
#[warnings="-closed-notation-not-level-0"]
Notation "'[{{'  P  '}}]'  e_t  '[{{'  Ψ  '}}]t'" := (hoareTgt P e_t Ψ) (at level 20) : bi_scope.
#[warnings="-closed-notation-not-level-0"]
Notation "'[{{'  P  '}}]'  e_s  @  π  '[{{'  Ψ  '}}]s'" := (hoareSrc P e_s π Ψ) (at level 20) : bi_scope.
