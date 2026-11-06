(******************************************************************************)
(** * C11 is weaker than IMM_S   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob imm_s_ppo.
Require Import imm_s_hb.
Require Import imm_s C11.

Set Implicit Arguments.

Section C11_TO_IMM_S.

Variable G : execution.

(******************************************************************************)
(** relations are contained in the corresponding ones **  *)
(******************************************************************************)

Lemma s_imm_consistentimplies_c11_consistent (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  c11_consistent G.
Proof using.
  cdes IPC. cdes IC. red. splits; auto.
Qed.

End C11_TO_IMM_S.