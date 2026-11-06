(******************************************************************************)
(** * RC11 is weaker than IMM_S   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob imm_s_ppo.
Require Import imm_s_hb.
Require Import imm_s.
Require Import RC11.

Set Implicit Arguments.

Section RC11_TO_IMM_S.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).

Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).

Notation "'detour'" := (detour G).

Notation "'rs'" := (rs G).
Notation "'release'" := (release G).
Notation "'sw'" := (sw G).
Notation "'hb'" := (hb G).

Notation "'ar_int'" := (ar_int G).
Notation "'ppo'" := (ppo G).
Notation "'bob'" := (bob G).

Notation "'ar'" := (ar G).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(******************************************************************************)
(** relations are contained in the corresponding ones **  *)
(******************************************************************************)

Lemma s_imm_consistentimplies_rc11_consistent (WF: Wf G) 
      (COND: ⦗R \₁ Acq⦘ ⨾ sb ⨾ ⦗W \₁ Rel⦘ ⊆ sb ⨾ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb ∪ ⦗R⦘ ⨾ deps ⨾ ⦗W⦘ ∪ rmw) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  rc11_consistent G.
Proof using.
  cdes IPC. cdes IC.
  red. splits; auto.
  rewrite rfi_union_rfe with (G:=G). 
  unfold Execution.rfi; rewrite inclusion_inter_l2, <- unionA, unionK.
  eapply acyclic_ud with (adom := W) (bdom := R); eauto using sb_acyclic.
  1-2: by destruct WF; unfold Execution.rfe; rewrite wf_rfD; eauto using minus_doma, minus_domb with hahn. 
  assert (T:= @sb_trans G); relsf; clear T.
  eapply irreflexive_inclusion, Cext; apply inclusion_t_t2. 
  unfold imm_s.ar, imm_s_ppo.ar_int; unionL; eauto with hahn.
  arewrite (R ≡₁ (R ∩₁ Acq) ∪₁ (R \₁ Acq)).
    by unfolder; split; ins; desf; destruct (is_acq lab x); auto. 
  rewrite id_union; relsf; unionL.
    by rewrite inclusion_seq_eqv_r at 1; unfold imm_bob.bob; auto 10 with hahn.
  arewrite (W ≡₁ (W ∩₁ Rel) ∪₁ (W \₁ Rel)) at 1.
    by unfolder; split; ins; desf; destruct (is_rel lab x); auto. 
  rewrite id_union; relsf; unionL.
    by rewrite inclusion_seq_eqv_l at 1; unfold imm_bob.bob, imm_bob.fwbob; auto 10 with hahn.
  rewrite COND.
  sin_rewrite rmw_in_ppo; auto.
  arewrite (⦗R⦘ ⨾ deps ⨾ ⦗W⦘ ⊆ ppo).
  { rewrite <- deps_rfi_in_ppo.
    sin_rewrite (ct_step deps).
    rewrite unionC, ct_unionE.
    basic_solver. }
  unionL.
  { rewrite <- seq_eqvK, seqA, <- seqA. 
    apply inclusion_step2_ct; unfold imm_bob.bob, imm_bob.fwbob; auto 10 with hahn. }
  all: etransitivity; [|by apply ct_step].
  all: basic_solver 20.
Qed.

End RC11_TO_IMM_S.
