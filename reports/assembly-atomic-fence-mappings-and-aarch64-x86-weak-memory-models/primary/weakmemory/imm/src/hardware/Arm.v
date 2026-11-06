(******************************************************************************)
(** * Definition of the ARMv8.3 memory model                                  *)
(* a fragment of the full model                                                *)
(* (omitting dmb.st, LDAR, and isb that are not used in compiled programs)    *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.

Set Implicit Arguments.

Section Arm.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'deps'" := (deps G).
Notation "'fre'" := (fre G).
Notation "'rfe'" := (rfe G).
Notation "'coe'" := (coe G).
Notation "'detour'" := (detour G).
Notation "'coi'" := (coi G).
Notation "'rfi'" := (rfi G).
Notation "'fri'" := (fri G).
Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).

Notation "'L'" := (W ∩₁ (fun a => is_true (is_rel lab a))).
Notation "'Q'" := (R ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'A'" := (R ∩₁ (fun a => is_true (is_sc  lab a))).

Notation "'F^ld'" := (F ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'F^sy'" := (F ∩₁ (fun a => is_true (is_rel lab a))).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(* Observed-by *)
Definition obs := rfe ∪ coe ∪ fre.

(* Dependency-ordered-before *)
Definition dob :=
   (addr ∪ data) ⨾ rfi^?
 ∪ (ctrl ∪ data) ⨾ ⦗W⦘ ⨾ coi^?
 ∪ addr ⨾ sb ⨾ ⦗W⦘.

(* Atomic-ordered-before *)
Definition aob :=
  rmw ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗Q⦘.

(* Barrier-ordered-before *)
Definition bob :=
    sb ⨾ ⦗F^sy⦘ ⨾ sb
  ∪ ⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ ⨾ sb
  ∪ ⦗Q⦘ ⨾ sb
  ∪ sb ⨾ ⦗L⦘ ⨾ coi^?
  ∪ ⦗L⦘ ⨾ sb ⨾ ⦗A⦘.

(******************************************************************************)
(** ** Consistency *)
(******************************************************************************)

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type ATOM : rmw_atomicity G.
Implicit Type SC_PER_LOC : sc_per_loc G.

Definition ArmConsistent :=
  ⟪ WF : Wf G ⟫ /\
  ⟪ COMP : complete G ⟫ /\
  ⟪ SC_PER_LOC: sc_per_loc G ⟫ /\
  ⟪ POWER_ATOMICITY : rmw_atomicity G ⟫ /\
  ⟪ ACYC : acyclic (obs ∪ dob ∪ aob ∪ bob) ⟫.

Implicit Type CON : ArmConsistent.


(******************************************************************************)
(** ** Additional derived relations to simlify our proofs *)
(******************************************************************************)

Definition obs' := rfe ∪ co ∪ fr.

Definition bob' :=
    bob ∪ ⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ 
        ∪ sb ⨾ ⦗F^sy⦘ 
        ∪ ⦗F^ld ∪₁ F^sy⦘ ⨾ sb
        ∪ ⦗L⦘ ⨾ coi.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_obsE WF: obs ≡ ⦗E⦘ ⨾ obs ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold obs.
rewrite (wf_rfeE WF) at 1.
rewrite (wf_coeE WF) at 1.
rewrite (wf_freE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_dobE WF: dob ≡ ⦗E⦘ ⨾ dob ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold dob.
rewrite (wf_addrE WF) at 1 2 3.
rewrite (wf_dataE WF) at 1 2.
rewrite (wf_rfiE WF) at 1.
rewrite (wf_ctrlE WF) at 1 2.
rewrite (wf_coiE WF) at 1.
rewrite wf_sbE at 1 2.
basic_solver 42.
Qed.

Lemma wf_aobE WF: aob ≡ ⦗E⦘ ⨾ aob ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold aob.
rewrite (wf_rmwE WF) at 1.
rewrite (wf_rfiE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_bobE WF: bob ≡ ⦗E⦘ ⨾ bob ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold bob.
rewrite wf_sbE at 1 2 3 4 5 6 7.
rewrite (wf_coiE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_obs'E WF: obs' ≡ ⦗E⦘ ⨾ obs' ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold obs'.
rewrite (wf_rfeE WF) at 1.
rewrite (wf_coE WF) at 1.
rewrite (wf_frE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_bob'E WF: bob' ≡ ⦗E⦘ ⨾ bob' ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold bob'.
rewrite (wf_bobE WF) at 1.
rewrite (wf_coiE WF) at 1.
rewrite wf_sbE at 1 2 3.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_obsD WF: obs ≡ ⦗RW⦘ ⨾ obs ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold obs.
rewrite (wf_rfeD WF) at 1.
rewrite (wf_coeD WF) at 1.
rewrite (wf_freD WF) at 1.
basic_solver 42.
Qed.

Lemma wf_obs'D WF: obs' ≡ ⦗RW⦘ ⨾ obs' ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold obs'.
rewrite (wf_rfeD WF) at 1.
rewrite (wf_coD WF) at 1.
rewrite (wf_frD WF) at 1.
basic_solver 42.
Qed.

Lemma wf_dobD WF: dob ≡ dob ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold dob.
rewrite (dom_r (wf_addrD WF)) at 1.
rewrite (dom_r (wf_dataD WF)) at 1.
rewrite (dom_r (wf_rfiD WF)) at 1.
rewrite (dom_r (wf_coiD WF)) at 1.
basic_solver 42.
Qed.

Lemma wf_aobD WF: aob ≡ aob ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold aob.
rewrite (dom_r (wf_rmwD WF)) at 1.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Properties of consistent executions  *)
(******************************************************************************)

Lemma obs_in_eco : obs ⊆ eco.
Proof using. unfold Arm.obs. rewrite rfe_in_eco, fre_in_eco, coe_in_eco. eauto with hahn. Qed.

Lemma eco_in_sb_obs_sb WF :  eco ⊆ sb^? ⨾ obs^? ⨾ obs^? ⨾ sb^?.
Proof using.
  rewrite (eco_alt WF).
  rewrite cr_union_r, seq_union_l.
  rewrite coi_union_coe, fri_union_fre, rfi_union_rfe.
  rewrite coi_in_sb, fri_in_sb, rfi_in_sb.
  arewrite (coe ⊆ obs).
  arewrite (fre ⊆ obs).
  arewrite (rfe ⊆ obs).
  rewrite !seq_union_l, !seq_union_r.
  basic_solver 20.
Qed.

Lemma detour_in_obs : detour ⊆ obs⁺ .
Proof using.
  unfold Execution.detour.
  arewrite (coe ⊆ obs).
  arewrite (rfe ⊆ obs).
  rewrite <- ct_ct.
  rewrite <- ct_step.
  basic_solver 12.
Qed.

Lemma obs_coi WF SC_PER_LOC : obs ⨾ coi ⊆ obs.
Proof using.
  unfold obs at 1.
  rewrite !seq_union_l.
  rewrite coe_coi; auto.
  rewrite fre_coi; auto.
  rewrite (dom_r (wf_rfeD WF)).
  rewrite (dom_l (wf_coiD WF)).
  unfold obs. type_solver 10.
Qed.

Lemma obs_fri WF SC_PER_LOC : obs ⨾ fri ⊆ obs.
Proof using.
  unfold obs at 1.
  rewrite !seq_union_l.
  rewrite (dom_r (wf_coeD WF)).
  rewrite (dom_r (wf_freD WF)).
  rewrite rfe_fri; auto.
  rewrite (dom_l (wf_friD WF)).
  unfold obs. type_solver 10.
Qed.

Lemma bob_coi WF : bob ⨾ coi ⊆ bob.
Proof using.
  unfold bob; relsf; rewrite ?seqA.
  arewrite (coi ⊆ sb) at 1.
  arewrite (coi ⊆ sb) at 1.
  arewrite (coi ⊆ sb) at 1.
  rewrite (@sb_sb G).
  arewrite_false (⦗A⦘ ⨾ coi).
  { rewrite (wf_coiD WF). type_solver. }
  unionL; eauto with hahn.
  2: basic_solver.
  arewrite (coi^? ⨾ coi ⊆ coi^?); eauto with hahn.
  generalize (coi_trans WF). basic_solver 21.
Qed.

Lemma bob'_coi WF : bob' ⨾ coi ⊆ bob'.
Proof using.
  unfold bob'.
  rewrite !seq_union_l, !seqA.
  rewrite (bob_coi WF). 
  arewrite (coi ⨾ coi ⊆ coi).
  { apply transitiveI. by apply coi_trans. }
  apply union_mori; [|done].
  do 3 (arewrite (coi ⊆ sb) at 1).
  rewrite (@sb_sb G).
  apply union_mori; [|done].
  transitivity bob.
  2: by eauto with hahn.
  rewrite unionA. apply inclusion_union_l; [done|].
  unfold bob. eauto with hahn.
Qed.

Lemma bob_fri WF : bob ⨾ fri ⊆ bob ⨾ bob^?.
Proof using.
  unfold bob at 1; relsf; rewrite ?seqA.
  arewrite (fri ⊆ sb) at 1.
  arewrite (fri ⊆ sb) at 1.
  arewrite (fri ⊆ sb) at 1.
  rewrite (@sb_sb G).
  assert (bob ⊆ bob ⨾ bob^?) as AA by basic_solver.
  unionL.
  1-3: by rewrite <- AA; unfold bob; eauto with hahn.
  { rewrite (wf_coiD WF), (wf_friD WF). type_solver. }
  arewrite (⦗A⦘ ⊆ ⦗A⦘ ⨾ ⦗Q⦘) by mode_solver.
  arewrite (fri ⊆ sb).
  arewrite (⦗Q⦘ ⨾ sb ⊆ bob).
  arewrite (⦗L⦘ ⨾ sb ⨾ ⦗A⦘ ⊆ bob).
  basic_solver.
Qed.

Lemma bob'_fri WF : bob' ⨾ fri ⊆ bob' ⨾ bob^?.
Proof using.
  unfold bob' at 1.
  rewrite !seq_union_l, !seqA.
  rewrite (bob_fri WF).
  arewrite (fri ⊆ sb) at 1.
  arewrite (fri ⊆ sb) at 1.
  arewrite (fri ⊆ sb) at 1.
  rewrite (@sb_sb G).
  assert (bob ⊆ bob' ⨾ bob^?) as AA.
  { unfold bob'. basic_solver 10. }
  unionL; eauto with hahn.
  4: { rewrite (wf_coiD WF), (wf_friD WF). type_solver. }
  1-2: by rewrite <- AA; unfold bob; eauto with hahn.
  transitivity bob'.
  2: basic_solver.
  unfold bob'. eauto with hahn.
Qed.

Lemma dob_alt WF :
 dob ≡
   addr
 ∪ (addr ∪ data) ⨾ rfi
 ∪ (ctrl ∪ data) ⨾ ⦗W⦘ ⨾ coi^?
 ∪ addr ⨾ sb ⨾ ⦗W⦘.
Proof using.
unfold dob.
rewrite (dom_r (wf_dataD WF)) at 1 3.
basic_solver 42.
Qed.

Lemma dob_coi WF : dob ⨾ coi ⊆ dob.
Proof using.
  rewrite dob_alt; ins.
  generalize (addr ∪ data), (ctrl ∪ data), (ctrl ∪ addr ⨾ sb). ins. relsf.
  unionL; rewrite ?seqA.
  { rewrite (dom_r (wf_coiD WF)) at 1.
    ie_unfolder. basic_solver 12. }
  { arewrite (rfi ⊆ rf) at 1.
    arewrite (coi ⊆ co) at 1.
    rewrite (rf_co WF). basic_solver. }
  { rewrite crE; relsf.
    generalize (@sb_trans G).
    generalize (co_trans WF).
    ie_unfolder. basic_solver 13. }
  rewrite (dom_r (wf_coiD WF)) at 1.
  generalize (@sb_trans G).
  ie_unfolder. basic_solver 42.
Qed.

Lemma dob_fri WF : dob ⨾ fri ⊆ dob.
Proof using.
  rewrite dob_alt; ins.
  set (ad := addr ∪ data); set (cd := ctrl ∪ data); set (ca := ctrl ∪ addr ⨾ sb).
  ins; relsf.
  unionL; rewrite ?seqA.
  + rewrite (dom_r (wf_friD WF)) at 1.
    arewrite (fri ⊆ sb); basic_solver 12.
  + ie_unfolder.
    rewrite (seq_ii (rf_fr WF)).
    unfold ad at 1; relsf; unionL.
    -- rewrite (dom_r (wf_coD WF)) at 1.
       basic_solver 21.
    -- rewrite (dom_l (wf_coD WF)) at 1.
       unfold cd.
       basic_solver 21.
  + rewrite (dom_r (wf_coiD WF)) at 1.
    rewrite (dom_l (wf_friD WF)) at 1.
    type_solver.
  + rewrite (dom_l (wf_friD WF)) at 1.
    type_solver.
Qed.

Lemma aob_fri WF : aob ⨾ fri ⊆ aob ⨾ bob^?.
Proof using.
  unfold aob; relsf; rewrite ?seqA; unionL.
  { rewrite (dom_l (wf_friD WF)) at 1.
    rewrite (dom_r (wf_rmwD WF)) at 1.
    type_solver. }
  unionR right.
  rewrite fri_in_sb.
  unfold bob.
  basic_solver 20.
Qed.

Lemma deps_in_ctrl_or_dob WF:
    deps ⊆ ctrl ∪ dob.
Proof using.
    rewrite (dob_alt WF).
unfold Execution.deps;
rewrite (dom_r (wf_dataD WF)) at 1.
basic_solver 12.
Qed.

Lemma dob_in_sb WF: dob ⊆ sb.
Proof using.
unfold dob.
rewrite (addr_in_sb WF).
rewrite (data_in_sb WF).
rewrite (ctrl_in_sb WF).
arewrite (coi ⊆ sb).
arewrite (rfi ⊆ sb).
generalize (@sb_trans G).
basic_solver 21.
Qed.

Lemma aob_in_sb WF: aob ⊆ sb.
Proof using.
unfold aob.
rewrite (rmw_in_sb WF).
arewrite (rfi ⊆ sb).
basic_solver 21.
Qed.

Lemma bob_in_sb WF: bob ⊆ sb.
Proof using.
unfold bob.
arewrite (coi ⊆ sb).
generalize (@sb_trans G).
basic_solver 21.
Qed.

Lemma bob'_in_sb WF: bob' ⊆ sb.
Proof using.
unfold bob'.
rewrite coi_in_sb.
rewrite (bob_in_sb WF).
basic_solver 21.
Qed.

Lemma external_alt_bob' WF CON : acyclic (obs ∪ dob ∪ aob ∪ bob').
Proof using.
  assert (SC_PER_LOC : sc_per_loc G) by apply CON.
  unfold bob'; rewrite <- !unionA in *.
  assert (APO: acyclic sb).
  { apply trans_irr_acyclic; eauto using sb_trans, sb_irr. }
  assert (X: acyclic (obs ∪ dob ∪ aob ∪ bob ∪ (⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ ∪ sb ⨾ ⦗F^sy⦘))).
  { apply acyclic_absorb; eauto.
    left; relsf; rewrite !seqA. 
    transitivity (⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘⨾ sb ∪ sb ⨾ ⦗F^sy⦘ ⨾ sb).
    2: by transitivity bob; eauto with hahn; unionL; eauto with hahn.
    rewrite (dob_in_sb WF), (aob_in_sb WF), (bob_in_sb WF).
    unionL; eauto with hahn.
    1-2: rewrite (dom_l (wf_obsD WF)); type_solver.
    split; auto.
    { apply CON. }
    apply inclusion_acyclic with (r':=sb); basic_solver. }
  assert (X' : acyclic (obs ∪ dob ∪ aob ∪ bob ∪ ⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ ∪ sb ⨾ ⦗F^sy⦘ ∪ ⦗F^ld ∪₁ F^sy⦘ ⨾ sb)).
  { rewrite <- unionA in X.
    rewrite unionC; apply acyclic_absorb; eauto.
    right; transitivity bob; relsf; rewrite ?seqA; unionL.
    { rewrite (dom_r (wf_obsD WF)); type_solver. }
    { rewrite (wf_dobD WF); type_solver. }
    { rewrite (wf_aobD WF); type_solver. }
    2-4: arewrite_id ⦗F^ld ∪₁ F^sy⦘; rels; eauto 6 with hahn.
    unfold bob; relsf; rewrite ?seqA.
    arewrite_false (⦗L⦘ ⨾ coi^? ⨾ ⦗F^ld ∪₁ F^sy⦘).
    rewrite (dom_r (wf_coiD WF)); type_solver.
    arewrite_false (⦗A⦘ ⨾ ⦗F^ld ∪₁ F^sy⦘).
    { type_solver. }
    arewrite_id ⦗F^ld ∪₁ F^sy⦘.
    rels.
    rewrite (@sb_sb G).
    basic_solver 21. }
  rewrite unionC.
  apply acyclic_absorb; eauto.
  2: { split; auto.
       arewrite_id ⦗L⦘. rewrite seq_id_l. rewrite coi_in_sb.
       apply sb_acyclic. }
  right.
  rewrite !unionA.
  arewrite ((dob ∪ (aob ∪ (bob ∪ (⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ ∪ (sb ⨾ ⦗F^sy⦘ ∪ ⦗F^ld ∪₁ F^sy⦘ ⨾ sb)))))
              ⊆ sb) at 1.
  { rewrite (aob_in_sb WF) at 1.
    rewrite (bob_in_sb WF) at 1.
    rewrite (dob_in_sb WF) at 1.
    clear. basic_solver. }
  rewrite seq_union_l.
  unionL.
  2: { arewrite (sb ⨾ ⦗L⦘ ⨾ coi ⊆ bob).
       2: by eauto with hahn.
       unfold bob. basic_solver 10. }
  transitivity obs.
  2: by eauto with hahn.
  arewrite_id ⦗L⦘. rewrite seq_id_l.
  apply obs_coi; auto.
Qed.

Lemma external_alt_fri CON :
    acyclic (fri ∪ obs ∪ dob ∪ aob ∪ bob').
Proof using.
  cdes CON.
  assert (AC' : acyclic (obs ∪ dob ∪ aob ∪ bob')) by (by apply external_alt_bob').
  rewrite !(unionA fri).
  rewrite ct_step with (r := obs ∪ dob ∪ aob ∪ bob').
  apply acyclic_absorb; ins.
  2: { unfold acyclic. rewrite ct_of_ct.
       split; auto.
       apply acyclic_disj.
       rewrite (wf_friD WF).
       type_solver 10. }
  right. rewrite ct_end at 1. rewrite !seqA.
  rewrite !seq_union_l.
  rewrite obs_fri; auto. 
  rewrite dob_fri; auto. 
  rewrite aob_fri; auto. 
  rewrite bob'_fri; auto. 
  arewrite (obs ∪ dob ∪ aob ⨾ bob^? ∪ bob' ⨾ bob^? ⊆
            (obs ∪ dob ∪ aob ∪ bob')⁺).
  2: by apply rt_ct.
  rewrite unionA. rewrite <- seq_union_l.
  apply inclusion_union_l.
  { rewrite <- ct_step. eauto with hahn. }
  rewrite ct_begin.
  arewrite (aob ∪ bob' ⊆ obs ∪ dob ∪ aob ∪ bob').
  hahn_frame.
  apply inclusion_r_rt.
  unfold bob'. eauto with hahn.
Qed.

Lemma external_alt CON :
    acyclic (obs' ∪ dob ∪ aob ∪ bob').
Proof using.
  cdes CON.
  assert (RMW_COI : rmw ⨾ coi ⊆ fri).
  { rewrite rmw_in_fri; auto. apply fri_coi; auto. }
  assert (AC' : acyclic (fri ∪ obs ∪ dob ∪ aob ∪ bob')) by (by apply external_alt_fri).
  arewrite (obs' ⊆ coi ∪ fri ∪ obs).
  { unfold obs', obs. rewrite coi_union_coe, fri_union_fre.
    unionL; eauto with hahn. }
  rewrite !(unionA coi). 
  apply acyclic_absorb; ins.
  2: { arewrite (coi ⊆ co). split; auto.
       apply (co_acyclic WF). }
  right. rewrite !seq_union_l.
  rewrite fri_coi; auto. 
  rewrite obs_coi; auto. 
  rewrite dob_coi; auto. 
  rewrite bob'_coi; auto. 
  arewrite (aob ⨾ coi ⊆ fri).
  { unfold aob at 1. rewrite seq_union_l. unionL; auto.
    rewrite (dom_l (wf_coiD WF)) at 1.
    type_solver 42. }
  do 4 (apply inclusion_union_l; [|by eauto with hahn]).
  eauto with hahn.
Qed.

End Arm.
