From iris Require Import bi.bi.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls lifting.
From simuliris.simulang Require Import lang notation tactics class_instances proofmode.

Import bi.

(** This file defines a simple value relation for encoding sums using
  pairs and shows a simple example program. This example is not fully
  worked out (the relation does not have support for heap operations),
  and there is no reflexivity or adequacy theorem proven.*)


Section fix_bi.
Context `{sheapGS Σ}.
Inductive val_rel_pure : val → val → Prop :=
  | val_rel_lit l : val_rel_pure (LitV l) (LitV l)
  | val_rel_injL v1 v2 : val_rel_pure v1 v2 → val_rel_pure ((#1, v1)%V) (InjLV v2)
  | val_rel_injR v1 v2 : val_rel_pure v1 v2 → val_rel_pure ((#2, v1)%V) (InjRV v2)
  | val_rel_pair v1 v2 v1' v2' :
      val_rel_pure v1 v1' →
      val_rel_pure v2 v2' →
      val_rel_pure ((v1, v2)%V) ((v1', v2')%V).
Local Hint Constructors val_rel_pure : core.
Definition val_rel v1 v2 : iProp Σ := (⌜val_rel_pure v1 v2⌝)%I.
Program Instance : sheapInv Σ := {|
  sheap_inv _ _ _ := ⌜True⌝%I;
  sheap_ext_rel _ := val_rel;
 |}.
Next Obligation. auto. Qed.
Global Instance : sheapInvStateIndependent.
Proof. done. Qed.

(* Sums are encoded as injL x -> (1, x); injR x -> (2, x); the tag encodes the constructor.  *)

Definition inj1_enc := (λ: "x", (#1, "x"))%E.
Definition inj2_enc := (λ: "x", (#2, "x"))%E.

Definition diverge := (λ: "x", Call "diverge" "x")%E.

(** the value relation determining which values can be passed to a function *)

Definition mul2_source : func :=
  λ: "x",
    match: "x" with
      InjL "x" => "x" * #2
    | InjR "x" => "x" + #2
    end.

Definition mul2_target : func :=
  λ: "x",
    if: Fst "x" = #1 then (Snd "x") * #2
      else if: Fst "x" = #2
        then (Snd "x") + #2
        else Call "diverge" #().

Definition source_prog : prog :=
  {[ "inj1_enc" := inj1_enc; "diverge" := diverge; "mul2" := mul2_source ]}.
Definition target_prog : prog :=
  {[ "diverge" := diverge; "mul2" := mul2_target]}.

Lemma mul2_sim π:
  ⊢ ∀ v_t v_s, val_rel v_t v_s -∗
    apply_func mul2_target v_t ⪯{π} apply_func mul2_source v_s {{ λ v_t' v_s', val_rel v_t' v_s' }}.
Proof.
  iIntros (?? Hval). rewrite /mul2_target /mul2_source.
  sim_pures.
  (* generate additional conditions on the shape of the source expression *)
  iApply sim_safe_implies.
  iIntros "%Ha"; destruct Ha as (v' & [-> | ->]).
  - inversion_clear Hval; subst.
    sim_pures.
    iApply sim_safe_implies. iIntros "%Ha"; destruct Ha as [(n & ->) _].
    rename select (val_rel_pure _ _) into Hval.
    inversion Hval; subst.
    by sim_pures; sim_val.
  - inversion_clear Hval; subst.
    sim_pures.
    iApply sim_safe_implies. iIntros "%Ha"; destruct Ha as [(n & ->) _].
    rename select (val_rel_pure _ _) into Hval.
    inversion Hval; subst.
    by sim_pures; sim_val.
Qed.

Definition source_client := (λ: "x", Call (f#"mul2") (InjL "x"))%E.
Definition target_client := (λ: "x", Call (f#"mul2") (Call (f#"inj1_enc") "x"))%E.

Lemma client_sim (n : Z) π :
  "target_client" @t target_client -∗
  "source_client" @s source_client -∗
  "inj1_enc" @t inj1_enc -∗
  Call (f#"target_client") #n ⪯{π} Call (f#"source_client") #n {{ λ v_t v_s, val_rel v_t v_s }}.
Proof.
  iIntros "Htarget Hsource Hinj1_t".
  target_call. target_call. source_call. sim_pures.
  iApply sim_call; [done..| eauto | ].
  iIntros (??) "?". iApply lift_post_val. done.
Qed.
End fix_bi.
