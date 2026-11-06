(******************************************************************************)
(** * Definition of execution graph events and labels *)
(******************************************************************************)

Require Import List.
From hahn Require Import Hahn.
From PromisingLib Require Import Basic Loc.
From hahnExt Require Import HahnExt.

Set Implicit Arguments.

Definition thread_id := Basic.Ident.t.
Definition tid_init := Coq.Numbers.BinNums.xH.

Definition location := Loc.t.
Definition value := nat.

(******************************************************************************)
(** ** Execution graph events  *)
(******************************************************************************)

Inductive actid := 
  | InitEvent (l : location)
  | ThreadEvent (thread : thread_id) (index : nat).

Definition tid a := 
  match a with
    | InitEvent l => tid_init 
    | ThreadEvent i _ => i
  end.

Definition is_tid i a : Prop := tid a = i.

Definition index a := 
  match a with
    | InitEvent l => 0
    | ThreadEvent _ n => n
  end.

Definition is_init a := 
  match a with
    | InitEvent _ => true
    | ThreadEvent _ _ => false
  end.

Lemma tid_set_dec thread :
  (fun x => tid x = thread) ∪₁ (fun x => tid x <> thread) ≡₁ (fun x => True).
Proof using. unfolder; split; ins; desf; tauto. Qed.

(******************************************************************************)
(** ** Same tid restriction *)
(******************************************************************************)

Definition same_tid := (fun x y => tid x = tid y).

Lemma restr_eq_rel_same_tid r :  restr_eq_rel tid r  ≡ r ∩ same_tid.
Proof using. unfold same_tid; basic_solver. Qed.

Lemma loceq_same_tid (r: relation actid) (H: funeq tid r):
 r ⊆ r ∩ same_tid.
Proof using.
unfold same_tid; basic_solver.
Qed.

Lemma same_tid_loceq (r: relation actid) (H: r ⊆ r ∩ same_tid):
 funeq tid r.
Proof using.
unfold same_tid; unfolder; firstorder.
Qed.

(******************************************************************************)
(** ** Decidable equality *)
(******************************************************************************)

Lemma eq_dec_actid :
  forall x y : actid, {x = y} + {x <> y}.
Proof using.
repeat decide equality.
Qed.

(******************************************************************************)
(** ** Labels  *)
(******************************************************************************)

Inductive mode := 
  | Opln
  | Orlx
  | Oacq
  | Orel
  | Oacqrel
  | Osc.

Definition mode_le lhs rhs :=
  match lhs, rhs with
    | Opln, _ => true
    | _, Opln => false
    | Orlx, _ => true
    | _, Orlx => false
    | Oacq, Oacq
    | Oacq, Oacqrel
    | Orel, Orel
    | Orel, Oacqrel
    | Oacqrel, Oacqrel
    | _, Osc => true
    | _ , _ => false
  end.

Inductive x_mode := 
  | Xpln
  | Xacq.

Inductive label := 
  | Aload  (ex:bool) (o:mode) (l:location) (v:value)
  | Astore (s:x_mode) (o:mode) (l:location) (v:value)
  | Afence (o:mode).


(*
   The meaning of the modes in each case:
   (currently Opln is redundant, easy to remove in the future)

                  IMM        POWER      ARM 
   =================================================
   Aload Opln       rlx       ld         ldr
   Aload Orlx       rlx       ld         ldr
   Aload Oacq       acq       ld         ldapr (?)
   Aload Orel       rlx       ld         ldr
   Aload Oacqrel    acq       ld         ldapr (?)
   Aload Osc        acq       ld         ldapr (?)

   Astore Opln      rlx       st         str
   Astore Orlx      rlx       st         str
   Astore Oacq      rlx       st         str
   Astore Orel      rel       st         stlr
   Astore Oacqrel   rel       st         stlr
   Astore Osc       rel       st         stlr

   Afence Opln      no-op     no-op      no-op
   Afence Orlx      no-op     isync      F-ld
   Afence Oacq      acq       lwsync     F-ld
   Afence Orel      rel       lwsync     F-sy
   Afence Oacqrel   acq-rel   lwsync     F-sy
   Afence Osc       sc        sync       F-sy

 *)

Section Labels.

Variable A : Type.
Variable lab : A -> label.

Definition loc a :=
  match lab a with
  | Aload _ _ l _
  | Astore _ _ l _ => Some l
  | _ => None
  end.

Definition val a :=
  match lab a with
  | Aload  _ _ _ v
  | Astore _ _ _ v => Some v
  | _ => None
  end.

Definition mod a :=
  match lab a with
  | Aload  _ o _ _
  | Astore _ o _ _
  | Afence o => o
  end.

Definition xmod a :=
  match lab a with
  | Astore x _ _ _ => Some x
  | _ => None
  end.

Definition is_r a := 
  match lab a with
  | Aload  _ _ _ _ => true
  | _ => false
  end.

Definition is_w a := 
  match lab a with
  | Astore _ _ _ _ => true
  | _ => false
  end.

Definition is_f a := 
  match lab a with
  | Afence _ => true
  | _ => false
  end.

Definition is_only_pln a : bool :=
  match mod a with
  | Opln => true
  | _ => false
  end.

Definition is_only_rlx a : bool :=
  match mod a with
  | Orlx => true
  | _ => false
  end.

Definition is_rlx a : bool := mode_le Orlx (mod a).
Definition is_acq a : bool := mode_le Oacq (mod a).
Definition is_rel a : bool := mode_le Orel (mod a).
Definition is_acqrel a : bool := mode_le Oacqrel (mod a).
Definition is_sc a : bool :=
  match mod a with
  | Osc => true
  | _ => false
  end.

Definition is_ra a : bool := is_acq a || is_rel a.

Lemma lab_rwf a : is_r a \/ is_w a \/ is_f a.
Proof using. unfold is_r, is_w, is_f; destruct (lab a); auto. Qed.

Definition is_xacq a := 
  match xmod a with
  | Some Xacq => true
  | _ => false
  end.

Definition R_ex a :=
  match lab a with
  | Aload r _ _ _ => r
  | _ => false
  end.

Lemma R_ex_in_R : R_ex ⊆₁ is_r.
Proof using.
unfold R_ex, is_r; basic_solver.
Qed.

Definition rmwmod a :=
  match lab a with
  | Aload r _ _ _ => Some r
  | _ => None
  end.


(******************************************************************************)
(** ** Same location restriction *)
(******************************************************************************)

Definition same_loc := (fun x y => loc x = loc y).

Lemma restr_eq_rel_same_loc r :  restr_eq_rel loc r  ≡ r ∩ same_loc.
Proof using. unfold same_loc; basic_solver. Qed.

Lemma loceq_same_loc (r: relation A) (H: funeq loc r):
 r ⊆ r ∩ same_loc.
Proof using.
unfold same_loc; basic_solver.
Qed.

Lemma same_loc_loceq (r: relation A) (H: r ⊆ r ∩ same_loc):
 funeq loc r.
Proof using.
unfold same_loc; unfolder; firstorder.
Qed.

Lemma same_loc_trans : transitive same_loc.
Proof using. unfold same_loc; red; ins. by rewrite H. Qed.

Lemma same_loc_sym : symmetric same_loc.
Proof using. unfold same_loc; red; ins. Qed.

(******************************************************************************)
(** ** Values and locations getters  *)
(******************************************************************************)

Lemma is_w_val x (WX : is_w x) : exists v, val x = Some v.
Proof using. unfold is_w, val in *; desf. eexists; eauto. Qed.

Lemma is_w_loc x (WX : is_w x) : exists l, loc x = Some l.
Proof using. unfold is_w, loc in *; desf. eexists; eauto. Qed.

Lemma is_r_val x (WX : is_r x) : exists v, val x = Some v.
Proof using. unfold is_r, val in *; desf. eexists; eauto. Qed.

Lemma is_r_loc x (WX : is_r x) : exists l, loc x = Some l.
Proof using. unfold is_r, loc in *; desf. eexists; eauto. Qed.

Lemma is_f_val x (FX : is_f x) : val x = None.
Proof using. unfold is_f, val in *; desf. Qed.

Lemma is_f_loc x  (FX: is_f x): loc x = None.
Proof using. unfold is_f, loc in *; desf. Qed. 

End Labels.

(******************************************************************************)
(** ** Identical labeling up to value  *)
(******************************************************************************)

Definition same_mod {A} (lab : A -> label) : relation A :=
  (fun x y => mod lab x = mod lab y).

Definition same_val {A} (lab : A -> label) : relation A :=
  (fun x y => val lab x = val lab y).

Definition same_label_u2v label1 label2 :=
  match label1, label2 with
  | Aload  r1 o1 l1 _, Aload  r2 o2 l2 _ => r1 = r2 /\ o1 = o2 /\ l1 = l2
  | Astore s1 o1 l1 _, Astore s2 o2 l2 _ => s1 = s2 /\ o1 = o2 /\ l1 = l2
  | Afence o1, Afence o2 => o1 = o2
  | _,_ => False
  end.

Section SameFunsSet.

Variable A : Type.
Variable s : A -> Prop.
Variable lab1 lab2 : A -> label.

Definition same_lab_u2v_dom  := 
  forall e (EE : s e),
    same_label_u2v (lab1 e) (lab2 e).

#[local]
Hint Unfold eq_dom loc mod xmod is_r is_w is_f is_acq is_rel is_rlx is_acqrel R_ex
     is_only_pln is_only_rlx is_sc is_ra is_xacq
     same_lab_u2v_dom same_label_u2v :
  same_lab_unfoldDb.

Ltac same_lab_set_solver_f SAME :=
  repeat (autounfold with same_lab_unfoldDb in *);
          intros a HH; specialize (SAME a HH);
          desf; desf.

Lemma same_lab_u2v_dom_loc (SAME: same_lab_u2v_dom) :
  eq_dom s (loc lab1) (loc lab2).
Proof using. same_lab_set_solver_f SAME. Qed.

Lemma same_lab_u2v_dom_mod (SAME: same_lab_u2v_dom) :
  eq_dom s (mod lab1) (mod lab2).
Proof using. same_lab_set_solver_f SAME. Qed.

Lemma same_lab_u2v_dom_xmod (SAME: same_lab_u2v_dom) :
  eq_dom s (xmod lab1) (xmod lab2).
Proof using. same_lab_set_solver_f SAME. Qed.

Ltac same_lab_set_solver_s SAME :=
  repeat (autounfold with same_lab_unfoldDb in *); unfolder;
          split; intros a HH; desf; split; auto; specialize (SAME a HH); desf.

Lemma same_lab_u2v_dom_is_r (SAME: same_lab_u2v_dom) :
  s ∩₁ is_r lab1 ≡₁ s ∩₁ is_r lab2.
Proof using. same_lab_set_solver_s SAME. Qed.

Lemma same_lab_u2v_dom_is_w (SAME: same_lab_u2v_dom) :
  s ∩₁ is_w lab1 ≡₁ s ∩₁ is_w lab2.
Proof using. same_lab_set_solver_s SAME. Qed.

Lemma same_lab_u2v_dom_is_f (SAME: same_lab_u2v_dom) :
  s ∩₁ is_f lab1 ≡₁ s ∩₁ is_f lab2.
Proof using. same_lab_set_solver_s SAME. Qed.

Lemma same_lab_u2v_dom_R_ex (SAME: same_lab_u2v_dom) :
  s ∩₁ R_ex lab1 ≡₁ s ∩₁ R_ex lab2.
Proof using. same_lab_set_solver_s SAME; desf. Qed.

Lemma same_lab_u2v_dom_is_only_pln (SAME: same_lab_u2v_dom) :
  s ∩₁ is_only_pln lab1 ≡₁ s ∩₁ is_only_pln lab2.
Proof using. same_lab_set_solver_s SAME; desf. Qed.

Lemma same_lab_u2v_dom_is_only_rlx (SAME: same_lab_u2v_dom) :
  s ∩₁ is_only_rlx lab1 ≡₁ s ∩₁ is_only_rlx lab2.
Proof using. same_lab_set_solver_s SAME; desf. Qed.

Lemma same_lab_u2v_dom_is_rlx (SAME: same_lab_u2v_dom) :
  s ∩₁ is_rlx lab1 ≡₁ s ∩₁ is_rlx lab2.
Proof using. same_lab_set_solver_s SAME; desf. Qed.

Lemma same_lab_u2v_dom_is_acq (SAME: same_lab_u2v_dom) :
  s ∩₁ is_acq lab1 ≡₁ s ∩₁ is_acq lab2.
Proof using. same_lab_set_solver_s SAME; desf. Qed.

Lemma same_lab_u2v_dom_is_rel (SAME: same_lab_u2v_dom) :
  s ∩₁ is_rel lab1 ≡₁ s ∩₁ is_rel lab2.
Proof using. same_lab_set_solver_s SAME; desf. Qed.

Lemma same_lab_u2v_dom_is_acqrel (SAME: same_lab_u2v_dom) :
  s ∩₁ is_acqrel lab1 ≡₁ s ∩₁ is_acqrel lab2.
Proof using. same_lab_set_solver_s SAME; desf. Qed.

Lemma same_lab_u2v_dom_is_sc (SAME: same_lab_u2v_dom) :
  s ∩₁ is_sc lab1 ≡₁ s ∩₁ is_sc lab2.
Proof using. same_lab_set_solver_s SAME; desf. Qed.

Lemma same_lab_u2v_dom_is_ra (SAME: same_lab_u2v_dom) :
  s ∩₁ is_ra lab1 ≡₁ s ∩₁ is_ra lab2.
Proof using. same_lab_set_solver_s SAME; desf. all: by rewrite Bool.orb_true_r. Qed.

Lemma same_lab_u2v_dom_is_xacq (SAME: same_lab_u2v_dom) :
  s ∩₁ is_xacq lab1 ≡₁ s ∩₁ is_xacq lab2.
Proof using. same_lab_set_solver_s SAME; desf. Qed.

Lemma same_lab_u2v_dom_same_loc (SAME: same_lab_u2v_dom) :
  restr_rel s (same_loc lab1) ≡ restr_rel s (same_loc lab2).
Proof using.
  unfolder. split.
  all: ins; desf; splits; auto.
  all: unfold same_loc, loc, same_lab_u2v_dom, same_label_u2v in *.
  all: set (SAMEY := SAME); specialize (SAMEY y H1).
  all: specialize (SAME x H0); desf; desf.
Qed.

End SameFunsSet.

Lemma same_label_u2v_val {A} (lab lab' : A -> label) x
      (U2V : same_label_u2v (lab x) (lab' x))
      (VAL : val lab x = val lab' x) :
  lab x = lab' x.
Proof using. unfold same_label_u2v, val in *. desf; desf. Qed.

Section SameFuns.

Variable A : Type.
Variable lab1 lab2 : A -> label.

Definition same_lab_u2v :=
  same_lab_u2v_dom (fun _ => True) lab1 lab2.

Lemma same_lab_u2v_loc (SAME: same_lab_u2v) :
  loc lab1 = loc lab2.
Proof using. apply eq_dom_full_eq. by apply same_lab_u2v_dom_loc. Qed.

Lemma same_lab_u2v_mod (SAME: same_lab_u2v) :
  mod lab1 = mod lab2.
Proof using. apply eq_dom_full_eq. by apply same_lab_u2v_dom_mod. Qed.

Lemma same_lab_u2v_xmod (SAME: same_lab_u2v) :
  xmod lab1 = xmod lab2.
Proof using. apply eq_dom_full_eq. by apply same_lab_u2v_dom_xmod. Qed.

Lemma same_lab_u2v_is_r (SAME: same_lab_u2v) :
  is_r lab1 ≡₁ is_r lab2.
Proof using. generalize (same_lab_u2v_dom_is_r SAME). relsf. Qed.

Lemma same_lab_u2v_is_w (SAME: same_lab_u2v) :
  is_w lab1 ≡₁ is_w lab2.
Proof using. generalize (same_lab_u2v_dom_is_w SAME). relsf. Qed.

Lemma same_lab_u2v_is_f (SAME: same_lab_u2v) :
  is_f lab1 ≡₁ is_f lab2.
Proof using. generalize (same_lab_u2v_dom_is_f SAME). relsf. Qed.

Lemma same_lab_u2v_R_ex (SAME: same_lab_u2v) :
  R_ex lab1 ≡₁ R_ex lab2.
Proof using. generalize (same_lab_u2v_dom_R_ex SAME). relsf. Qed.

Lemma same_lab_u2v_is_only_pln (SAME: same_lab_u2v) :
  is_only_pln lab1 ≡₁ is_only_pln lab2.
Proof using. generalize (same_lab_u2v_dom_is_only_pln SAME). relsf. Qed.

Lemma same_lab_u2v_is_only_rlx (SAME: same_lab_u2v) :
  is_only_rlx lab1 ≡₁ is_only_rlx lab2.
Proof using. generalize (same_lab_u2v_dom_is_only_rlx SAME). relsf. Qed.

Lemma same_lab_u2v_is_rlx (SAME: same_lab_u2v) :
  is_rlx lab1 ≡₁ is_rlx lab2.
Proof using. generalize (same_lab_u2v_dom_is_rlx SAME). relsf. Qed.

Lemma same_lab_u2v_is_acq (SAME: same_lab_u2v) :
  is_acq lab1 ≡₁ is_acq lab2.
Proof using. generalize (same_lab_u2v_dom_is_acq SAME). relsf. Qed.

Lemma same_lab_u2v_is_rel (SAME: same_lab_u2v) :
  is_rel lab1 ≡₁ is_rel lab2.
Proof using. generalize (same_lab_u2v_dom_is_rel SAME). relsf. Qed.

Lemma same_lab_u2v_is_acqrel (SAME: same_lab_u2v) :
  is_acqrel lab1 ≡₁ is_acqrel lab2.
Proof using. generalize (same_lab_u2v_dom_is_acqrel SAME). relsf. Qed.

Lemma same_lab_u2v_is_sc (SAME: same_lab_u2v) :
  is_sc lab1 ≡₁ is_sc lab2.
Proof using. generalize (same_lab_u2v_dom_is_sc SAME). relsf. Qed.

Lemma same_lab_u2v_is_ra (SAME: same_lab_u2v) :
  is_ra lab1 ≡₁ is_ra lab2.
Proof using. generalize (same_lab_u2v_dom_is_ra SAME). relsf. Qed.

Lemma same_lab_u2v_is_xacq (SAME: same_lab_u2v) :
  is_xacq lab1 ≡₁ is_xacq lab2.
Proof using. generalize (same_lab_u2v_dom_is_xacq SAME). relsf. Qed.

Lemma same_lab_u2v_same_loc (SAME: same_lab_u2v) :
  same_loc lab1 ≡ same_loc lab2.
Proof using. generalize (same_lab_u2v_dom_same_loc SAME). by rewrite !restr_full. Qed.
End SameFuns.

Section SameFuns2.

Lemma same_lab_u2v_comm {A} (lab1 lab2 : A -> label)
      (S1 : same_lab_u2v lab1 lab2) :
  same_lab_u2v lab2 lab1.
Proof using.
  unfold same_lab_u2v, same_lab_u2v_dom. ins.
  specialize (S1 e EE).
  unfold same_label_u2v in *.
  desf; desf.
Qed.

Lemma same_lab_u2v_follows_set {A} s (lab1 lab2 : A -> label)
      (S1 : same_lab_u2v lab1 lab2) :
  same_lab_u2v_dom s lab1 lab2.
Proof using. unfold same_lab_u2v, same_lab_u2v_dom in *. ins. by apply S1. Qed.

Lemma same_lab_u2v_dom_inclusion {A} s s' (lab lab' : A -> label)
      (SS : s' ⊆₁ s)
      (S1 : same_lab_u2v_dom s lab lab') :
  same_lab_u2v_dom s' lab lab'.
Proof using. red. ins. apply S1. by apply SS. Qed.

Lemma same_label_u2v_trans lbl1 lbl2 lbl3
      (S1 : same_label_u2v lbl1 lbl2)
      (S2 : same_label_u2v lbl2 lbl3) :
  same_label_u2v lbl1 lbl3.
Proof using. unfold same_label_u2v in *. desf; desf. Qed.

Lemma same_label_u2v_comm lbl1 lbl2
      (S1 : same_label_u2v lbl1 lbl2) :
  same_label_u2v lbl2 lbl1.
Proof using. unfold same_label_u2v in *. desf; desf. Qed.

Lemma same_lab_u2v_dom_trans {A} (s : A -> Prop) lab1 lab2 lab3
      (S1 : same_lab_u2v_dom s lab1 lab2)
      (S2 : same_lab_u2v_dom s lab2 lab3) :
  same_lab_u2v_dom s lab1 lab3.
Proof using.
  red. ins.
  specialize (S1 e EE).
  specialize (S2 e EE).
  eapply same_label_u2v_trans; eauto.
Qed.

Lemma same_lab_u2v_dom_comm {A} (s : A -> Prop) lab1 lab2
      (S2 : same_lab_u2v_dom s lab1 lab2) :
  same_lab_u2v_dom s lab2 lab1.
Proof using.
  red. ins. specialize (S2 e EE).
    by apply same_label_u2v_comm.
Qed.

Lemma same_lab_u2v_dom_same_mod {A} (lab lab' : A -> label) (s : A -> Prop)
      (SAME: same_lab_u2v_dom s lab lab') :
  restr_rel s (same_mod lab) ≡ restr_rel s (same_mod lab').
Proof using.
  unfolder. split.
  all: ins; desf; splits; auto.
  all: unfold same_mod, mod, same_lab_u2v_dom, same_label_u2v in *.
  all: set (SAMEY := SAME); specialize (SAMEY y H1).
  all: specialize (SAME x H0); desf; desf.
Qed.

End SameFuns2.

(******************************************************************************)
(** ** Sequenced-Before *)
(******************************************************************************)

Require Import Lia.

Definition ext_sb a b := 
  match a, b with 
    | _, InitEvent _ => False
    | InitEvent _, ThreadEvent _ _ => True
    | ThreadEvent t i, ThreadEvent t' i' => t = t' /\ i < i' 
   end.

Lemma ext_sb_trans : transitive ext_sb.
Proof using.
unfold ext_sb; red; ins.
destruct x,y,z; ins; desf; splits; eauto.
by rewrite H2.
Qed.

Lemma ext_sb_irr : irreflexive ext_sb.
Proof using.
unfold ext_sb; red; ins.
destruct x; firstorder. lia.
Qed.

Lemma ext_sb_to_non_init : ext_sb ⊆ ext_sb ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
unfold is_init, ext_sb; basic_solver.
Qed.

Lemma ext_sb_semi_total_l x y z 
  (N: ~ is_init x) (NEQ: index y <> index z) (XY: ext_sb x y) (XZ: ext_sb x z): 
  ext_sb y z \/ ext_sb z y.
Proof using.
unfold ext_sb in *.
destruct x,y,z; ins; desf.
cut(index1 < index2 \/ index2 < index1).
tauto.
lia.
Qed.

Lemma ext_sb_semi_total_r x y z 
  (NEQ: index y <> index z) (XY: ext_sb y x) (XZ: ext_sb z x): 
  ext_sb y z \/ ext_sb z y.
Proof using.
unfold ext_sb in *.
destruct x,y,z; ins; desf; eauto.
cut(index1 < index2 \/ index2 < index1).
tauto.
lia.
Qed.

Lemma ext_sb_tid_init x y (SB : ext_sb x y): tid x = tid y \/ is_init x.
Proof using.
unfold ext_sb in *; desf; ins; desf; eauto.
Qed.

Lemma ext_sb_tid_init': ext_sb ⊆ ext_sb ∩ same_tid ∪ ⦗is_init⦘ ⨾ ext_sb.
Proof using.
generalize ext_sb_tid_init; firstorder.
Qed.

Lemma tid_ext_sb: same_tid ⊆ ext_sb^? ∪ ext_sb^{-1} ∪ (is_init × is_init).
Proof using.
unfold ext_sb, same_tid, tid, is_init, cross_rel; unfolder.
ins; destruct x, y; desf; eauto.
cut(index0 < index1 \/ index1 < index0 \/ index0 = index1).
by ins; desf; eauto.
lia.
Qed.

Lemma tid_n_init_ext_sb: same_tid ⨾ ⦗set_compl is_init⦘ ⊆ ext_sb^? ∪ ext_sb^{-1}.
Proof using.
rewrite tid_ext_sb at 1.
unfold cross_rel.
basic_solver 12.
Qed.

(******************************************************************************)
(** ** is_init properties *)
(******************************************************************************)

Lemma is_init_tid : 
  is_init ⊆₁ fun x => tid x = tid_init. 
Proof using. unfolder. unfold is_init. ins. desf. Qed.

Lemma initninit_in_ext_sb : is_init × (set_compl is_init) ⊆ ext_sb.
Proof using. unfold ext_sb. basic_solver. Qed.

(******************************************************************************)
(** ** Tactics *)
(******************************************************************************)

#[global]
Hint Unfold set_union set_inter is_r is_w is_f R_ex : type_unfolderDb.
Tactic Notation "type_unfolder" :=  repeat autounfold with type_unfolderDb in *.

Tactic Notation "type_solver" int_or_var(index) := 
  type_unfolder; basic_solver index.

Tactic Notation "type_solver" :=  type_solver 4.

#[global]
Hint Unfold set_union set_inter is_r is_w is_f R_ex : mode_unfolderDb.
#[global]
Hint Unfold is_only_pln is_only_rlx is_rlx is_rel is_acq is_acqrel is_sc is_ra is_xacq : mode_unfolderDb.
Tactic Notation "mode_unfolder" :=  repeat autounfold with mode_unfolderDb in *.

Tactic Notation "mode_solver" int_or_var(index) := 
  mode_unfolder; basic_solver index.

Tactic Notation "mode_solver" :=  mode_solver 4.

Section EventsCountability. 
  Definition actid_alt: Type := location + thread_id * nat.

  Lemma actid_alt_isomorphic:
    isomorphism (fun e => match e with
                       | InitEvent l => inl l
                       | ThreadEvent t i => inr (t, i)
                       end)
                (fun ae => match ae with
                        | inl l => InitEvent l
                        | inr (t, i) => ThreadEvent t i
                        end).
  Proof using. split; ins; [destruct a | destruct b as [? | [? ?]]]; auto. Qed.   
  
  Lemma actid_countable: countable (@set_full actid).
  Proof using.
    eapply countable_isomorphic.
    { eapply isomorphism_sym, actid_alt_isomorphic. }
    apply countable_sum.
    { Set Printing All.
      unfold location, Loc.Loc.t. apply pos_countable. }
    apply countable_prod.
    { unfold thread_id, Basic.Ident.t. apply pos_countable. }
    apply nat_countable.
  Qed.

End EventsCountability.   

Section Props.
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Lemma ntid_tid_set_inter s thread :
  s ⊆₁ s ∩₁ NTid_ thread ∪₁ s ∩₁ Tid_ thread.
Proof using.
  ins.
  rewrite <- set_inter_union_r.
  unfolder. ins. splits; auto.
  destruct (classic (tid x = thread)); eauto.
Qed.
End Props.
