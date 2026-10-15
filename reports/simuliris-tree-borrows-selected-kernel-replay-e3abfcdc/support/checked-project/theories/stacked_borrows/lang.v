(** This file has been adapted from the Stacked Borrows development, available at
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From simuliris.simulation Require Export language.
From iris.algebra Require Import ofe.

From simuliris.stacked_borrows Require Export expr_semantics bor_semantics parallel_subst.



Module bor_lang.

(** COMBINED SEMANTICS -------------------------------------------------------*)

Record state := mkState {
  (* Heap of scalars *)
  shp : mem;
  (* Stacked borrows for the heap *)
  sst : stacks;
  (* Set of active call ids *)
  scs : call_id_set;
  (* Counter for pointer tag generation *)
  snp : ptr_id;
  (* Counter for call id generation *)
  snc : call_id;
}.

Record config := mkConfig {
  (* Static global function table *)
  cfn : prog;
  (* Shared state *)
  cst : state;
}.

Implicit Type (σ: state).

(** BASIC LANGUAGE PROPERTIES ------------------------------------------------*)
(** Closed expressions *)

Lemma is_closed_subst X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  revert e X. fix FIX 1. intros e; destruct e=> X /=; rewrite ?bool_decide_spec ?andb_True=> He ?;
    repeat case_bool_decide; simplify_eq/=; f_equal;
    try by intuition eauto with set_solver.
  - case He=> _. clear He. rename select (list expr) into el.
    induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
Qed.

Lemma is_closed_nil_subst e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply is_closed_subst with []; set_solver. Qed.

Lemma is_closed_of_result X v : is_closed X (of_result v).
Proof. by destruct v as [[]|]. Qed.

Lemma to_of_result v : to_result (of_result v) = Some v.
Proof. by destruct v as [[]|]. Qed.
Lemma of_to_result e v : to_result e = Some v → of_result v = e.
Proof. destruct e=>//=; intros; by simplify_eq. Qed.
Global Instance of_result_inj : Inj (=) (=) of_result.
Proof. by intros ?? Hv; apply (inj Some); rewrite -2!to_of_result Hv /=. Qed.
Lemma is_closed_to_result X e v : to_result e = Some v → is_closed X e.
Proof. intros <-%of_to_result. apply is_closed_of_result. Qed.

Lemma list_Forall_to_of_result vl :
  Forall (λ ei, is_Some (to_result ei)) (of_result <$> vl).
Proof.
  apply Forall_forall. move => e /list_elem_of_fmap [? [-> ?]].
  rewrite to_of_result. by eexists.
Qed.

Lemma of_result_list_expr (vl: list value) :
  (of_result <$> (ValR <$> vl)) = Val <$> vl.
Proof. induction vl as [|v vl IH]; [done|]. by rewrite 3!fmap_cons IH. Qed.

(** Equality and other typeclass stuff *)

Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable'
    (λ o, match o with AddOp => 0 | SubOp => 1 | LeOp => 2 |
                  LtOp => 3 | EqOp => 4 | OffsetOp => 5 end)
    (λ x, match x with 0 => AddOp | 1 => SubOp | 2 => LeOp |
                  3 => LtOp | 4 => EqOp | _ => OffsetOp end) _); by intros [].
Qed.

Global Instance scalar_eq_dec : EqDecision scalar.
Proof. solve_decision. Defined.
Global Instance scalar_countable : Countable scalar.
Proof.
  refine (inj_countable
          (λ v, match v with
              | ScPoison => inl $ inl (inl ())
              | ScPtr l bor => inl $ inl (inr (l,bor))
              | ScInt n => inl $ inr (inl n)
              | ScFnPtr n => inl $ inr (inr n)
              | ScCallId c => inr c
              end)
          (λ s, match s with
              | inl (inl (inl ())) => Some ScPoison
              | inl (inl (inr (l,bor))) => Some $ ScPtr l bor
              | inl (inr (inl n)) => Some $ ScInt n
              | inl (inr (inr n)) => Some $ ScFnPtr n
              | inr c => Some $ ScCallId c
              end) _); by intros [].
Qed.

Global Instance retag_kind_eq_dec : EqDecision retag_kind.
Proof. solve_decision. Defined.
Global Instance retag_kind_countable : Countable retag_kind.
Proof.
  refine (inj_countable
          (λ k, match k with
              | FnEntry => inl $ inl ()
              | TwoPhase => inl $ inr ()
              | RawRt => inr $ inl ()
              | Default => inr $ inr ()
              end)
          (λ s, match s with
              | inl (inl _) => Some $ FnEntry
              | inl (inr _) => Some TwoPhase
              | inr (inl _) => Some RawRt
              | inr (inr _) => Some Default
              end) _); by intros [].
Qed.

Fixpoint expr_beq (e : expr) (e' : expr) : bool :=
  let fix expr_list_beq el el' :=
    match el, el' with
    | [], [] => true
    | eh::eq, eh'::eq' => expr_beq eh eh' && expr_list_beq eq eq'
    | _, _ => false
    end
  in
  match e, e' with
  | Val v, Val v' => bool_decide (v = v')
  | Var x, Var x' => bool_decide (x = x')
  | Case e el, Case e' el'
    (* | App e el, App e' el' *) => expr_beq e e' && expr_list_beq el el'
  (* | Rec f xl e, Rec f' xl' e' =>
      bool_decide (f = f') && bool_decide (xl = xl') && expr_beq e e' *)
  | Call e1 e2, Call e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
  | BinOp op e1 e2, BinOp op' e1' e2' =>
      bool_decide (op = op') && expr_beq e1 e1' && expr_beq e2 e2'
  | Place l bor T , Place l' bor' T' =>
      bool_decide (l = l') && bool_decide (bor = bor') && bool_decide (T = T')
  | Deref e T, Deref e' T' =>
      bool_decide (T = T') && expr_beq e e'
  | Retag e1 e2 pk T kind, Retag e1' e2' pk' T' kind' =>
     bool_decide (pk = pk') && bool_decide (T = T') &&
     bool_decide (kind = kind') && expr_beq e1 e1' && expr_beq e2 e2'
  | Copy e, Copy e' | Ref e, Ref e'
  (* | AtomRead e, AtomRead e' *) => expr_beq e e'
  | Let x e1 e2, Let x' e1' e2' =>
    bool_decide (x = x') && expr_beq e1 e1' && expr_beq e2 e2'
  | Proj e1 e2, Proj e1' e2' | Conc e1 e2, Conc e1' e2'
    | Write e1 e2, Write e1' e2' (* | AtomWrite e1 e2, AtomWrite e1' e2' *) =>
      expr_beq e1 e1' && expr_beq e2 e2'
  (* | Field e path, Field e' path' => expr_beq e e' && bool_decide (path = path') *)
  (* | CAS e0 e1 e2, CAS e0' e1' e2' =>
      expr_beq e0 e0' && expr_beq e1 e1' && expr_beq e2 e2' *)
  | Fork e, Fork e' => expr_beq e e'
  | Alloc T, Alloc T' => bool_decide (T = T')
  | Free e, Free e' | EndCall e, EndCall e' => expr_beq e e'
  | InitCall, InitCall => true
  | While e1 e2, While e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
  (* | SysCall id, SysCall id' => bool_decide (id = id') *)
  | _, _ => false
  end.

Lemma expr_beq_correct (e1 e2 : expr) : expr_beq e1 e2 ↔ e1 = e2.
Proof.
  revert e1 e2; fix FIX 1; intros e1 e2;
    destruct e1 as [| |? el1| | | | | | | | | | (* | *) | | | | |? el1 | | ],
             e2 as [| |? el2| | | | | | | | | | (* | *) | | | | |? el2 | | ];
    simpl; try done;
    rewrite ?andb_True ?bool_decide_spec ?FIX;
    try (split; intro; [destruct_and?|split_and?]; congruence).
  - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; intros el2; destruct el2; try done.
      specialize (FIX el1h). naive_solver. }
    clear FIX. naive_solver.
Qed.

Global Instance expr_dec_eq : EqDecision expr.
Proof.
  refine (λ e1 e2, cast_if (decide (expr_beq e1 e2))); by rewrite -expr_beq_correct.
Defined.
Global Instance expr_countable : Countable expr.
Proof.
  refine (inj_countable'
    (fix go e := match e with
      | Var x => GenNode 0 [GenLeaf $ inl $ inl $ inl $ inl x]
      | Val v => GenNode 1 [GenLeaf $ inl $ inl $ inl $ inr v]
      (* | Rec f xl e => GenNode 2 [GenLeaf $ inl $ inl $ inr $ inl f;
                                 GenLeaf $ inl $ inl $ inr $ inr xl; go e]
      | App e el => GenNode 3 (go e :: (go <$> el)) *)
      | Call e1 e2 => GenNode 2 [go e1; go e2]
      | InitCall => GenNode 3 []
      | EndCall e => GenNode 4 [go e]
      | BinOp op e1 e2 => GenNode 5 [GenLeaf $ inl $ inl $ inr $ inl op;
                                     go e1; go e2]
      | Proj e1 e2 => GenNode 6 [go e1; go e2]
      | Conc e1 e2 => GenNode 7 [go e1; go e2]
      | Place l tag T => GenNode 8 [GenLeaf $ inl $ inl $ inr $ inr l;
                                    GenLeaf $ inl $ inr $ inl $ inl tag;
                                    GenLeaf $ inl $ inr $ inl $ inr T]
      | Copy e => GenNode 9 [go e]
      | Write e1 e2 => GenNode 10 [go e1; go e2]
      | Free e => GenNode 11 [go e]
      | Alloc T => GenNode 12 [GenLeaf $ inl $ inr $ inr $ inl T]
      | Deref e T => GenNode 13 [GenLeaf $ inl $ inr $ inr $ inr T; go e]
      | Ref e => GenNode 14 [go e]
      (* | Field e path => GenNode 15 [GenLeaf $ inr $ inl $ inl (* $ inl *) path; go e] *)
      | Retag e1 e2 pk T kind =>
          GenNode 15 [GenLeaf $ inr $ inl $ inl pk;
                      GenLeaf $ inr $ inl $ inr T;
                      GenLeaf $ inr $ inr $ inl kind; go e1; go e2]
      | Let x e1 e2 => GenNode 16 [GenLeaf$ inr $ inr $ inr x; go e1; go e2]
      | Case e el => GenNode 17 (go e :: (go <$> el))
      | Fork e => GenNode 23 [go e]
      | While e1 e2 => GenNode 24 [go e1; go e2]
    (*| SysCall id => GenNode 24 [GenLeaf $ inr $ inr id] *)
     end)
    (fix go s := match s with
     | GenNode 0 [GenLeaf (inl (inl (inl (inl x))))] => Var x
     | GenNode 1 [GenLeaf (inl (inl (inl (inr v))))] => Val v
     | GenNode 2 [e1; e2] => Call (go e1) (go e2)
     | GenNode 3 [] => InitCall
     | GenNode 4 [e] => EndCall (go e)
     (* | GenNode 2 [GenLeaf (inl (inl (inr (inl f))));
                  GenLeaf (inl (inl (inr (inr xl)))); e] => Rec f xl (go e)
     | GenNode 3 (e :: el) => App (go e) (go <$> el) *)
     | GenNode 5 [GenLeaf (inl (inl (inr (inl op)))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 6 [e1; e2] => Proj (go e1) (go e2)
     | GenNode 7 [e1; e2] => Conc (go e1) (go e2)
     | GenNode 8 [GenLeaf (inl (inl (inr (inr l))));
                  GenLeaf (inl (inr (inl (inl tag))));
                  GenLeaf (inl (inr (inl (inr T))))] => Place l tag T
     | GenNode 9 [e] => Copy (go e)
     | GenNode 10 [e1; e2] => Write (go e1) (go e2)
     | GenNode 11 [e] => Free (go e)
     | GenNode 12 [GenLeaf (inl (inr (inr (inl T))))] => Alloc T
     | GenNode 13 [GenLeaf (inl (inr (inr (inr T)))); e] => Deref (go e) T
     | GenNode 14 [e] => Ref (go e)
     (* | GenNode 15 [GenLeaf (inr (inl (inl (*  (inl *) path(* ) *)))); e] => Field (go e) path *)
     | GenNode 15 [GenLeaf (inr (inl (inl pk)));
                   GenLeaf (inr (inl (inr T)));
                   GenLeaf (inr (inr (inl kind))); e1; e2] =>
        Retag (go e1) (go e2) pk T kind
     | GenNode 16 [GenLeaf (inr (inr (inr x))); e1; e2] => Let x (go e1) (go e2)
     | GenNode 17 (e :: el) => Case (go e) (go <$> el)
     | GenNode 23 [e] => Fork (go e)
     | GenNode 24 [e1; e2] => While (go e1) (go e2)
    (* | GenNode 24 [GenLeaf (inr (inr id))] => SysCall id *)
     | _ => (#[☠])%E
     end) _).
  fix FIX 1. intros []; f_equal=>//; rename select (list expr) into el; revert el; clear -FIX.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
Qed.

Global Instance result_dec_eq : EqDecision result.
Proof.
  refine (λ v1 v2, cast_if (decide (of_result v1 = of_result v2))); abstract naive_solver.
Defined.
Global Instance result_countable : Countable result.
Proof.
  refine (inj_countable
    (λ v, match v with
          | ValR v => inl v
          | PlaceR l bor T => inr (l, bor, T)
          end)
    (λ x, match x with
          | inl v => Some $ ValR $ v
          | inr (l, bor, T) => Some $ PlaceR l bor T
          end) _).
  by intros [].
Qed.

Global Instance scalar_inhabited : Inhabited scalar := populate ScPoison.
Global Instance expr_inhabited : Inhabited expr := populate (#[☠])%E.
Global Instance result_inhabited : Inhabited result := populate (ValR [☠]%S).
Global Instance state_Inhabited : Inhabited state.
Proof. do 2!econstructor; exact: inhabitant. Qed.

Canonical Structure locO {SI : sidx} := leibnizO loc.
Canonical Structure scalarO {SI : sidx} := leibnizO scalar.
Canonical Structure resultO {SI : sidx} := leibnizO result.
Canonical Structure exprO {SI : sidx} := leibnizO expr.
Canonical Structure stateO {SI : sidx} := leibnizO state.

(** Basic properties about the language *)


Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.
Global Instance fill_inj K : Inj (=) (=) (fill K).
Proof. induction K; intros ???; by simplify_eq/=. Qed.

Lemma fill_item_result Ki e :
  is_Some (to_result (fill_item Ki e)) → is_Some (to_result e).
Proof. intros [r ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_result Ki e :
  to_result e = None → to_result (fill_item Ki e) = None.
Proof. intros EqN. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma list_expr_result_eq_inv rl1 rl2 e1 e2 el1 el2 :
  to_result e1 = None → to_result e2 = None →
  fmap of_result rl1 ++ e1 :: el1 = fmap of_result rl2 ++ e2 :: el2 →
  rl1 = rl2 ∧ el1 = el2.
Proof.
  revert rl2; induction rl1 as [|?? IH]; intros rl2; destruct rl2 as [|? rl2];
    intros H1 H2; inversion 1.
  - done.
  - subst. by rewrite to_of_result in H1.
  - subst. by rewrite to_of_result in H2.
  - destruct (IH rl2); auto. split; f_equal; auto. by apply (inj of_result).
Qed.

Lemma fill_item_no_result_inj Ki1 Ki2 e1 e2 :
  to_result e1 = None → to_result e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1 as [| | | | | | | | | | | | | | (* | *) | | | | ],
           Ki2 as [| | | | | | | | | | | | | | (* | *) | | | |];
  intros He1 He2 EQ; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_result (of_result _) = None |- _ => by rewrite to_of_result in H
    end; auto;
  destruct (list_expr_result_eq_inv vl1 vl2 e1 e2 el1 el2); auto; congruence.
Qed.

Lemma fill_result K e :
  is_Some (to_result (fill K e)) → is_Some (to_result e) ∧ K = [].
Proof.
  revert e. induction K as [|Ki K IH]; intros e; [done|].
  move => /= /IH [Eq ?]. subst. split.
  - by eapply fill_item_result.
  - destruct Eq. by destruct Ki.
Qed.
Lemma fill_no_result K e :
  to_result e = None → to_result (fill K e) = None.
Proof.
  destruct (to_result (fill K e)) eqn:H.
  - edestruct (fill_result) as [[v' ?] _]; [ eauto | congruence].
  - done.
Qed.

Section base_step.

Inductive base_step (P : prog) :
  expr → state → expr → state → list expr → Prop :=
  | HeadPureS σ e e' efs
      (ExprStep: pure_expr_step P σ.(shp) e e' efs)
    : base_step P e σ e' σ efs
  | HeadImpureS σ e e' ev h' α' cids' nxtp' nxtc' efs
      (ExprStep : mem_expr_step σ.(shp) e ev h' e' efs)
      (InstrStep: bor_step σ.(sst) σ.(scs) σ.(snp) σ.(snc)
                           ev α' cids' nxtp' nxtc')
    : base_step P e σ e' (mkState h' α' cids' nxtp' nxtc') efs.

Lemma result_base_stuck P e1 σ1 e2 σ2 efs :
  base_step P e1 σ1 e2 σ2 efs → to_result e1 = None.
Proof.
  destruct 1.
  - rename select (pure_expr_step _ _ _ _ _) into Hstep; inversion Hstep; naive_solver.
  - rename select (mem_expr_step _ _ _ _ _ _) into Hstep; inversion Hstep; naive_solver.
Qed.

Lemma base_ctx_step_result P Ki e σ1 e2 σ2 efs :
  base_step P (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_result e).
Proof.
  destruct Ki; inversion_clear 1;
    (rename select (pure_expr_step _ _ _ _ _) into Hstep ||
     rename select (mem_expr_step _ _ _ _ _ _) into Hstep);
    inversion_clear Hstep;
    simplify_option_eq; eauto using is_Some_to_value_result.
Qed.

Lemma base_step_fill_result P Ki K e σ1 e2 σ2 efs:
  base_step P (fill K (fill_item Ki e)) σ1 e2 σ2 efs → is_Some (to_result e).
Proof.
  revert e Ki.
  induction K as [ | Ki' K IH]; simpl; intros e Ki.
  - by intros ?%base_ctx_step_result.
  - intros H. eapply IH in H. by eapply fill_item_result.
Qed.

Lemma head_ectx_step_no_result P K e σ1 e2 σ2 efs:
  to_result e = None → base_step P (fill K e) σ1 e2 σ2 efs → K = empty_ectx.
Proof.
  intros Hnores H.
  destruct K as [ | Ki K]; first reflexivity.
  exfalso. apply base_step_fill_result in H.
  eapply is_Some_None; by rewrite <-Hnores.
Qed.

Definition of_class (m : mixin_expr_class result) : expr :=
  match m with
  | ExprVal r => of_result r
  | ExprCall f r => of_call f r
  end.
Definition to_class (e : expr) : option (mixin_expr_class result) :=
  match to_result e with
  | Some v => Some (ExprVal v)
  | None => option_map (λ '(fn, r), ExprCall fn r) (to_call e)
  end.

Lemma to_of_class m : to_class (of_class m) = Some m.
Proof.
  destruct m.
  - cbn. rewrite /to_class to_of_result; done.
  - cbn. rewrite to_of_result; done.
Qed.
Lemma of_to_class e m : to_class e = Some m → of_class m = e.
Proof.
  destruct m.
  + rewrite /to_class.
    destruct e; try discriminate 1; first by inversion 1.
    - cbn. destruct to_fname; cbn; last done. destruct to_result; cbn; done.
    - cbn. inversion 1; done.
  + destruct e; try discriminate 1. rewrite /to_class; simpl.
    match goal with |- context[to_fname ?e] => destruct e; simpl end.
    { rename select value into v.
      destruct v as [ | [] [ | ]]; simpl; try congruence.
      rename select expr into e2.
      destruct e2; try discriminate 1; cbn; by inversion 1.
    }
    all: congruence.
Qed.

Lemma to_class_result e r : to_class e = Some (ExprVal r) → to_result e = Some r.
Proof.
  destruct e; simpl; try discriminate 1.
  - by inversion 1.
  - match goal with |- context[Call ?e _] => destruct e end;
    rewrite /to_class; simpl.
    { rename select expr into e2.
      destruct to_fname; destruct e2; try discriminate 1. }
    all: discriminate 1.
  - by inversion 1.
Qed.
Lemma to_class_call e f r : to_class e = Some (ExprCall f r) → to_call e = Some (f, r).
Proof.
  destruct e; rewrite /to_class; simpl; try discriminate 1.
  destruct to_fname; simpl; try discriminate 1.
  match goal with |- context[to_result ?e] => destruct e end;
  simpl; try discriminate 1; by inversion 1.
Qed.

Lemma to_result_class e r : to_result e = Some r → to_class e = Some (ExprVal r).
Proof. destruct e; cbn; try discriminate 1; by inversion 1. Qed.
Lemma to_call_class e f r : to_call e = Some (f, r) → to_class e = Some (ExprCall f r).
Proof.
  destruct e; rewrite /to_call /to_class; simpl; try discriminate 1.
  destruct to_fname; try discriminate 1.
  destruct to_result; try discriminate 1; by inversion 1.
Qed.

Lemma fill_eq P σ1 σ2 e1 e1' e2 K K' efs:
  to_result e1 = None →
  base_step P e1' σ1 e2 σ2 efs →
  fill K e1 = fill K' e1' →
  ∃ K'', K' = ectx_compose K K''.
Proof.
  intros Hres Hstep; revert K'.
  induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
  destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
  { rewrite fill_app in Hstep. apply base_ctx_step_result in Hstep.
    apply fill_result in Hstep as [Hstep%not_eq_None_Some _]; done. }
  rewrite !fill_app /= in Hfill.
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_result_inj, Hfill; first by apply fill_no_result.
    apply fill_no_result. eauto using result_base_stuck. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto.
  exists K''. unfold ectx_compose. cbn. by rewrite assoc.
Qed.

Lemma bor_lang_mixin :
  LanguageMixin of_class to_class empty_ectx ectx_compose fill
    subst_map free_vars apply_func base_step.
Proof.
  constructor.
  - apply to_of_class.
  - apply of_to_class.
  - intros p v ???? H%result_base_stuck. rewrite to_of_result in H. congruence.
  - intros p f v ????. split.
    + cbn. inversion 1; subst;
      (rename select (pure_expr_step _ _ _ _ _) into Hstep ||
       rename select (mem_expr_step _ _ _ _ _ _) into Hstep);
      inversion_clear Hstep; subst.
      rewrite ->to_of_result in *.
      simplify_eq.
      eexists _. eauto.
    + intros (fn & ? & -> & -> & ->). cbn.
      constructor; constructor; [done | rewrite to_of_result; eauto].
  - eapply subst_map_empty.
  - eapply subst_map_subst_map.
  - eapply subst_map_free_vars.
  - eapply free_vars_subst_map.
  - done.
  - intros ???. by rewrite -fill_app.
  - apply fill_inj.
  - intros K e H.
    destruct to_class as [[]|] eqn:Heq; last by apply is_Some_None in H.
    + right. apply to_class_result in Heq.
      edestruct (fill_result K e) as [[v' Hval] _]; first by eauto.
      exists v'. by apply to_result_class.
    + destruct (to_result e) eqn:Hres. { right; eauto using to_result_class. }
      left. apply to_class_call in Heq. clear H.
      assert (K ≠ empty_ectx → to_call (fill K e) = None) as H.
      { clear Heq. destruct K as [ | Ki K]; first by destruct 1. intros _.
        revert Hres. revert Ki e.
        induction K as [ | ?? IH]; cbn; intros Ki e Hres.
        - destruct Ki; cbn; try reflexivity.
          { destruct e; [ | reflexivity..].
            rename select value into v.
            destruct v as [ |[] ]; done. }
          rewrite Hres. by destruct to_fname.
        - cbn in IH. by apply IH, fill_item_no_result.
      }
      rewrite Heq in H. destruct K; first done.
      rename select string into fn_name.
      rename select result into arg.
      enough (Some (fn_name, arg) = None) by congruence. by apply H.
  - intros p K K' e1' e1_redex σ1 e2 σ2 efs H. destruct to_class as [ [] | ] eqn:Heq; first done.
    + intros _ Hstep.
      eapply fill_eq; [ | apply Hstep | apply H].
      rewrite <-(of_to_class _ _ Heq). reflexivity.
    + intros _ Hstep. eapply fill_eq; [ | apply Hstep | apply H].
      destruct to_result eqn:Hres; last done. apply to_result_class in Hres; congruence.
  - intros ?????? H.
    match goal with |- context[to_class ?e] => destruct (to_result e) eqn:Heq end.
    { right. eexists. by apply to_result_class. }
    left. by eapply head_ectx_step_no_result.
Qed.
End base_step.

End bor_lang.

(** Language *)
Canonical Structure bor_lang := Language (bor_lang.bor_lang_mixin).
Export bor_lang.

