(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From Equations Require Import Equations.
From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.stacked_borrows Require Export lang_base notation type locations.
Local Open Scope Z_scope.

(*** EXPRESSION SEMANTICS --------------------------------------------------***)

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Val v => Val v
  | Call e1 e2 => Call (subst x es e1) (subst x es e2)
  | InitCall => InitCall
  | EndCall e => EndCall (subst x es e)
  | Place l tag T => Place l tag T
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | Proj e1 e2 => Proj (subst x es e1) (subst x es e2)
  | Conc e1 e2 => Conc (subst x es e1) (subst x es e2)
  | Copy e => Copy (subst x es e)
  | Write e1 e2 => Write (subst x es e1) (subst x es e2)
  | Alloc T => Alloc T
  | Free e => Free (subst x es e)
  (* | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2) *)
  (* | AtomWrite e1 e2 => AtomWrite (subst x es e1) (subst x es e2) *)
  (* | AtomRead e => AtomRead (subst x es e) *)
  | Deref e T => Deref (subst x es e) T
  | Ref e => Ref (subst x es e)
  (* | Field e path => Field (subst x es e) path *)
  | Retag e1 e2 pkind T kind => Retag (subst x es e1) (subst x es e2) pkind T kind
  | Let x1 e1 e2 =>
      Let x1 (subst x es e1)
                 (if bool_decide (BNamed x ≠ x1) then subst x es e2 else e2)
  | Case e el => Case (subst x es e) (fmap (subst x es) el)
  | Fork e => Fork (subst x es e) 
  | While e1 e2 => While (subst x es e1) (subst x es e2)
  (* | SysCall id => SysCall id *)
  end.

(* formal argument list substitution *)
Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

Fixpoint subst_l (xl : list binder) (esl : list expr) (e : expr) : option expr :=
  match xl, esl with
  | [], [] => Some e
  | x::xl, es::esl => subst_l xl esl (subst' x es e)
  | _, _ => None
  end.
Arguments subst_l _%_binder _ _%_E.

Lemma subst_l_is_Some xl el e :
  length xl = length el → is_Some (subst_l xl el e).
Proof.
  revert el e. induction xl as [|x xl IH] => el e.
  { destruct el; [by eexists|done]. }
  destruct el as [|e1 el]; [done|].
  rewrite /= /subst'. intros ?.
  eapply IH. congruence.
Qed.

Lemma subst_l_is_Some_length xl el e e' :
  subst_l xl el e = Some e' → length xl = length el.
Proof.
  revert e e' el. induction xl as [|x xl IH] => e e' el; [by destruct el|].
  destruct el as [|e1 el]; [done|].
  rewrite /= /subst'. intros Eq. f_equal.
  eapply IH. done.
Qed.

Lemma subst_l_nil_is_Some el e e' :
  subst_l [] el e = Some e' → e' = e.
Proof.
  intros Eq.
  have EqN: el = [].
  { apply nil_length_inv. by rewrite -(subst_l_is_Some_length _ _ _ _ Eq). }
  subst el. simpl in Eq. by simplify_eq.
Qed.

Lemma subst_result x e r :
  subst x e (of_result r) = of_result r.
Proof. destruct r; simpl; done. Qed.
Lemma subst'_result x e r : 
  subst' x e (of_result r) = of_result r.
Proof. destruct r, x; simpl; done. Qed.

(** Functions and function calls *)
Definition func : Type := string * expr.
Definition apply_func (fn : func) (r : result) := subst fn.1 r fn.2.

(** Evaluation contexts *)
Inductive ectx_item :=
| CallLEctx (r2 : result)
| CallREctx (e1 : expr)
| EndCallEctx
| BinOpREctx (op : bin_op) (e1 : expr)
| BinOpLEctx (op : bin_op) (r2 : result)
| ProjREctx (e1 : expr)
| ProjLEctx (r2 : result)
| ConcREctx (e1 : expr)
| ConcLEctx (r2 : result)
| CopyEctx
| WriteREctx (e1 : expr)
| WriteLEctx (r2 : result)
| FreeEctx
| DerefEctx (T : type)
| RefEctx
(* | FieldEctx (path : list nat) *)
| RetagREctx (e1 : expr) (pkind : pointer_kind) (T : type) (kind : retag_kind)
| RetagLEctx (r2 : result) (pkind : pointer_kind) (T : type) (kind : retag_kind)
| LetEctx (x : binder) (e2 : expr)
| CaseEctx (el : list expr)
(* Deliberately nothing for While and Fork; those reduce *before* the subexpressions reduce! *)
.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | CallLEctx r2 => Call e (of_result r2)
  | CallREctx e1 => Call e1 e
  | EndCallEctx => EndCall e
  | BinOpREctx op e1 => BinOp op e1 e
  | BinOpLEctx op r2 => BinOp op e (of_result r2)
  | ProjREctx e1 => Proj e1 e
  | ProjLEctx r2 => Proj e (of_result r2)
  | ConcREctx e1 => Conc e1 e
  | ConcLEctx r2 => Conc e (of_result r2)
  | CopyEctx => Copy e
  | WriteREctx e1 => Write e1 e
  | WriteLEctx r2 => Write e (of_result r2)
  | FreeEctx => Free e
  | DerefEctx T => Deref e T
  | RefEctx => Ref e
  (* | FieldEctx path => Field e path *)
  | RetagLEctx r2 pk T kind => Retag e (of_result r2) pk T kind
  | RetagREctx e1 pk T kind => Retag e1 e pk T kind
  | LetEctx x e2 => Let x e e2
  | CaseEctx el => Case e el
  end.

(** Building actual evaluation contexts out of ectx_items *)
Definition ectx := list ectx_item.
Definition empty_ectx : ectx := [].
Definition ectx_compose : ectx → ectx → ectx := flip (++).

Definition fill (K : ectx) (e : expr) : expr := foldl (flip fill_item) e K.

Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. apply foldl_app. Qed.

(** General contexts *)
Inductive ctx_item :=
  | LetLCtx (x : binder) (e2 : expr)
  | LetRCtx (x : binder) (e1 : expr)
  | CallLCtx (e2 : expr)
  | CallRCtx (e1 : expr)
  | EndCallCtx
  | BinOpLCtx (op : bin_op) (e2 : expr)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | ProjLCtx (e2 : expr)
  | ProjRCtx (e1 : expr)
  | ConcLCtx (e2 : expr)
  | ConcRCtx (e1 : expr)
  | CopyCtx
  | WriteLCtx (e2 : expr)
  | WriteRCtx (e1 : expr)
  | FreeCtx
  | DerefCtx (T : type)
  | RefCtx
  | RetagLCtx (e2 : expr) (pkind : pointer_kind) (T : type) (kind : retag_kind)
  | RetagRCtx (e1 : expr) (pkind : pointer_kind) (T : type) (kind : retag_kind)
  | CaseLCtx (el : list expr)
  | CaseRCtx (e : expr) (el1 el2 : list expr)
  | WhileLCtx (e1 : expr)
  | WhileRCtx (e0 : expr)
  | ForkCtx
  .

Definition fill_ctx_item (Ci : ctx_item) (e : expr) : expr :=
  match Ci with
  | LetLCtx x e2 => Let x e e2
  | LetRCtx x e1 => Let x e1 e
  | CallLCtx e2 => Call e e2
  | CallRCtx e1 => Call e1 e
  | EndCallCtx => EndCall e
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op e1 => BinOp op e1 e
  | ProjLCtx e2 => Proj e e2
  | ProjRCtx e1 => Proj e1 e
  | ConcLCtx e2 => Conc e e2
  | ConcRCtx e1 => Conc e1 e
  | CopyCtx => Copy e
  | WriteLCtx e2 => Write e e2
  | WriteRCtx e1 => Write e1 e
  | FreeCtx => Free e
  | DerefCtx T => Deref e T
  | RefCtx => Ref e
  | RetagLCtx e2 pk T k => Retag e e2 pk T k
  | RetagRCtx e1 pk T k => Retag e1 e pk T k
  | CaseLCtx el => Case e el
  | CaseRCtx e0 el1 el2 => Case e0 (el1 ++ e :: el2)
  | WhileLCtx e1 => While e e1
  | WhileRCtx e0 => While e0 e
  | ForkCtx => Fork e
  end.

Definition ctx := list ctx_item.
Definition fill_ctx (C : ctx) (e : expr) : expr :=
  foldl (flip fill_ctx_item) e C.

Lemma fill_ctx_app C1 C2 e :
  fill_ctx (C1 ++ C2) e = fill_ctx C2 (fill_ctx C1 e).
Proof. apply foldl_app. Qed.

(** Splitting an expression into information about the head expression and subexpressions. *)
Inductive expr_head :=
  | ValHead (v : value)
  | VarHead (x : string)
  | LetHead (x : binder)
  | CallHead
  | InitCallHead
  | EndCallHead
  | ProjHead
  | ConcHead
  | BinOpHead (op : bin_op)
  | PlaceHead (l : loc) (tg : tag) (T : type)
  | DerefHead (T : type)
  | RefHead
  | CopyHead
  | WriteHead
  | AllocHead (T : type)
  | FreeHead
  | RetagHead (pk : pointer_kind) (T : type) (kind : retag_kind)
  | CaseHead
  | ForkHead
  | WhileHead
.

Definition expr_split_head (e : expr) : (expr_head * list expr) :=
  match e with
  | Val v => (ValHead v, [])
  | Var x => (VarHead x, [])
  | Let x e1 e2 => (LetHead x, [e1; e2])
  | Call e1 e2 => (CallHead, [e1; e2])
  | BinOp op e1 e2 => (BinOpHead op, [e1; e2])
  | InitCall => (InitCallHead, [])
  | EndCall e => (EndCallHead, [e])
  | Proj e1 e2 => (ProjHead, [e1; e2])
  | Conc e1 e2 => (ConcHead, [e1; e2])
  | Place l tg T => (PlaceHead l tg T, [])
  | Deref e T => (DerefHead T, [e])
  | Ref e => (RefHead, [e])
  | Copy e => (CopyHead, [e])
  | Write e1 e2 => (WriteHead, [e1; e2])
  | Fork e => (ForkHead, [e])
  | Alloc T => (AllocHead T, [])
  | Free e => (FreeHead, [e])
  | Retag e1 e2 pk T k => (RetagHead pk T k, [e1; e2])
  | Case e el => (CaseHead, e :: el)
  | While e0 e1 => (WhileHead, [e0; e1])
  end.

Global Instance expr_split_head_inj : Inj (=) (=) expr_split_head.
Proof. move => [^ e1] [^ e2] => //=; move => [*]; by simplify_eq. Qed.

Definition ectxi_split_head (Ki : ectx_item) : (expr_head * list expr) :=
  match Ki with
  | LetEctx x e => (LetHead x, [e])
  | CallLEctx r => (CallHead, [of_result r])
  | CallREctx e => (CallHead, [e])
  | EndCallEctx => (EndCallHead, [])
  | BinOpLEctx op r => (BinOpHead op, [of_result r])
  | BinOpREctx op e => (BinOpHead op, [e])
  | ProjREctx e => (ProjHead, [e])
  | ProjLEctx r => (ProjHead, [of_result r])
  | ConcREctx e => (ConcHead, [e])
  | ConcLEctx r => (ConcHead, [of_result r])
  | CopyEctx => (CopyHead, [])
  | WriteLEctx r => (WriteHead, [of_result r])
  | WriteREctx e => (WriteHead, [e])
  | FreeEctx => (FreeHead, [])
  | DerefEctx T => (DerefHead T, [])
  | RefEctx => (RefHead, [])
  | RetagREctx e1 pk T k => (RetagHead pk T k, [e1])
  | RetagLEctx r2 pk T k => (RetagHead pk T k, [of_result r2])
  | CaseEctx el => (CaseHead, el)
  end.

Definition ctxi_split_head (Ci : ctx_item) : (expr_head * list expr) :=
  match Ci with
  | LetLCtx x e2 => (LetHead x, [e2])
  | LetRCtx x e1 => (LetHead x, [e1])
  | CallLCtx e2 => (CallHead, [e2])
  | CallRCtx e1 => (CallHead, [e1])
  | EndCallCtx => (EndCallHead, [])
  | BinOpLCtx op e2 => (BinOpHead op, [e2])
  | BinOpRCtx op e1 => (BinOpHead op, [e1])
  | ProjLCtx e2 => (ProjHead, [e2])
  | ProjRCtx e1 => (ProjHead, [e1])
  | ConcLCtx e2 => (ConcHead, [e2])
  | ConcRCtx e1 => (ConcHead, [e1])
  | CopyCtx => (CopyHead, [])
  | WriteLCtx e2 => (WriteHead, [e2])
  | WriteRCtx e1 => (WriteHead, [e1])
  | FreeCtx => (FreeHead, [])
  | DerefCtx T => (DerefHead T, [])
  | RefCtx => (RefHead, [])
  | RetagRCtx e1 pk T k => (RetagHead pk T k, [e1])
  | RetagLCtx e2 pk T k => (RetagHead pk T k, [e2])
  | CaseLCtx el => (CaseHead, el)
  | CaseRCtx e el1 el2 => (CaseHead, e :: el1 ++ el2)
  | WhileLCtx e1 => (WhileHead, [e1])
  | WhileRCtx e0 => (WhileHead, [e0])
  | ForkCtx => (ForkHead, [])
  end.

(** Global static function table *)
Definition prog := gmap fname func.

(** The stepping relation *)
(* Be careful to make sure that poison is always stuck when used for anything
   except for reading from or writing to memory! *)
Definition sc_of_bool (b : bool) : scalar :=
  ScInt $ Z.b2z b.

Coercion sc_of_bool : bool >-> scalar.
Coercion ScInt : Z >-> scalar.
Coercion ScFnPtr : fname >-> scalar.

Implicit Type (h : mem).

Fixpoint init_mem (l:loc) (n:nat) h : mem :=
  match n with
  | O => h
  | S n => <[l := ☠%S]>(init_mem (l +ₗ 1) n h)
  end.

Fixpoint free_mem (l:loc) (n:nat) h : mem :=
  match n with
  | O => h
  | S n => delete l (free_mem (l +ₗ 1) n h)
  end.

Inductive scalar_eq h : scalar → scalar → Prop :=
(* No refl case for poison *)
| IntRefl z : scalar_eq h (ScInt z) (ScInt z)
| LocRefl l tag1 tag2 : scalar_eq h (ScPtr l tag1) (ScPtr l tag2)
(* Comparing unallocated pointers can non-deterministically say they are equal
   even if they are not.  Given that our `free` actually makes addresses
   re-usable, this may not be strictly necessary, but it is the most
   conservative choice that avoids UB (and we cannot use UB as this operation is
   possible in safe Rust). *)
| LocUnallocL l1 l2 tag1 tag2 :
    h !! l1 = None →
    scalar_eq h (ScPtr l1 tag1) (ScPtr l2 tag2)
| LocUnallocR l1 l2 tag1 tag2 :
    h !! l2 = None →
    scalar_eq h (ScPtr l1 tag1) (ScPtr l2 tag2).

Inductive scalar_neq : scalar → scalar → Prop :=
| IntNeq z1 z2 :
    z1 ≠ z2 → scalar_neq (ScInt z1) (ScInt z2)
| LocNeq l1 l2 tag1 tag2 :
    l1 ≠ l2 → scalar_neq (ScPtr l1 tag1) (ScPtr l2 tag2)
| LocNeqNullR l tag :
    scalar_neq (ScPtr l tag) (ScInt 0)
| LocNeqNullL l tag :
    scalar_neq (ScInt 0) (ScPtr l tag).


Inductive bin_op_eval h : bin_op → scalar → scalar → scalar → Prop :=
| BinOpPlus z1 z2 :
    bin_op_eval h AddOp (ScInt z1) (ScInt z2) (ScInt (z1 + z2))
| BinOpMinus z1 z2 :
    bin_op_eval h SubOp (ScInt z1) (ScInt z2) (ScInt (z1 - z2))
| BinOpLe z1 z2 :
    bin_op_eval h LeOp (ScInt z1) (ScInt z2) (sc_of_bool $ bool_decide (z1 ≤ z2)%Z)
| BinOpLt z1 z2 :
    bin_op_eval h LtOp (ScInt z1) (ScInt z2) (sc_of_bool $ bool_decide (z1 < z2)%Z)
| BinOpEqTrue l1 l2 :
    scalar_eq h l1 l2 → bin_op_eval h EqOp l1 l2 (sc_of_bool true)
| BinOpEqFalse l1 l2 :
    scalar_neq l1 l2 → bin_op_eval h EqOp l1 l2 (sc_of_bool false)
| BinOpOffset l z tag :
    bin_op_eval h OffsetOp (ScPtr l tag) (ScInt z) (ScPtr (l +ₗ z) tag).

Global Hint Constructors scalar_eq : core.
Global Hint Constructors scalar_neq : core.
Global Hint Constructors bin_op_eval : core.
Global Instance scalar_eq_dec h sc1 sc2 : Decision (scalar_eq h sc1 sc2).
Proof.
  destruct sc1 as [|n1|l1| |], sc2 as [|n2|l2| |]; try by (right; intros H; inversion H).
  - destruct (decide (n1 = n2)) as [ -> | ];
    [left; eauto | right; intros H; inversion H; done].
  - destruct (decide (l1 = l2)) as [<- | Hneq]; first by left; eauto.
    destruct (h !! l1) eqn:Heq; last left; eauto.
    destruct (h !! l2) eqn:Heq'; last left; eauto.
    right. intros H; inversion H; subst; congruence.
Qed.
Global Instance scalar_neq_dec sc1 sc2 : Decision (scalar_neq sc1 sc2).
Proof.
  destruct sc1 as [|n1|l1| |], sc2 as [|n2|l2| |]; try by (right; intros H; inversion H).
  - destruct (decide (n1 = n2)) as [-> | Hneq]; [right; intros H; inversion H; congruence | left; eauto].
  - destruct (decide (n1 = 0)) as [-> | Hneq]; [left; eauto | right; intros H; inversion H; congruence].
  - destruct (decide (n2 = 0)) as [-> | Hneq]; [left; eauto | right; intros H; inversion H; congruence].
  - destruct (decide (l1 = l2)) as [<- | Hneq]; [right; intros H; inversion H; congruence | left; eauto].
Qed.


(* Compute subtype of `T` and offset to it from `path` *)
Fixpoint field_access (T : type) (path : list nat) :
  option (nat * type) :=
  match path with
  | [] => Some (O, T)
  | i :: path =>
    match T with
    | FixedSize sz =>
        if bool_decide (i ≤ sz) then Some (i, FixedSize (sz - i)) else None
    | Reference _ _ => match i with O => Some (O, T) | _ => None end
    | Unsafe T => field_access T path
    | Union Ts => T ← Ts !! i ; field_access T path
    | Product Ts =>
        T ← Ts !! i ; offT ← field_access T path;
        let sz : nat := foldl (λ sz T', sz + tsize T')%nat O (take i Ts) in
        Some (offT.1 + sz, offT.2)%nat
    | Sum Ts =>
        T ← Ts !! i ; offT ← field_access T path; Some (offT.1 + 1, offT.2)%nat
    end
  end.

Fixpoint write_mem l (v: value) h: mem :=
  match v with
  | [] => h
  | s :: v => write_mem (l +ₗ 1) v (<[l := s]> h)
  end.

Section no_mangle.
Local Unset Mangle Names. (* work around https://github.com/mattam82/Coq-Equations/issues/407 *)
Equations read_mem (l: loc) (n: nat) h: option value :=
  read_mem l n h := go l n (Some [])
  where go : loc → nat → option value → option value :=
        go l' O      oacc := oacc;
        go l' (S n')  oacc :=
          acc ← oacc ;
          v ← h !! l';
          go (l' +ₗ 1) n' (Some (acc ++ [v])).
End no_mangle.

Definition fresh_block (h : mem) : block :=
  let loclst : list loc := elements (dom h) in
  let blockset : gset block := foldr (λ l, ({[l.1]} ∪.)) ∅ loclst in
  fresh blockset.

Lemma is_fresh_block h i : (fresh_block h,i) ∉ dom h.
Proof.
  assert (∀ l (ls: list loc) (X : gset block),
    l ∈ ls → l.1 ∈ foldr (λ l, ({[l.1]} ∪.)) X ls) as help.
  { induction 1; set_solver. }
  rewrite /fresh_block /shift /= -elem_of_elements.
  move=> /(help _ _ ∅) /=. apply is_fresh.
Qed.

Lemma fresh_block_equiv (h1 h2: mem) :
  dom h1 ≡ dom h2 → fresh_block h1 = fresh_block h2.
Proof.
  intros EqD. apply elements_proper in EqD.
  rewrite /fresh_block. apply (fresh_proper (C:= gset _)).
  apply foldr_permutation; [apply _..|set_solver|done].
Qed.

Inductive pure_expr_step (P : prog) (h : mem) : expr → expr → list expr → Prop :=
| BinOpPS op (l1 l2 l': scalar) :
    bin_op_eval h op l1 l2 l' →
    pure_expr_step P h (BinOp op #[l1] #[l2]) #[l'] []
(* TODO: add more operations for values *)
| ProjPS (i: Z) (v : value) (s : scalar)
    (DEFINED: 0 ≤ i ∧ v !! (Z.to_nat i) = Some s) :
    pure_expr_step P h (Proj (Val v) #[i]) #[s] []
| ConcPS v1 v2 :
    pure_expr_step P h (Conc (Val v1) (Val v2))
                       (Val (v1 ++ v2)) []
| RefPS l lbor T :
    (* is_Some (h !! l) → *)
    pure_expr_step P h (Ref (Place l lbor T)) #[ScPtr l lbor] []
| DerefPS l lbor T
    (* (DEFINED: ∀ (i: nat), (i < tsize T)%nat → l +ₗ i ∈ dom h) *) :
    pure_expr_step P h (Deref #[ScPtr l lbor] T) (Place l lbor T) []
(* | FieldBS l lbor T path off T'
    (FIELD: field_access T path = Some (off, T')) :
    pure_expr_step FNs h (Field (Place l lbor T) path)
                         SilentEvt (Place (l +ₗ off) lbor T') *)
| LetPS x e1 e2 e' :
    is_Some (to_result e1) →
    subst' x e1 e2 = e' →
    pure_expr_step P h (let: x := e1 in e2) e' []
| CasePS i el e :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    pure_expr_step P h (case: #[i] of el) e []
| CallPS fn e2 f arg :
    P !! f = Some fn →
    to_result e2 = Some arg →
    pure_expr_step P h (Call #[ScFnPtr f] e2)
                       (apply_func fn arg) []
| WhilePS e1 e2 :
    (* unfold by one step *)
    pure_expr_step P h (While e1 e2) (if: e1 then (e2;; while: e1 do e2 od) else #[☠]) []
| ForkPS (e : expr) :
    pure_expr_step P h (Fork e) #[☠] [e]
  .

Inductive mem_expr_step (h: mem) : expr → event → mem → expr → list expr → Prop :=
| InitCallBS (c: call_id):
    mem_expr_step
              h InitCall
              (InitCallEvt c)
              h (Val $ [ScCallId c]) []
| EndCallBS (call: call_id) e :
    to_value e = Some [ScCallId call] →
    mem_expr_step h (EndCall e) (EndCallEvt call) h #[☠] []
| CopyBS l lbor T (v: value)
    (READ: read_mem l (tsize T) h = Some v) :
    mem_expr_step h (Copy (Place l lbor T)) (CopyEvt l lbor T v) h (Val v) []
| FailedCopyBS l lbor T :
    (* failed copies lead to poison, but still of the appropriate length *)
    mem_expr_step h (Copy (Place l lbor T)) (FailedCopyEvt l lbor T) h (Val $ replicate (tsize T) ScPoison) []
| WriteBS l lbor T v (LEN: length v = tsize T)
    (DEFINED: ∀ (i: nat), (i < length v)%nat → l +ₗ i ∈ dom h) :
    mem_expr_step
              h (Place l lbor T <- Val v)
              (WriteEvt l lbor T v)
              (write_mem l v h) #[☠] []
| AllocBS lbor T :
    let l := (fresh_block h, 0) in
    mem_expr_step
              h (Alloc T)
              (AllocEvt l lbor T)
              (init_mem l (tsize T) h) (Place l lbor T) []
| DeallocBS T l lbor :
    (∀ m, is_Some (h !! (l +ₗ m)) ↔ 0 ≤ m < tsize T) →
    mem_expr_step
              h (Free (Place l lbor T))
              (DeallocEvt l lbor T)
              (free_mem l (tsize T) h) #[☠] []
| RetagBS l otag ntag pkind T kind c :
    mem_expr_step
              h (Retag #[ScPtr l otag] #[ScCallId c] pkind T kind)
              (RetagEvt l otag ntag pkind T kind c)
              h #[ScPtr l ntag] []

(* observable behavior *)
(* | SysCallBS id h:
    expr_step (SysCall id) h (SysCallEvt id) (Lit LitPoison) h [] *)
.
