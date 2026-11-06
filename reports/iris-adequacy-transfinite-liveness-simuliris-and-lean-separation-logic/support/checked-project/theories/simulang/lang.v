From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe stepindex_finite.
From simuliris.simulation Require Export language.
From simuliris.simulang Require Export locations.

(** heap_lang.  A fairly simple language used for common Iris examples.

Noteworthy design choices:

- This is a right-to-left evaluated language, like CakeML and OCaml.  The reason
  for this is that it makes curried functions usable: Given a WP for [f a b], we
  know that any effects [f] might have do not matter until after *both* [a] and
  [b] are evaluated.  With left-to-right evaluation, that triple is basically
  useless unless the user let-expands [b].

- Even after deallocating a location, the heap remembers that these locations
  were previously allocated and makes sure they do not get reused. This is
  necessary to ensure soundness of the [meta] feature provided by [gen_heap].
  Also, unlike in languages like C, allocated and deallocated "blocks" do not
  have to match up: you can allocate a large array of locations and then
  deallocate a hole out of it in the middle.
*)

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module simp_lang.

(** Expressions and vals. *)

(** We have a notion of "poison" as a variant of unit that may not be compared
with anything. This is useful for erasure proofs: if we erased things to unit,
[<erased> == unit] would evaluate to true after erasure, changing program
behavior. So we erase to the poison value instead, making sure that no legal
comparisons could be affected. *)
Definition fname := string.
Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitPoison
  | LitLoc (l : loc) | LitFn (fn : fname).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

(* ordering requirement on memory accesses *)
Inductive order : Set :=
  ScOrd | Na1Ord | Na2Ord.

Inductive val :=
  | LitV (l : base_lit)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
    (* instead of lambda abstractions, we have let expressions and calls *)
  | Var (x : string)
  | GlobalVar (x : string)
  | Let (x : binder) (e1 e2 : expr)
  | Call (e1 : expr) (e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | While (e0 e1 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Match (e0 : expr) (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr)
  (* Concurrency *)
  | Fork (e : expr)
  (* Heap *)
  | AllocN (e1 e2 : expr) (* array length (positive number), initial value *)
  | FreeN (e1 e2 : expr) (* number of cells to free, location *)
  | Load (o : order) (e : expr)
  | Store (o : order) (e1 : expr) (e2 : expr)
(*  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
  | FAA (e1 : expr) (e2 : expr) (* Fetch-and-add *) *)
  .

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Definition to_fname (e : expr) : option fname :=
  match to_val e with
  | Some (LitV (LitFn fn)) => Some fn
  | _ => None
  end.
Definition of_fname (fn : fname) := Val $ LitV $ LitFn fn.

Definition of_call f v := Call (of_fname f) (of_val v).
Definition to_call (e : expr) : option (fname * val) :=
  match e with
  | Call e1 e2 =>
      match to_fname e1 with
      | Some fn => option_map (pair fn) (to_val e2)
      | _ => None
      end
  | _ => None
  end.


(** We assume the following encoding of values to 64-bit words: The least 3
significant bits of every word are a "tag", and we have 61 bits of payload,
which is enough if all pointers are 8-byte-aligned (common on 64bit
architectures). The tags have the following meaning:

0: Payload is the data for a LitV (LitInt _).
1: Payload is the data for a InjLV (LitV (LitInt _)).
2: Payload is the data for a InjRV (LitV (LitInt _)).
3: Payload is the data for a LitV (LitLoc _).
4: Payload is the data for a InjLV (LitV (LitLoc _)).
4: Payload is the data for a InjRV (LitV (LitLoc _)).
6: Payload is one of the following finitely many values, which 61 bits are more
   than enough to encode:
   LitV LitUnit, InjLV (LitV LitUnit), InjRV (LitV LitUnit),
   LitV LitPoison, InjLV (LitV LitPoison), InjRV (LitV LitPoison),
   LitV (LitBool _), InjLV (LitV (LitBool _)), InjRV (LitV (LitBool _)).
7: Value is boxed, i.e., payload is a pointer to some read-only memory area on
   the heap which stores whether this is a RecV, PairV, InjLV or InjRV and the
   relevant data for those cases. However, the boxed representation is never
   used if any of the above representations could be used.

Ignoring (as usual) the fact that we have to fit the infinite Z/loc into 61
bits, this means every value is machine-word-sized and can hence be atomically
read and written.  Also notice that the sets of boxed and unboxed values are
disjoint. *)
Definition lit_is_unboxed (l: base_lit) : Prop :=
  match l with
  (** Disallow comparing (erased) prophecies with (erased) prophecies, by
  considering them boxed. *)
  | LitPoison => False
  | LitInt _ | LitBool _  | LitLoc _ | LitFn _ | LitUnit => True
  end.
Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => lit_is_unboxed l
  | InjLV (LitV l) => lit_is_unboxed l
  | InjRV (LitV l) => lit_is_unboxed l
  | _ => False
  end.

Global Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l).
Proof. destruct l; simpl; exact (decide _). Defined.
Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | [] | [] ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

(** The state: heaps of [lock_state * val]s. *)
Inductive lock_state :=
| WSt | RSt (n : nat).
Record state : Type := State {
  heap: gmap loc (lock_state * val);
  used_dyn_blocks: gset dyn_block;
  globals: gset string;
}.
(** The initial heap contains only global variables as a closed
program can only refer to global variables on the heap.  *)
(* TODO: Allow global variables to contain arrays by using [gs : gmap string (list val)] *)
Definition state_init (gs : gmap string val) : state :=
  {| heap := kmap global_loc ((λ v, (RSt 0, v)) <$> gs); used_dyn_blocks := ∅; globals := dom gs |}.
Definition heap_wf (σ: state) : Prop :=
  ∀ b i v, σ.(heap) !! Loc (DynBlock b) i = Some v → b ∈ σ.(used_dyn_blocks).
Lemma state_init_wf gs :
  heap_wf (state_init gs).
Proof. by move => b i [st v] /= /lookup_kmap_Some [?[??]]. Qed.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Lemma to_of_call f v : to_call (of_call f v) = Some (f, v).
Proof. reflexivity. Qed.

Lemma of_to_call e f v : to_call e = Some (f, v) → of_call f v = e.
Proof.
  destruct e => //=.
  match goal with |- context[to_fname ?e] => destruct e => //= end.
  match goal with |- context[Val ?v] => destruct v as [[] | | |] => //= end.
  match goal with |- context[to_val ?e] => destruct e => //= end.
  by intros [= <- <-].
Qed.

Global Instance lock_state_eq_dec : EqDecision lock_state.
Proof. solve_decision. Defined.
Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance order_eq_dec : EqDecision order.
Proof. solve_decision. Defined.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.
Global Instance expr_eq_dec : EqDecision expr.
Proof. solve_decision. Defined.

Global Instance lock_state_countable : Countable lock_state.
Proof.
  refine (inj_countable' (λ st, match st with
   | RSt n => inr n
   | WSt => inl ()
   end) (λ st, match st with
   | (inl _) => WSt
   | (inr n) => RSt n
   end) _); by intros [].
Qed.
Global Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => (inl (inl n))
  | LitBool b => (inl (inr b))
  | LitUnit => (inr (inl false))
  | LitPoison => (inr (inl true))
  | LitLoc l => (inr (inr (inr l)))
  | LitFn fn => (inr (inr (inl fn)))
  end) (λ l, match l with
  | (inl (inl n)) => LitInt n
  | (inl (inr b)) => LitBool b
  | (inr (inl false)) => LitUnit
  | (inr (inl true)) => LitPoison
  | (inr (inr (inr l))) => LitLoc l
  | (inr (inr (inl fn))) => LitFn fn
  end) _); by intros [].
Qed.
Global Instance un_op_countable : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
  (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
Qed.
Global Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | OffsetOp => 13
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | _ => OffsetOp
  end) _); by intros [].
Qed.
Global Instance order_countable : Countable order.
Proof.
  refine (inj_countable' (λ o, match o with
   | ScOrd => 0
   | Na1Ord => 1
   | Na2Ord => 2
  end) (λ n, match n with
  | 0 => ScOrd
  | 1 => Na1Ord
  | _ => Na2Ord
  end) _); by intros [].
Qed.
Global Instance val_countable : Countable val.
Proof.
 set (enc :=
   fix go v :=
     match v with
     | LitV l => GenLeaf l
     | PairV v1 v2 => GenNode 1 [go v1; go v2]
     | InjLV v => GenNode 2 [go v]
     | InjRV v => GenNode 3 [go v]
     end).
 set (dec :=
   fix go v :=
     match v with
     | GenLeaf l => LitV l
     | GenNode 1 [v1; v2] => PairV (go v1) (go v2)
     | GenNode 2 [v] => InjLV (go v)
     | GenNode 3 [v] => InjRV (go v)
     | _ => LitV LitUnit (* dummy *)
     end).
 refine (inj_countable' enc dec _). intros v. induction v; simplify_eq/=; by f_equal.
Qed.

Global Instance : Inhabited lock_state := populate (RSt 0).
Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; used_dyn_blocks := inhabitant; globals := inhabitant |}.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

(** Evaluation contexts *)
Inductive ectx_item :=
  (* we can evaluate the expression that x will be bound to *)
  | LetEctx (x : binder) (e2 : expr)
  | CallLEctx (v2 : val)
  | CallREctx (e1 : expr)
  | UnOpEctx (op : un_op)
  | BinOpLEctx (op : bin_op) (v2 : val)
  | BinOpREctx (op : bin_op) (e1 : expr)
  | IfEctx (e1 e2 : expr)
  (* Deliberately nothing for While; that reduces *before* the condition reduces! *)
  | PairLEctx (v2 : val)
  | PairREctx (e1 : expr)
  | FstEctx
  | SndEctx
  | InjLEctx
  | InjREctx
  | MatchEctx (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr)
  | AllocNLEctx (v2 : val)
  | AllocNREctx (e1 : expr)
  | FreeNLEctx (v2 : val)
  | FreeNREctx (e1 : expr)
  | LoadEctx (o : order)
  | StoreLEctx (o : order) (v2 : val)
  | StoreREctx (o : order) (e1 : expr)
(*  | CmpXchgLEctx (v1 : val) (v2 : val)
  | CmpXchgMEctx (e0 : expr) (v2 : val)
  | CmpXchgREctx (e0 : expr) (e1 : expr)
  | FaaLEctx (v2 : val)
  | FaaREctx (e1 : expr) *)
  .

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | LetEctx x e2 => Let x e e2
  | CallLEctx v2 => Call e (Val v2)
  | CallREctx e1 => Call e1 e
  | UnOpEctx op => UnOp op e
  | BinOpLEctx op v2 => BinOp op e (Val v2)
  | BinOpREctx op e1 => BinOp op e1 e
  | IfEctx e1 e2 => If e e1 e2
  | PairLEctx v2 => Pair e (Val v2)
  | PairREctx e1 => Pair e1 e
  | FstEctx => Fst e
  | SndEctx => Snd e
  | InjLEctx => InjL e
  | InjREctx => InjR e
  | MatchEctx x1 e1 x2 e2 => Match e x1 e1 x2 e2
  | AllocNLEctx v2 => AllocN e (Val v2)
  | AllocNREctx e1 => AllocN e1 e
  | FreeNLEctx v2 => FreeN e (Val v2)
  | FreeNREctx e1 => FreeN e1 e
  | LoadEctx o => Load o e
  | StoreLEctx o v2 => Store o e (Val v2)
  | StoreREctx o e1 => Store o e1 e
(*  | CmpXchgLEctx v1 v2 => CmpXchg e (Val v1) (Val v2)
  | CmpXchgMEctx e0 v2 => CmpXchg e0 e (Val v2)
  | CmpXchgREctx e0 e1 => CmpXchg e0 e1 e
  | FaaLEctx v2 => FAA e (Val v2)
  | FaaREctx e1 => FAA e1 e *)
  end.

(** General contexts *)
Inductive ctx_item :=
  | LetLCtx (x : binder) (e2 : expr)
  | LetRCtx (x : binder) (e1 : expr)
  | CallLCtx (e2 : expr)
  | CallRCtx (e1 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (e2 : expr)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | IfLCtx (e1 e2 : expr)
  | IfMCtx (e0 e2 : expr)
  | IfRCtx (e0 e1 : expr)
  | WhileLCtx (e1 : expr)
  | WhileRCtx (e0 : expr)
  | PairLCtx (v2 : expr)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | MatchLCtx (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr)
  | MatchMCtx (e0 : expr) (x1 : binder) (x2 : binder) (e2 : expr)
  | MatchRCtx (e0 : expr) (x1 : binder) (e1 : expr) (x2 : binder)
  | ForkCtx
  | AllocNLCtx (v2 : expr)
  | AllocNRCtx (e1 : expr)
  | FreeNLCtx (v2 : expr)
  | FreeNRCtx (e1 : expr)
  | LoadCtx (o : order)
  | StoreLCtx (o : order) (v2 : expr)
  | StoreRCtx (o : order) (e1 : expr)
(*  | CmpXchgLCtx (v1 : expr) (v2 : expr)
  | CmpXchgMCtx (e0 : expr) (v2 : expr)
  | CmpXchgRCtx (e0 : expr) (e1 : expr)
  | FaaLCtx (v2 : expr)
  | FaaRCtx (e1 : expr) *)
  .

Definition fill_ctx_item (Ci : ctx_item) (e : expr) : expr :=
  match Ci with
  | LetLCtx x e2 => Let x e e2
  | LetRCtx x e1 => Let x e1 e
  | CallLCtx e2 => Call e e2
  | CallRCtx e1 => Call e1 e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op e1 => BinOp op e1 e
  | IfLCtx e1 e2 => If e e1 e2
  | IfMCtx e0 e2 => If e0 e e2
  | IfRCtx e0 e1 => If e0 e1 e
  | WhileLCtx e1 => While e e1
  | WhileRCtx e0 => While e0 e
  | PairLCtx e2 => Pair e e2
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | MatchLCtx x1 e1 x2 e2 => Match e x1 e1 x2 e2
  | MatchMCtx e0 x1 x2 e2 => Match e0 x1 e x2 e2
  | MatchRCtx e0 x1 e1 x2 => Match e0 x1 e1 x2 e
  | ForkCtx => Fork e
  | AllocNLCtx e2 => AllocN e e2
  | AllocNRCtx e1 => AllocN e1 e
  | FreeNLCtx e2 => FreeN e e2
  | FreeNRCtx e1 => FreeN e1 e
  | LoadCtx o => Load o e
  | StoreLCtx o e2 => Store o e e2
  | StoreRCtx o e1 => Store o e1 e
(*  | CmpXchgLCtx e1 e2 => CmpXchg e e1 e2
  | CmpXchgMCtx e0 e2 => CmpXchg e0 e e2
  | CmpXchgRCtx e0 e1 => CmpXchg e0 e1 e
  | FaaLCtx e2 => FAA e e2
  | FaaRCtx e1 => FAA e1 e *)
  end.

Definition ctx := list ctx_item.
Definition fill_ctx (C : ctx) (e : expr) : expr :=
  foldl (flip fill_ctx_item) e C.

Lemma fill_ctx_app C1 C2 e :
  fill_ctx (C1 ++ C2) e = fill_ctx C2 (fill_ctx C1 e).
Proof. apply foldl_app. Qed.

(** Splitting an expression into information about the head expression and subexpressions. *)
Inductive expr_head :=
  | ValHead (v : val)
  | VarHead (x : string)
  | GlobalVarHead (x : string)
  | LetHead (x : binder)
  | CallHead
  | UnOpHead (op : un_op)
  | BinOpHead (op : bin_op)
  | IfHead
  | WhileHead
  | PairHead
  | FstHead
  | SndHead
  | InjLHead
  | InjRHead
  | MatchHead (x1 : binder) (x2 : binder)
  | ForkHead
  | AllocNHead
  | FreeNHead
  | LoadHead (o : order)
  | StoreHead (o : order)
(*  | CmpXchgHead
  | FAAHead *)
.

Definition expr_split_head (e : expr) : (expr_head * list expr) :=
  match e with
  | Val v => (ValHead v, [])
  | Var x => (VarHead x, [])
  | GlobalVar x => (GlobalVarHead x, [])
  | Let x e1 e2 => (LetHead x, [e1; e2])
  | Call e1 e2 => (CallHead, [e1; e2])
  | UnOp op e => (UnOpHead op, [e])
  | BinOp op e1 e2 => (BinOpHead op, [e1; e2])
  | If e0 e1 e2 => (IfHead, [e0;e1;e2])
  | While e0 e1 => (WhileHead, [e0; e1])
  | Pair e1 e2 => (PairHead, [e1; e2])
  | Fst e => (FstHead, [e])
  | Snd e => (SndHead, [e])
  | InjL e => (InjLHead, [e])
  | InjR e => (InjRHead, [e])
  | Match e0 x1 e1 x2 e2 => (MatchHead x1 x2, [e0;e1;e2])
  | Fork e => (ForkHead, [e])
  | AllocN e1 e2 => (AllocNHead, [e1; e2])
  | FreeN e1 e2 => (FreeNHead, [e1; e2])
  | Load o e => (LoadHead o, [e])
  | Store o e1 e2 => (StoreHead o, [e1; e2])
(*  | CmpXchg e0 e1 e2 => (CmpXchgHead, [e0;e1;e2])
  | FAA e1 e2 => (FAAHead, [e1; e2]) *)
  end.

Global Instance expr_split_head_inj : Inj (=) (=) expr_split_head.
Proof. move => [^ e1] [^ e2] => //=; move => [*]; by simplify_eq. Qed.

Definition ectxi_split_head (Ki : ectx_item) : (expr_head * list expr) :=
  match Ki with
  | LetEctx x e => (LetHead x, [e])
  | CallLEctx v => (CallHead, [Val v])
  | CallREctx e => (CallHead, [e])
  | UnOpEctx op => (UnOpHead op, [])
  | BinOpLEctx op v => (BinOpHead op, [Val v])
  | BinOpREctx op e => (BinOpHead op, [e])
  | IfEctx e1 e2 => (IfHead, [e1; e2])
  | PairLEctx v => (PairHead, [Val v])
  | PairREctx e => (PairHead, [e])
  | FstEctx => (FstHead, [])
  | SndEctx => (SndHead, [])
  | InjLEctx => (InjLHead, [])
  | InjREctx => (InjRHead, [])
  | LoadEctx o => (LoadHead o, [])
  | MatchEctx x1 e1 x2 e2 => (MatchHead x1 x2, [e1; e2])
  | AllocNLEctx v => (AllocNHead, [Val v])
  | AllocNREctx e => (AllocNHead, [e])
  | FreeNLEctx v => (FreeNHead, [Val v])
  | FreeNREctx e => (FreeNHead, [e])
  | StoreLEctx o v => (StoreHead o, [Val v])
  | StoreREctx o e => (StoreHead o, [e])
(*  | CmpXchgLEctx v1 v2 => (CmpXchgHead, [Val v1; Val v2])
  | CmpXchgMEctx e1 v2 => (CmpXchgHead, [e1; Val v2])
  | CmpXchgREctx e1 e2 => (CmpXchgHead, [e1; e2])
  | FaaLEctx v => (FAAHead, [Val v])
  | FaaREctx e => (FAAHead, [e]) *)
  end.

Definition ctxi_split_head (Ci : ctx_item) : (expr_head * list expr) :=
  match Ci with
  | LetLCtx x e2 => (LetHead x, [e2])
  | LetRCtx x e1 => (LetHead x, [e1])
  | CallLCtx e2 => (CallHead, [e2])
  | CallRCtx e1 => (CallHead, [e1])
  | UnOpCtx op => (UnOpHead op, [])
  | BinOpLCtx op e2 => (BinOpHead op, [e2])
  | BinOpRCtx op e1 => (BinOpHead op, [e1])
  | IfLCtx e1 e2 => (IfHead, [e1; e2])
  | IfMCtx e0 e2 => (IfHead, [e0; e2])
  | IfRCtx e0 e1 => (IfHead, [e0; e1])
  | WhileLCtx e1 => (WhileHead, [e1])
  | WhileRCtx e0 => (WhileHead, [e0])
  | PairLCtx v2 => (PairHead, [v2])
  | PairRCtx e1 => (PairHead, [e1])
  | FstCtx => (FstHead, [])
  | SndCtx => (SndHead, [])
  | InjLCtx => (InjLHead, [])
  | InjRCtx => (InjRHead, [])
  | MatchLCtx x1 e1 x2 e2 => (MatchHead x1 x2, [e1; e2])
  | MatchMCtx e0 x1 x2 e2 => (MatchHead x1 x2, [e0; e2])
  | MatchRCtx e0 x1 e1 x2 => (MatchHead x1 x2, [e0; e1])
  | ForkCtx => (ForkHead, [])
  | AllocNLCtx v2 => (AllocNHead, [v2])
  | AllocNRCtx e1 => (AllocNHead, [e1])
  | FreeNLCtx v2 => (FreeNHead, [v2])
  | FreeNRCtx e1 => (FreeNHead, [e1])
  | LoadCtx o => (LoadHead o, [])
  | StoreLCtx o v2 => (StoreHead o, [v2])
  | StoreRCtx o e1 => (StoreHead o, [e1])
(*  | CmpXchgLCtx v1 v2 => (CmpXchgHead, [v1; v2])
  | CmpXchgMCtx e0 v2 => (CmpXchgHead, [e0; v2])
  | CmpXchgRCtx e0 e1 => (CmpXchgHead, [e0; e1])
  | FaaLCtx v2 => (FAAHead, [v2])
  | FaaRCtx e1 => (FAAHead, [e1]) *)
  end.


(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ | GlobalVar _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Let y e1 e2 =>
     Let y (subst x v e1) (if decide (BNamed x ≠ y) then subst x v e2 else e2)
  | Call e1 e2 => Call (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | While e0 e1 => While (subst x v e0) (subst x v e1)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Match e0 x1 e1 x2 e2 => Match (subst x v e0) x1 (if decide (BNamed x ≠ x1) then subst x v e1 else e1)
      x2 (if decide (BNamed x ≠ x2) then subst x v e2 else e2)
  | Fork e => Fork (subst x v e)
  | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
  | FreeN e1 e2 => FreeN (subst x v e1) (subst x v e2)
  | Load o e => Load o (subst x v e)
  | Store o e1 e2 => Store o (subst x v e1) (subst x v e2)
(*  | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | FAA e1 e2 => FAA (subst x v e1) (subst x v e2) *)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(** Functions and function calls *)
Definition func : Type := string * expr.
Bind Scope expr_scope with func.
Definition apply_func (fn : func) (v : val) := subst fn.1 v fn.2.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => if decide (n2 = 0) then None else Some $ LitInt (n1 `quot` n2)
  | RemOp => if decide (n2 = 0) then None else Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  | OffsetOp => None (* Pointer arithmetic *)
  end%Z.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    (* Crucially, this compares the same way as [CmpXchg]! *)
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.


Definition state_upd_heap (f: gmap loc (lock_state * val) → gmap loc (lock_state * val)) (σ: state) : state :=
  {| heap := f σ.(heap); used_dyn_blocks := σ.(used_dyn_blocks); globals := σ.(globals) |}.
Global Arguments state_upd_heap _ !_ /.
Definition state_upd_used_dyn_blocks (f: gset dyn_block → gset dyn_block) (σ: state) : state :=
  {| heap := σ.(heap); used_dyn_blocks := f σ.(used_dyn_blocks); globals := σ.(globals) |}.
Global Arguments state_upd_used_dyn_blocks _ !_ /.

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc (lock_state * val) :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := (RSt 0, v)]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := (RSt 0, v)]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs ow k :
  heap_array l vs !! k = Some ow ↔
  ∃ j w, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ ow = (RSt 0, w) ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & w & ? & -> & -> & ?)].
    { eexists 0, _. rewrite loc_add_0. naive_solver lia. }
    eexists (1 + j)%Z, _. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & w & ? & -> & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z, _. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc (lock_state * val)) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&w&?&->&?&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate (Z.to_nat n) v) ∪ h) σ.

Lemma state_init_heap_empty l v σ :
  state_init_heap l 0 v σ = σ.
Proof.
  destruct σ as [h]. rewrite /state_init_heap /=. f_equiv.
  by rewrite left_id.
Qed.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_upd_heap <[l:= (RSt 0, v)]> σ.
Proof.
  destruct σ as [h]. rewrite /state_init_heap /=. f_equiv.
  rewrite right_id insert_union_singleton_l. done.
Qed.

Fixpoint free_mem (l : loc) (n : nat) (σ : gmap loc (lock_state * val))
  : gmap loc (lock_state * val) :=
  match n with
  | O => σ
  | S n => delete l (free_mem (l +ₗ 1) n σ)
  end.
Lemma lookup_free_mem_1 l l' n σ :
  loc_block l ≠ loc_block l' → (free_mem l n σ) !! l' = σ !! l'.
Proof.
  induction n as [ | n IH] in l |-*; cbn; first done.
  intros Hneq. rewrite lookup_delete_ne; last by congruence.
  by apply IH.
Qed.
Lemma lookup_free_mem_2 l l' (n : nat) σ :
  loc_block l = loc_block l' → (loc_idx l ≤ loc_idx l' < loc_idx l + n)%Z → (free_mem l n σ) !! l' = None.
Proof.
  induction n as [ | n IH] in l |-*; cbn; first lia.
  intros Hblock Hi.
  destruct (decide (loc_idx l = loc_idx l')) as [Heq | Hneq].
  - rewrite lookup_delete_None; left. destruct l, l'; simpl in *; congruence.
  - rewrite lookup_delete_ne; last congruence. apply IH; first done. destruct l, l'; simpl in *; lia.
Qed.
Lemma lookup_free_mem_3 l l' (n : nat) σ :
  loc_block l = loc_block l' → (loc_idx l' < loc_idx l)%Z → (free_mem l n σ) !! l' = σ !! l'.
Proof.
  induction n as [ | n IH] in l |-*; cbn; first done.
  intros Hblock Hi. rewrite lookup_delete_ne.
  - apply IH; first done. destruct l, l'; cbn in *; lia.
  - destruct l, l'; cbn in *; intros [=]. lia.
Qed.
Lemma lookup_free_mem_4 l l' (n : nat) σ :
  loc_block l = loc_block l' → (loc_idx l' >= loc_idx l + n)%Z → (free_mem l n σ) !! l' = σ !! l'.
Proof.
  induction n as [ | n IH] in l |-*; cbn; first done.
  intros Hblock Hi. rewrite lookup_delete_ne.
  - apply IH; first done. destruct l, l'; cbn in *; lia.
  - destruct l, l'; cbn in *; intros [=]. lia.
Qed.
Lemma lookup_free_mem_Some l l' n σ v:
  free_mem l n σ !! l' = Some v ↔ σ !! l' = Some v ∧ (loc_block l ≠ loc_block l' ∨ ¬(loc_idx l ≤ loc_idx l' < loc_idx l + n)%Z).
Proof.
  destruct (decide (loc_block l = loc_block l')).
  2: { rewrite lookup_free_mem_1 //. naive_solver. }
  destruct (decide (loc_idx l' < loc_idx l)%Z).
  { rewrite lookup_free_mem_3 //. naive_solver lia. }
  destruct (decide (loc_idx l' >= loc_idx l + n)%Z).
  { rewrite lookup_free_mem_4 //. naive_solver lia. }
  rewrite lookup_free_mem_2 //; [|lia]. naive_solver lia.
Qed.

Lemma delete_free_mem σ l n o:
  (o > 0)%Z →
  delete l (free_mem (l +ₗ o) n σ) = free_mem (l +ₗ o) n (delete l σ).
Proof.
  intros HO.
  induction n as [|n IH] in o, HO|-* => //=. rewrite delete_delete. f_equal.
  rewrite loc_add_assoc IH; [done | lia].
Qed.

Lemma heap_wf_init_mem b n σ v:
  heap_wf σ →
  heap_wf $ State (heap_array (dyn_loc b) (replicate n v) ∪ σ.(heap)) ({[b]} ∪ σ.(used_dyn_blocks)) σ.(globals).
Proof.
  move => Hwf b' i' v' /lookup_union_Some_raw [/heap_array_lookup[?[?[?[[??][??]]]]]|[??]].
  - set_solver.
  - set_unfold. right. by apply: Hwf.
Qed.
Lemma heap_wf_free_mem l n σ:
  heap_wf σ →
  heap_wf $ state_upd_heap (free_mem l n) σ.
Proof. move => Hwf b' i' v' /lookup_free_mem_Some [??]. by apply: Hwf. Qed.
Lemma heap_wf_insert σ l p :
  heap_wf σ → is_Some (σ.(heap) !! l) →
  heap_wf $ state_upd_heap <[l := p]> σ.
Proof. move => Hwf [??] ??? /lookup_insert_Some[[??]|[??]]; simplify_eq; by apply: Hwf. Qed.

(** Building actual evaluation contexts out of ectx_items *)
Definition ectx := list ectx_item.
Definition empty_ectx : ectx := [].
Definition ectx_compose : ectx → ectx → ectx := flip (++).

Definition fill (K : ectx) (e : expr) : expr := foldl (flip fill_item) e K.

Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. apply foldl_app. Qed.

(** Programs *)
Definition prog := gmap fname func.

Notation "e1 ;; e2" := (Let BAnon e1%E e2%E)
  (at level 100, e2 at level 200,
   format "'[' '[hv' '[' e1 ']' ;;  ']' '/' e2 ']'") : expr_scope.
Inductive base_step (P : prog) : expr → state → expr → state → list expr → Prop :=
  | GlobalVarS n σ :
     n ∈ σ.(globals) →
     base_step P (GlobalVar n) σ (Val $ LitV $ LitLoc $ global_loc n) σ []
  | PairS v1 v2 σ :
     base_step P (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ []
  | InjLS v σ :
     base_step P (InjL $ Val v) σ (Val $ InjLV v) σ []
  | InjRS v σ :
     base_step P (InjR $ Val v) σ (Val $ InjRV v) σ []
  | LetS x v1 e2 e' σ :
     e' = subst' x v1 e2 →
     base_step P (Let x (Val $ v1) e2) σ e' σ []
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     base_step P (UnOp op (Val v)) σ (Val v') σ []
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     base_step P (BinOp op (Val v1) (Val v2)) σ (Val v') σ []
  | IfTrueS e1 e2 σ :
     base_step P (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ []
  | IfFalseS e1 e2 σ :
     base_step P (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ []
  | WhileS e0 e1 σ :
      base_step P (While e0 e1) σ (If e0 (e1 ;; While e0 e1) (Val $ LitV $ LitUnit)) σ []
  | FstS v1 v2 σ :
     base_step P (Fst (Val $ PairV v1 v2)) σ (Val v1) σ []
  | SndS v1 v2 σ :
     base_step P (Snd (Val $ PairV v1 v2)) σ (Val v2) σ []
  | MatchLS v x1 e1 x2 e2 e' σ :
      e' = subst' x1 v e1 →
     base_step P (Match (Val $ InjLV v) x1 e1 x2 e2) σ e' σ []
  | MatchRS v x1 e1 x2 e2 e' σ :
      e' = subst' x2 v e2 →
     base_step P (Match (Val $ InjRV v) x1 e1 x2 e2) σ e' σ []
  | ForkS e σ:
     base_step P (Fork e) σ (Val $ LitV LitUnit) σ [e]
  | AllocNS n v σ b :
     (0 < n)%Z →
     b ∉ σ.(used_dyn_blocks) →
     (∀ i, σ.(heap) !! (dyn_loc b +ₗ i) = None) →
     base_step P (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
               (Val $ LitV $ LitLoc (dyn_loc b)) (state_upd_used_dyn_blocks ({[b]} ∪.) (state_init_heap (dyn_loc b) n v σ)) []
  | FreeNS l σ n :
     (0 < n)%Z →
     block_is_dyn l.(loc_block) →
     (* always need to deallocate the full block *)
     (∀ m, is_Some (σ.(heap) !! (l +ₗ m)) ↔ 0 ≤ m < n)%Z →
     base_step P (FreeN (Val $ LitV $ LitInt n) (Val $ LitV $ LitLoc l)) σ
               (Val $ LitV LitUnit) (state_upd_heap (free_mem l (Z.to_nat n)) σ) []
  | LoadScS l v σ n :
     σ.(heap) !! l = Some (RSt n, v) →
     base_step P (Load ScOrd (Val $ LitV $ LitLoc l)) σ (of_val v) σ []
  | StoreScS l v v' σ :
     σ.(heap) !! l = Some (RSt 0, v) →
     base_step P (Store ScOrd (Val $ LitV $ LitLoc l) (Val v')) σ
               (Val $ LitV LitUnit) (state_upd_heap <[l:=(RSt 0, v')]> σ) []
  | LoadNa1S l v σ n :
      σ.(heap) !! l = Some (RSt n, v) →
      base_step P (Load Na1Ord (Val $ LitV $ LitLoc l)) σ
        (Load Na2Ord (Val $ LitV $ LitLoc l)) (state_upd_heap <[l := (RSt (S n), v)]> σ) []
  | LoadNa2S l v σ n :
      σ.(heap) !! l = Some (RSt (S n), v) →
      base_step P (Load Na2Ord (Val $ LitV $ LitLoc l)) σ
                (of_val v) (state_upd_heap <[l := (RSt n, v)]> σ) []
  | StoreNa1S l v v' σ :
      σ.(heap) !! l = Some (RSt 0, v) →
      base_step P (Store Na1Ord (Val $ LitV $ LitLoc l) (Val v')) σ
                (Store Na2Ord (Val $ LitV $ LitLoc l) (Val v')) (state_upd_heap <[l:=(WSt, v)]> σ) []
  | StoreNa2S l v v' σ :
      σ.(heap) !! l = Some (WSt, v) →
      base_step P (Store Na2Ord (Val $ LitV $ LitLoc l) (Val v')) σ
                (Val $ LitV LitUnit) (state_upd_heap <[l:=(RSt 0, v')]> σ) []
  | CallS f v fn σ :
     P !! f = Some fn →
     base_step P (Call (Val $ LitV $ LitFn f) (Val v)) σ (apply_func fn v) σ [].


Definition of_class (m : mixin_expr_class val) : expr :=
  match m with
  | ExprVal v => of_val v
  | ExprCall f v => of_call f v
  end.
Definition to_class (e : expr) : option (mixin_expr_class val) :=
  match to_val e with
  | Some v => Some (ExprVal v)
  | None => option_map (λ '(fn, v), ExprCall fn v) (to_call e)
  end.

Lemma to_of_class m : to_class (of_class m) = Some m.
Proof. destruct m; done. Qed.
Lemma of_to_class e m : to_class e = Some m → of_class m = e.
Proof.
  destruct m.
  + destruct e; try discriminate 1; first by inversion 1.
    rewrite /to_class; simpl. destruct to_fname, to_val; simpl; congruence.
  + destruct e; try discriminate 1. rewrite /to_class; simpl.
    match goal with |- context[to_fname ?e] => destruct e => //= end.
    match goal with |- context[to_fname (Val ?xv)] => rename xv into v end.
    destruct v as [[ | | | | |fn] | | | ]; simpl; try congruence.
    match goal with |- context[to_val ?e] => destruct e => //= end.
    by inversion 1.
Qed.

Lemma to_class_val e v : to_class e = Some (ExprVal v) → to_val e = Some v.
Proof.
  destruct e; simpl; try discriminate 1.
  - by inversion 1.
  - match goal with |- context[Call ?e _] => destruct e => //= end.
    rewrite /to_class; simpl.
    destruct to_fname; last done.
    match goal with |- context[to_val ?e] => destruct e => //= end.
Qed.
Lemma to_class_call e f v : to_class e = Some (ExprCall f v) → to_call e = Some (f, v).
Proof.
  destruct e; rewrite /to_class; simpl; try discriminate 1.
  destruct to_fname; simpl; try discriminate 1.
  match goal with |- context[to_val ?e] => destruct e => //= end.
  by inversion 1.
Qed.

Lemma to_val_class e v : to_val e = Some v → to_class e = Some (ExprVal v).
Proof. destruct e; cbn; try discriminate 1. by inversion 1. Qed.
Lemma to_call_class e f v : to_call e = Some (f, v) → to_class e = Some (ExprCall f v).
Proof.
  destruct e; rewrite /to_call /to_class; simpl; try discriminate 1.
  destruct to_fname; try discriminate 1.
  destruct to_val; try discriminate 1. by inversion 1.
Qed.

(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Global Instance fill_inj K : Inj (=) (=) (fill K).
Proof. induction K; intros ???; by simplify_eq/=. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.
Lemma fill_item_val_none Ki e :
  to_val e = None → to_val (fill_item Ki e) = None.
Proof.
  destruct (to_val (fill_item Ki e)) eqn:H.
  - edestruct (fill_item_val) as [v' ?]; [ eauto | congruence].
  - done.
Qed.

Lemma fill_val K e :
  is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  induction K as [|Ki K IH] in e |-*; intros [v ?].
  - simplify_option_eq; eauto.
  - eapply fill_item_val, IH, mk_is_Some. eauto.
Qed.
Lemma fill_val_none K e :
  to_val e = None → to_val (fill K e) = None.
Proof.
  destruct (to_val (fill K e)) eqn:H.
  - edestruct (fill_val) as [v' ?]; [ eauto | congruence].
  - done.
Qed.

Lemma val_base_stuck P e1 σ1 e2 σ2 efs : base_step P e1 σ1 e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma base_ctx_step_val P Ki e σ1 e2 σ2 efs :
  base_step P (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e).
Proof. revert e2. induction Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma base_step_fill_val P Ki K e σ1 e2 σ2 efs:
  base_step P (fill K (fill_item Ki e)) σ1 e2 σ2 efs → is_Some (to_val e).
Proof.
  revert e Ki.
  induction K as [ | Ki' K IH]; simpl; intros e Ki.
  - by intros ?%base_ctx_step_val.
  - intros H. eapply IH in H. by eapply fill_item_val.
Qed.

Lemma head_ectx_step_no_val P K e σ1 e2 σ2 efs:
  to_val e = None → base_step P (fill K e) σ1 e2 σ2 efs → K = empty_ectx.
Proof.
  intros Hnoval H.
  destruct K as [ | Ki K]; first reflexivity.
  exfalso. apply base_step_fill_val in H.
  eapply is_Some_None; by rewrite <-Hnoval.
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  revert Ki1. induction Ki2; intros Ki1; induction Ki1; naive_solver eauto with f_equal.
Qed.

Lemma alloc_fresh P v n σ :
  let l := dyn_loc (fresh σ.(used_dyn_blocks)) in
  (0 < n)%Z →
  heap_wf σ →
  base_step P (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ
            (Val $ LitV $ LitLoc l)
            (state_upd_used_dyn_blocks ({[(fresh σ.(used_dyn_blocks))]} ∪.) (state_init_heap l n v σ)) [].
Proof.
  intros l Hn Hwf. apply AllocNS; first done.
  - apply is_fresh.
  - move => i. apply eq_None_not_Some => -[? /Hwf]. apply is_fresh.
Qed.

Lemma fill_eq P σ1 σ2 e1 e1' e2 K K' efs:
  to_val e1 = None →
  base_step P e1' σ1 e2 σ2 efs →
  fill K e1 = fill K' e1' →
  ∃ K'', K' = ectx_compose K K''.
Proof.
  intros Hval Hstep; revert K'.
  induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
  destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
  { rewrite fill_app in Hstep. apply base_ctx_step_val in Hstep.
    apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
  rewrite !fill_app /= in Hfill.
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill; first by apply fill_val_none.
    apply fill_val_none. eauto using val_base_stuck. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto.
  exists K''. unfold ectx_compose. cbn. by rewrite assoc.
Qed.


(** * Parallel substitution for SimpLang *)
(** Definitions and proofs mostly yoinked from https://gitlab.mpi-sws.org/FP/stacked-borrows/-/blob/master/theories/lang/subst_map.v *)

Fixpoint subst_map (xs : gmap string val) (e : expr) : expr :=
  match e with
  | Var y => if xs !! y is Some v then Val v else Var y
  | Val v => Val v
  | GlobalVar n => GlobalVar n
  | Let x1 e1 e2 => Let x1 (subst_map xs e1) (subst_map (binder_delete x1 xs) e2)
  | Call e1 e2 => Call (subst_map xs e1) (subst_map xs e2)
  | UnOp op e => UnOp op (subst_map xs e)
  | BinOp op e1 e2 => BinOp op (subst_map xs e1) (subst_map xs e2)
  | If e0 e1 e2 => If (subst_map xs e0) (subst_map xs e1) (subst_map xs e2)
  | While e0 e1 => While (subst_map xs e0) (subst_map xs e1)
  | Pair e1 e2 => Pair (subst_map xs e1) (subst_map xs e2)
  | Fst e => Fst (subst_map xs e)
  | Snd e => Snd (subst_map xs e)
  | InjL e => InjL (subst_map xs e)
  | InjR e => InjR (subst_map xs e)
  | Match e0 x1 e1 x2 e2 => Match (subst_map xs e0) x1 (subst_map (binder_delete x1 xs) e1)
      x2 (subst_map (binder_delete x2 xs) e2)
  | Fork e => Fork (subst_map xs e)
  | AllocN e1 e2 => AllocN (subst_map xs e1) (subst_map xs e2)
  | FreeN e1 e2 => FreeN (subst_map xs e1) (subst_map xs e2)
  | Load o e => Load o (subst_map xs e)
  | Store o e1 e2 => Store o (subst_map xs e1) (subst_map xs e2)
(*  | CmpXchg e0 e1 e2 => CmpXchg (subst_map xs e0) (subst_map xs e1) (subst_map xs e2)
  | FAA e1 e2 => FAA (subst_map xs e1) (subst_map xs e2) *)
  end.

Lemma subst_map_empty e :
  subst_map ∅ e = e.
Proof.
  induction e; simpl; f_equal; eauto.
  all: match goal with |- context[binder_delete ?x ∅] => destruct x; first done end.
  all: simpl; rewrite delete_empty; done.
Qed.

Lemma subst_map_subst map x (v : val) (e : expr) :
  subst_map map (subst x v e) = subst_map (<[x:=v]>map) e.
Proof.
  revert x v map; induction e; intros xx r map; simpl;
  try (f_equal; eauto).
  all: try match goal with |- context[binder_delete ?x _] => destruct x; simpl; first done end.
  - case_decide.
    + simplify_eq/=. by rewrite lookup_insert_eq.
    + rewrite lookup_insert_ne; done.
  - case_decide.
    + rewrite delete_insert_ne; last by congruence. done.
    + simplify_eq/=. by rewrite delete_insert_eq.
  - case_decide.
    + rewrite delete_insert_ne; last by congruence. done.
    + simplify_eq/=. by rewrite delete_insert_eq.
  - case_decide.
    + rewrite delete_insert_ne; last by congruence. done.
    + simplify_eq/=. by rewrite delete_insert_eq.
Qed.

Lemma subst_subst_map x (v : val) map e :
  subst x v (subst_map (delete x map) e) =
  subst_map (<[x:=v]>map) e.
Proof.
  revert map v x; induction e; intros map v0 xx; simpl;
  try (f_equal; eauto).
  all: try match goal with |- context[binder_delete ?x _] => destruct x; simpl; first by auto end.
  - match goal with |- context[delete _ _ !! ?s] => rename s into x end.
    destruct (decide (xx=x)) as [->|Hne].
    + rewrite lookup_delete_eq // lookup_insert_eq //. simpl.
      rewrite decide_True //.
    + rewrite lookup_delete_ne // lookup_insert_ne //.
      destruct (map !! x) as [rr|].
      * by destruct rr.
      * simpl. rewrite decide_False //.
  - case_decide.
    + rewrite delete_insert_ne //; last congruence. rewrite delete_delete. eauto.
    + simplify_eq. rewrite delete_delete_eq delete_insert_eq. done.
  - case_decide.
    + rewrite delete_insert_ne //; last congruence. rewrite delete_delete. eauto.
    + simplify_eq. rewrite delete_delete_eq delete_insert_eq. done.
  - case_decide.
    + rewrite delete_insert_ne //; last congruence. rewrite delete_delete. eauto.
    + simplify_eq. rewrite delete_delete_eq delete_insert_eq. done.
Qed.

Lemma subst_map_singleton x v e :
  subst_map {[x:=v]} e = subst x v e.
Proof. rewrite -subst_map_subst subst_map_empty //. Qed.

Lemma subst'_subst_map b (v : val) map e :
  subst' b v (subst_map (binder_delete b map) e) =
  subst_map (binder_insert b v map) e.
Proof.
  destruct b; first done.
  exact: subst_subst_map.
Qed.

Lemma subst_map_subst_map xs ys e :
  subst_map xs (subst_map ys e) = subst_map (ys ∪ xs) e.
Proof.
  revert e.
  induction ys as [|x v ys HNone IH] using map_ind => e.
  { by rewrite left_id subst_map_empty. }
  by rewrite -insert_union_l -[in X in _ = X]subst_map_subst -IH subst_map_subst.
Qed.

(** "Free variables" and their interaction with subst_map *)
Local Definition binder_to_ctx (x : binder) : gset string :=
  if x is BNamed s then {[s]} else ∅.

Fixpoint free_vars (e : expr) : gset string :=
  match e with
  | Val v => ∅
  | GlobalVar n => ∅
  | Var x => {[x]}
  | Let x e1 e2 => free_vars e1 ∪ (free_vars e2 ∖ binder_to_ctx x)
  | Match e0 x1 e1 x2 e2 =>
    free_vars e0 ∪
    (free_vars e1 ∖ binder_to_ctx x1) ∪
    (free_vars e2 ∖ binder_to_ctx x2)
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Load _ e =>
     free_vars e
  | Call e1 e2 | While e1 e2 | BinOp _ e1 e2 | Pair e1 e2
  | AllocN e1 e2 | FreeN e1 e2 | Store _ e1 e2 =>
     free_vars e1 ∪ free_vars e2
  | If e0 e1 e2 =>
     free_vars e0 ∪ free_vars e1 ∪ free_vars e2
  end.

Local Lemma binder_delete_eq x y (xs1 xs2 : gmap string val) :
  (if y is BNamed s then s ≠ x → xs1 !! x = xs2 !! x else xs1 !! x = xs2 !! x) →
  binder_delete y xs1 !! x = binder_delete y xs2 !! x.
Proof.
  destruct y as [|s]; first done. simpl.
  destruct (decide (s = x)) as [->|Hne].
  - rewrite !lookup_delete_eq //.
  - rewrite !lookup_delete_ne //. eauto.
Qed.

Lemma subst_map_free_vars (xs1 xs2 : gmap string val) (e : expr) :
  (∀ x, x ∈ free_vars e → xs1 !! x = xs2 !! x) →
  subst_map xs1 e = subst_map xs2 e.
Proof.
  revert xs1 xs2; induction e=>/= xs1 xs2 Heq;
  solve [
    (* trivial cases *)
    done
  | (* variable case *)
    rewrite Heq; [done|set_solver]
  | (* recursive cases *)
    f_equal;
    repeat lazymatch goal with x : binder |- _ => destruct x end;
    intuition eauto using binder_delete_eq with set_solver
  ].
Qed.

Lemma subst_free_vars x v e :
  x ∉ free_vars e →
  subst x v e = e.
Proof.
  intros Hfree.
  rewrite -(subst_map_empty (subst x v e)).
  rewrite subst_map_subst.
  rewrite (subst_map_free_vars _ ∅); first by apply subst_map_empty.
  intros y ?. rewrite lookup_insert_ne //. set_solver.
Qed.

Lemma free_vars_subst x v e :
  free_vars (subst x v e) = free_vars e ∖ {[x]}.
Proof.
  induction e=>/=; repeat case_decide; set_solver.
Qed.

Lemma free_vars_subst_map xs e :
  free_vars (subst_map xs e) = free_vars e ∖ (dom xs).
Proof.
  induction xs as [| x v xs HNone IH] using map_ind.
  - rewrite subst_map_empty. set_solver.
  - rewrite -subst_subst_map delete_id // free_vars_subst IH. set_solver.
Qed.

(* Proving the mixin *)

Lemma simp_lang_mixin :
  LanguageMixin of_class to_class empty_ectx ectx_compose fill
    subst_map free_vars apply_func base_step.
Proof.
  constructor.
  - apply to_of_class.
  - apply of_to_class.
  - intros p v ???? H%val_base_stuck. cbn in H. congruence.
  - intros p f v ????. split.
    + cbn. inversion 1; subst. eexists _. eauto.
    + intros (fn & ? & -> & -> & ->). cbn. by constructor.
  - eapply subst_map_empty.
  - eapply subst_map_subst_map.
  - eapply subst_map_free_vars.
  - eapply free_vars_subst_map.
  - done.
  - intros ???. by rewrite -fill_app.
  - apply fill_inj.
  - intros K e H.
    destruct to_class as [[]|] eqn:Heq; last by apply is_Some_None in H.
    + right. apply to_class_val in Heq.
      edestruct (fill_val K e) as [v' Hval]; first by eauto.
      exists v'. by apply to_val_class.
    + destruct (to_val e) eqn:Hval. { right; eauto using to_val_class. }
      left. apply to_class_call in Heq. clear H.
      assert (K ≠ empty_ectx → to_call (fill K e) = None) as H.
      { clear Heq. destruct K as [ | Ki K]; first by destruct 1. intros _.
        revert Hval. revert Ki e.
        induction K as [ | ?? IH]; cbn; intros Ki e Hval.
        - destruct Ki; cbn; try reflexivity.
          { rewrite /to_fname. by rewrite Hval. }
          rewrite Hval. by destruct to_fname.
        - cbn in IH. by apply IH, fill_item_val_none.
      }
      rewrite Heq in H. destruct K; first done.
      rename select string into fn_name.
      rename select val into arg.
      enough (Some (fn_name, arg) = None) by congruence. by apply H.
  - intros p K K' e1' e1_redex σ1 e2 σ2 efs H. destruct to_class as [ [] | ] eqn:Heq; first done.
    + intros _ Hstep.
      eapply fill_eq; [ | apply Hstep | apply H].
      rewrite <-(of_to_class _ _ Heq). reflexivity.
    + intros _ Hstep. eapply fill_eq; [ | apply Hstep | apply H].
      destruct to_val eqn:Hval; last done. apply to_val_class in Hval; congruence.
  - intros ?????? H.
    match goal with |- context[to_class ?e] => destruct (to_val e) eqn:Heq end.
    { right. eexists. by apply to_val_class. }
    left. by eapply head_ectx_step_no_val.
Qed.
End simp_lang.

Canonical Structure simp_lang := Language (simp_lang.simp_lang_mixin).
Export simp_lang.
