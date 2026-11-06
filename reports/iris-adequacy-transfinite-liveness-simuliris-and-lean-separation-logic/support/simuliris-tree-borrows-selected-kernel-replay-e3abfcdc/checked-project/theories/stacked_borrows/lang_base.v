(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From stdpp Require Export countable binders gmap.
From iris.prelude Require Import prelude options.

(*Global Open Scope general_if_scope.*)
From simuliris.stacked_borrows Require Export type locations.

Declare Scope expr_scope.
Declare Scope val_scope.
Declare Scope sc_scope.
Declare Scope result_scope.

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.
Delimit Scope sc_scope with S.
Delimit Scope result_scope with R.

Local Open Scope Z_scope.

(** Id to track calls *)
Notation call_id := nat (only parsing).
(* Set of active call ids *)
Definition call_id_set := gset call_id.

(** Tags for pointers *)
Notation ptr_id := nat (only parsing).

Inductive tag :=
  | Tagged (t: ptr_id)
  | Untagged.

Global Instance tag_eq_dec : EqDecision tag.
Proof. solve_decision. Defined.
Global Instance tag_countable : Countable tag.
Proof.
  refine (inj_countable
          (λ tg, match tg with
              | Tagged t => inl t
              | Untagged => inr ()
              end)
          (λ s, match s with
              | inl t => Some $ Tagged t
              | inr _ => Some $ Untagged
              end) _); by intros [].
Qed.

Inductive permission := Unique | SharedReadWrite | SharedReadOnly | Disabled.
Global Instance permission_eq_dec : EqDecision permission.
Proof. solve_decision. Defined.
Global Instance permission_countable : Countable permission.
Proof.
  refine (inj_countable
    (λ p,
      match p with
      | Unique => 0 | SharedReadWrite => 1 | SharedReadOnly => 2 | Disabled => 3
      end)
    (λ s,
      match s with
      | 0 => Some Unique | 1 => Some SharedReadWrite | 2 => Some SharedReadOnly
      | _ => Some Disabled
      end) _); by intros [].
Qed.

(** Stacks of borrows. *)
Record item := mkItem {
  perm      : permission;
  tg        : tag;
  protector : option call_id;
}.
Global Instance item_eq_dec : EqDecision item.
Proof. solve_decision. Defined.

Definition stack := list item.
Definition stacks := gmap loc stack.

(** Retag kinds *)
Inductive retag_kind := FnEntry | TwoPhase | RawRt | Default.

Definition is_two_phase (kind: retag_kind) : bool :=
  match kind with TwoPhase => true | _ => false end.

(** Language base constructs *)

(** Unary/Binary ops *)
Inductive bin_op :=
  | AddOp     (* + addition       *)
  | SubOp     (* - subtraction    *)
(* | MulOp     (* * multiplication *)
  | DivOp     (* / division       *)
  | RemOp     (* % modulus        *)
  | BitXorOp  (* ^ bit xor        *)
  | BitAndOp  (* & bit and        *)
  | BitOrOp   (* | bit or         *)
  | ShlOp     (* << shift left    *)
  | ShrOp     (* >> shift right   *) *)
  | EqOp      (* == equality      *)
  | LtOp      (* < less than      *)
  | LeOp      (* <= less than or equal to *)
(* | NeOp      (* != not equal to  *)
  | GeOp      (* >= greater than or equal to *)
  | GtOp      (* > greater than   *) *)
  | OffsetOp  (* . offset         *)
  .

(** Base values *)
Notation fname := string (only parsing).
Inductive scalar :=
  ScPoison | ScInt (n: Z) | ScPtr (l: loc) (tg: tag) | ScFnPtr (fn: fname) | ScCallId (c : call_id).
Bind Scope sc_scope with scalar.
Definition value := list scalar.
Bind Scope val_scope with value.

(** Expressions *)
(* We never induct on this type since it uses [list].
So disable schemes since we do not need them, but generating them causes warnings. *)
#[schemes=none]
Inductive expr :=
(* base values *)
| Val (v : value)
(* variables *)
| Var (x : string)
(* function calls *)
| Call (e1 : expr) (e2 : expr)  (* Call a function through a FnPtr `e1` with argument `e2` *)
| InitCall                      (* Initializing a stack frame and return the ID *)
| EndCall (e : expr)               (* End the current call with ID `e` *)
(* operations on value *)
| Proj (e1 e2 : expr)             (* Projection out sub value *)
| Conc (e1 e2 : expr)             (* concatenate lists of scalars *)
(* bin op *)
| BinOp (op : bin_op) (e1 e2 : expr)
(* place operation *)
| Place (l : loc) (tg : tag) (T : type)
                                  (* A place is a tagged pointer: every access
                                     to memory revolves around a place. *)
| Deref (e : expr) (T : type)       (* Deference a pointer `e` into a place
                                     presenting the location that `e` points to.
                                     The location has type `T`. *)
| Ref (e : expr)                   (* Turn a place `e` into a pointer value. *)
(* | Field (e: expr) (path: list nat)(* Create a place that points to a component
                                     of the place `e`. `path` defines the path
                                     through the type. *) *)
(* mem op *)
| Copy (e : expr)                 (* Read from the place `e` *)
| Write (e1 e2 : expr)             (* Write the value `e2` to the place `e1` *)
| Alloc (T : type)                 (* Allocate a place of type `T` *)
| Free (e : expr)                 (* Free the place `e` *)
(* atomic mem op *)
(* | CAS (e0 e1 e2 : expr) *)     (* CAS the value `e2` for `e1` to the place `e0` *)
(* | AtomWrite (e1 e2: expr) *)
(* | AtomRead (e: expr) *)
(* retag *) (* Retag the memory pointed to by `e1` of type (Reference pk T) with
  retag kind `kind`, for call_id `e2`. *)
| Retag (e1 : expr) (e2 : expr) (pk : pointer_kind) (T : type) (kind : retag_kind)
(* let binding *)
| Let (x : binder) (e1 e2: expr)
(* case *)
| Case (e : expr) (el: list expr)
(* concurrency *)
| Fork (e : expr)
(* While *)
| While (e1 e2 : expr)
(* observable behavior *)
(* | SysCall (id: nat) *)
.

Bind Scope expr_scope with expr.

Arguments Val _%_E.
(* Arguments App _%_E _%_E. *)
Arguments BinOp _ _%_E _%_E.
Arguments Call _%_E _%_E.
Arguments EndCall _%_E.
Arguments Proj _%_E _%_E.
Arguments Conc _%_E _%_E.
Arguments Deref _%_E _%_T.
Arguments Ref _%_E.
(* Arguments Field _%_E _. *)
Arguments Copy _%_E.
Arguments Write _%_E _%_E.
Arguments Alloc _%_T.
Arguments Free _%_E.
(* Arguments CAS _%_E _%_E _%_E. *)
(* Arguments AtomWrite _%_E _%_E. *)
(* Arguments AtomRead _%_E. *)
Arguments Retag _%_E _%_E _ _ _.
Arguments Let _%_binder _%_E _%_E.
Arguments Case _%_E _%_E.
Arguments While _%_E _%_E.
(* Arguments Fork _%_E. *)

(** Closedness *)
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Val _ | Place _ _ _ | Alloc _ | InitCall (* | SysCall _ *) => true
  | Var x => bool_decide (x ∈ X)
  | BinOp _ e1 e2 | (* AtomWrite e1 e2 | *) Write e1 e2 | While e1 e2 
      | Conc e1 e2 | Proj e1 e2 | Call e1 e2 | Retag e1 e2 _ _ _ => is_closed X e1 && is_closed X e2
  | Let x e1 e2 => is_closed X e1 && is_closed (x :b: X) e2
  | Case e el 
      => is_closed X e && forallb (is_closed X) el
  | Fork e | Copy e  | Deref e _ | Ref e (* | Field e _ *)
      | Free e | EndCall e (* | AtomRead e | Fork e *)
      => is_closed X e
  (* | CAS e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2 *)
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
#[global]
Hint Mode Closed + + : typeclass_instances.
Global Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Global Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

(** Irreducible (language values) *)
Inductive result :=
| ValR (v : value)
| PlaceR (l : loc) (tg : tag) (T : type)
.
Bind Scope result_scope with result.

Definition of_result (v : result) : expr :=
  match v with
  | ValR v => Val v
  | PlaceR l tag T => Place l tag T
  end.

Definition to_result (e : expr) : option result :=
  match e with
  | Val v => Some (ValR v)
  | Place l T tag => Some (PlaceR l T tag)
  | _ => None
  end.

Definition to_value (e : expr) : option value :=
  match e with
  | Val v => Some v
  | _ => None
  end.
Definition of_value (v : value) : expr := Val v.

Definition to_fname (e : expr) : option fname :=
  match to_value e with
  | Some ([ScFnPtr fn]) => Some fn
  | _ => None
  end.
Definition of_fname (fn : fname) := Val $ [ScFnPtr fn].

Definition of_call f r := Call (of_fname f) (of_result r).
Definition to_call (e : expr) : option (fname * result) :=
  match e with
  | Call e1 e2 =>
      match to_fname e1 with
      | Some fn => option_map (pair fn) (to_result e2)
      | _ => None
      end
  | _ => None
  end.


Lemma is_Some_to_value_result (e: expr):
  is_Some (to_value e) → is_Some (to_result e).
Proof. destruct e; simpl; intros []; naive_solver. Qed.

Lemma Val_to_value e v : to_value e = Some v → Val v = e.
Proof. destruct e; try discriminate. intros [= ->]. done. Qed.

Lemma list_Forall_to_value (es: list expr):
  Forall (λ ei, is_Some (to_value ei)) es ↔ (∃ vs, es = Val <$> vs).
Proof.
  induction es as [ | e es IH]; split.
  - intros _. exists []. done.
  - intros _. constructor.
  - intros [[v EQv] [vs EQvs]%IH]%Forall_cons. exists (v::vs).
    simpl. f_equal; last done.
    erewrite Val_to_value; done.
  - intros [[|v vs] EQ]; first discriminate.
    move:EQ=> [= -> EQ]. constructor; first by eauto.
    apply IH. eexists. done.
Qed.


(** Main state: a heap of scalars. *)
Definition mem := gmap loc scalar.

(** Internal events *)
Inductive event :=
| AllocEvt (l : loc) (lbor : tag) (T : type)
| DeallocEvt (l : loc) (lbor: tag) (T : type)
| CopyEvt (l : loc) (lbor : tag) (T : type) (v : value)
| FailedCopyEvt (l : loc) (lbor : tag) (T : type)
| WriteEvt (l : loc) (lbor : tag) (T : type) (v : value)
| InitCallEvt (c : call_id)
| EndCallEvt (c : call_id)
| RetagEvt (l : loc) (otag ntag : tag) (pk : pointer_kind) (T : type) (kind : retag_kind) (c : call_id)
(* | SysCallEvt (id: nat) *)
| SilentEvt.
