(** Core language definitions.
  This defines most of the low level stuff, starting at "what is a tag"
  up to the inductive definition of borrow events.
  This does *not* include nontrivial computations about objects of the language,
  which are mostly in [bor_semantics.v].
  Trivial lemmas (decidability/countability instances and easy conversions)
  are included here, but overall most lemmas should be kept to files such as [bor_lemmas.v].

  This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From stdpp Require Export countable binders gmap.
From iris.prelude Require Import prelude options.

(*Global Open Scope general_if_scope.*)
From simuliris.tree_borrows Require Export locations tree.

Declare Scope expr_scope.
Declare Scope val_scope.
Declare Scope sc_scope.
Declare Scope result_scope.
Declare Scope pointer.

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
Notation tag := nat (only parsing).

(* Whether a type contains interior mutability.
   This is only relevant for [Reserved] and appears in the state machine
   because some transitions depend on interior mutability. *)
Inductive interior_mut := InteriorMut | TyFrz.
Global Instance interior_mut_eq_dec : EqDecision interior_mut.
Proof. solve_decision. Defined.
Global Instance interior_mut_countable : Countable interior_mut.
Proof.
  refine (inj_countable
    (λ m, match m with
           | InteriorMut => true
           | TyFrz => false
           end)
    (λ b, Some match b with
           | true => InteriorMut
           | false => TyFrz
           end)
    _); by intros [].
Qed.

(* Whether a [Reserved] tag is also conflicted. *)
Inductive res_conflicted := ResConflicted | ResActivable.
Global Instance res_conflicted_eq_dec : EqDecision res_conflicted.
Proof. solve_decision. Defined.
Global Instance res_conflicted_countable : Countable res_conflicted.
Proof.
  refine (inj_countable
    (λ m, match m with
           | ResConflicted => true
           | ResActivable => false
           end)
    (λ b, Some match b with
           | true => ResConflicted
           | false => ResActivable
           end)
    _); by intros [].
Qed.

(* [permission] is the lowest level of the state machine.
   This is _not yet_ the per-location data, that would be [lazy_permission].
   We will sometimes call "permission" something that in reality is a
   [lazy_permission]. *)
Inductive permission :=
  | Cell
  | Reserved (confl:res_conflicted)
  | ReservedIM
  | Active
  | Frozen
  | Disabled.

Global Instance permission_eq_dec : EqDecision permission.
Proof. solve_decision. Defined.
Global Instance permission_countable : Countable permission.
Proof.
  refine (inj_countable
    (λ p,
      match p with
      | Cell => inl 4
      | Reserved c => inr c
      | ReservedIM => inl 3
      | Active => inl 0 | Frozen => inl 1 | Disabled => inl 2
      end)
    (λ s,
      Some match s with
      | inl 4 => Cell
      | inr c => Reserved c
      | inl 3 => ReservedIM
      | inl 0 => Active | inl 1 => Frozen | inl _ => Disabled
      end) _); by intros [].
Qed.

(* Strong/weak protectors are a distinction that is necessary because
   of [Box], because even though [Box] is protected, it needs to allow deallocation.
   We will not really consider optimizations where this distinction is important,
   but for completeness we do distinguish two kinds of protectors. *)
Inductive prot_strong :=
  | ProtStrong
  | ProtWeak
  .

Global Instance prot_strong_eq_dec : EqDecision prot_strong.
Proof. solve_decision. Defined.
Global Instance prot_strong_countable : Countable prot_strong.
Proof.
  refine (inj_countable'
    (λ p:prot_strong, if p then true else false)
    (λ b:bool, if b then ProtStrong else ProtWeak) _); by intros [].
Qed.

(* A protector. Note that while we say a tag "has a protector" when it is protected,
   this development will often call "protector" a variable of type [option protector]
   because unlike a [protector], all tags have one. *)
Record protector := mkProtector {
  strong : prot_strong; (* [ProtWeak] for [Box]es, [ProtStrong] for everything else *)
  call : call_id; (* Function call id that the tag is an argument of *)
}.
Global Instance protector_eq_dec : EqDecision protector.
Proof. solve_decision. Defined.
Global Instance protector_countable : Countable protector.
Proof.
  refine (inj_countable'
    (λ p:protector, (p.(strong), p.(call)))
    (λ t, {| strong:=t.1; call:=t.2 |}) _); by intros [].
Qed.

(* Boolean flag that records if a permission has been initialized.
   A permission starts uninitialized and becomes permanently initialized on the
   first child access. See [bor_semantics.v]'s [requires_init]. *)
Inductive perm_init :=
  | PermInit
  | PermLazy
  .

Global Instance perm_init_eq_dec : EqDecision perm_init.
Proof. solve_decision. Defined.

(* Initialized status is irreversible. *)
Definition most_init p p' :=
  match p with
  | PermInit => PermInit
  | PermLazy => p'
  end.

(* The true per-location data is a permission *and* an initialized status. *)
Record lazy_permission := mkPerm {
  initialized : perm_init;
  perm        : permission;
}.
Global Instance lazy_perm_eq_dec : EqDecision lazy_permission.
Proof. solve_decision. Defined.

(* Permissions for one tag. This is most of the available per-tag-per-allocation data. *)
Definition permissions := gmap Z lazy_permission.

(* Data associated with one tag *)
(* Note: this is a substructure of the miri "Node", as it doesn't include the
   pointers that impose the structure of the tree.
   In this development we instead define the tree structure using the [tree] type. *)
Record item := mkItem {
  (* Metadata determined on item creation *)
  itag  : tag;
  iprot : option protector;
  initp : permission;
  (* Most of the data (and all of the modifiable data) is here. *)
  iperm : permissions;
}.
Global Instance item_eq_dec : EqDecision item.
Proof. solve_decision. Defined.

Definition item_lookup (it : item) (l : Z) :=
  default (mkPerm PermLazy it.(initp)) (it.(iperm) !! l).

(* Per-allocation borrow data *)
Definition trees := gmap block (tree item).

(** Retag kinds *)
Inductive retag_kind := FnEntry | Default.

(** Language base constructs *)

(** Unary/Binary ops *)
Inductive bin_op :=
  | AddOp     (* + addition       *)
  | SubOp     (* - subtraction    *)
  | EqOp      (* == equality      *)
  | LtOp      (* < less than      *)
  | LeOp      (* <= less than or equal to *)
  | OffsetOp  (* . offset         *)
  .

(** Base values *)
Notation fname := string (only parsing).
Inductive scalar :=
  ScPoison | ScInt (n: Z) | ScPtr (l: loc) (tg: tag) | ScFnPtr (fn: fname) | ScCallId (c : call_id).
Bind Scope sc_scope with scalar.
Definition value := list scalar.
Bind Scope val_scope with value.

Inductive access_kind := AccessRead | AccessWrite.
(* Implicit accesses inserted on function exit are not visible to children *)
Inductive access_visibility := VisibleAll | OnlyNonChildren.

(* The state machine only cares about Foreign vs Child.
   The invariants need more fine-grained relationships between tags.
   We use this two-layer representation so that things compute better. *)
Inductive immediaity := Immediate | FurtherAway.
Inductive foreign_rel_pos := Parent (direct:immediaity) | Cousin.
Inductive child_rel_pos := Strict (direct:immediaity) | This.
Inductive rel_pos := Foreign (pos : foreign_rel_pos) | Child (pos : child_rel_pos).

Global Instance access_kind_eq_dec : EqDecision access_kind.
Proof. solve_decision. Qed.
Global Instance access_visibility_eq_dec : EqDecision access_visibility.
Proof. solve_decision. Qed.
Global Instance immediaity_eq_dec : EqDecision immediaity.
Proof. solve_decision. Qed.
Global Instance foreign_rel_pos_eq_dec : EqDecision foreign_rel_pos.
Proof. solve_decision. Qed.
Global Instance child_rel_pos_eq_dec : EqDecision child_rel_pos.
Proof. solve_decision. Qed.
Global Instance rel_pos_eq_dec : EqDecision rel_pos.
Proof. solve_decision. Qed.

Global Instance access_kind_countable : Countable access_kind.
Proof.
  refine (inj_countable
    (λ m, match m with
           | AccessRead => true
           | AccessWrite => false
           end)
    (λ b, Some match b with
           | true => AccessRead
           | false => AccessWrite
           end)
    _); by intros [].
Qed.

Inductive pointer_kind := Box | MutRef | ShrRef.
Global Instance pointer_kind_eq_dec : EqDecision pointer_kind.
Proof. solve_decision. Defined.
Global Instance pointer_kind_countable : Countable pointer_kind.
Proof.
  refine (inj_countable
    (λ m, match m with
           | Box => inl ()
           | MutRef => inr (inl ())
           | ShrRef => inr (inr ())
           end)
    (λ b, Some match b with
           | inl _ => Box
           | inr (inl _) => MutRef
           | inr (inr _) => ShrRef
           end)
    _); by intros [].
Qed.


(** Expressions *)
(* We never induct on this type since it uses [list.]
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
| Place (l : loc) (tg : tag) (sz : nat)
                                  (* A place is a tagged pointer: every access
                                     to memory revolves around a place. *)
| Deref (e : expr) (sz : nat)       (* Deference a pointer `e` into a place
                                     presenting the location that `e` points to.
                                     The location has the kind and size of `ptr`. *)
| Ref (e : expr)                   (* Turn a place `e` into a pointer value. *)
(* mem op *)
| Copy (e : expr)                 (* Read from the place `e` *)
| Write (e1 e2 : expr)             (* Write the value `e2` to the place `e1` *)
| Alloc (sz : nat)                 (* Allocate a place of type `T` *)
| Free (e : expr)                 (* Free the place `e` *)
(* retag *) (* Retag the memory pointed to by `e1` with
  retag kind `kind`, for call_id `e2`. The new pointer should have pointer kind pk. *)
| Retag (e1 : expr) (e2 : expr) (pk : pointer_kind) (im : interior_mut) (sz : nat) (kind : retag_kind)
(* let binding *)
| Let (x : binder) (e1 e2: expr)
(* case *)
| Case (e : expr) (el: list expr)
(* concurrency *)
| Fork (e : expr)
(* While *)
| While (e1 e2 : expr)
.

Bind Scope expr_scope with expr.

Arguments Val _%_E.
Arguments BinOp _ _%_E _%_E.
Arguments Call _%_E _%_E.
Arguments EndCall _%_E.
Arguments Proj _%_E _%_E.
Arguments Conc _%_E _%_E.
Arguments Deref _%_E _%_nat.
Arguments Ref _%_E.
Arguments Copy _%_E.
Arguments Write _%_E _%_E.
Arguments Alloc _%_nat.
Arguments Free _%_E.
Arguments Retag _%_E _%_E _%_nat _.
Arguments Let _%_binder _%_E _%_E.
Arguments Case _%_E _%_E.
Arguments While _%_E _%_E.

(** Closedness *)
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Val _ | Place _ _ _ | Alloc _ | InitCall => true
  | Var x => bool_decide (x ∈ X)
  | BinOp _ e1 e2 | Write e1 e2 | While e1 e2 
      | Conc e1 e2 | Proj e1 e2 | Call e1 e2 | Retag e1 e2 _ _ _ _ => is_closed X e1 && is_closed X e2
  | Let x e1 e2 => is_closed X e1 && is_closed (x :b: X) e2
  | Case e el 
      => is_closed X e && forallb (is_closed X) el
  | Fork e | Copy e | Deref e _ | Ref e
      | Free e | EndCall e
      => is_closed X e
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
| PlaceR (l : loc) (tg : tag) (sz : nat)
.
Bind Scope result_scope with result.

Definition of_result (v : result) : expr :=
  match v with
  | ValR v => Val v
  | PlaceR l tag ptr => Place l tag ptr
  end.

Definition to_result (e : expr) : option result :=
  match e with
  | Val v => Some (ValR v)
  | Place l tag ptr => Some (PlaceR l tag ptr)
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

(** Main state: a heap of scalars, each with an associated lock to detect data races. *)
Definition mem := gmap loc scalar.

(* Arbitrary borrow events. *)
Inductive event :=
| AllocEvt (alloc : block) (lbor : tag) (range : Z * nat)
| DeallocEvt (alloc : block) (lbor: tag) (range : Z * nat)
| CopyEvt (alloc : block) (lbor : tag) (range : Z * nat) (v : value)
| WriteEvt (alloc : block) (lbor : tag) (range : Z * nat) (v : value)
| InitCallEvt (c : call_id)
| EndCallEvt (c : call_id)
| RetagEvt (alloc : block) (range : Z * nat) (otag ntag : tag) (pk : pointer_kind) (im : interior_mut) (c : call_id) (rk : retag_kind)
| SilentEvt.

