From iris.prelude Require Import prelude options.

Implicit Type (V W X Y:Type).

(** General Preliminaries *)

#[global]
Arguments option_bind {_} {_} _ _.
#[global]
Arguments option_join {_} _.

Lemma option_bind_inv {A B} (f : A → option B) x y :
  option_bind f x = Some y →
  ∃ k, x = Some k ∧ f k = Some y.
Proof.
  destruct x as [x|]; last done.
  by exists x.
Qed.


(* Generic tree *)
(* NOTE: we are using the "tilted" representation of n-ary trees
   where the binary children are the next n-ary sibling and the first n-ary child.
   This is motivated by the much nicer induction principles we get,
   but requires more careful definition of the parent-child relationship.
   In any case anything we do here is abstracted away as far as the more
   high-level principles are concerned.
   *)
Inductive tree X :=
  | empty
  | branch (data:X) (sibling child:tree X)
  .
(* EXAMPLE:

   the n-ary tree of width 4 and height 2

   x
   |- y1
   |- y2
   |- y3
   |- y4

   is encoded by a binary tree of height 5

   branch x
    empty
    (branch y1
      (branch y2
        (branch y3
          (branch y4 empty empty)
          empty
        empty
      empty
 *)

Arguments empty {X}.
Arguments branch {X} data sibling child.
Definition tbranch X : Type := X * tree X * tree X.

Definition of_branch {X} (br:tbranch X)
  : tree X :=
  let '(root, lt, rt) := br in branch root lt rt.

Definition root {X} (br:tbranch X)
  : X := let '(r, _, _) := br in r.

(** The main traversal operation is the folding. *)

Definition fold_subtrees {X Y} (unit:Y) (combine:tbranch X -> Y -> Y -> Y)
  : tree X -> Y := fix aux tr : Y :=
  match tr with
  | empty => unit
  | branch data sibling child => combine (data, sibling, child) (aux sibling) (aux child)
  end.

Definition fold_nodes {X Y} (unit:Y) (combine:X -> Y -> Y -> Y)
  : tree X -> Y := fold_subtrees unit (fun subtree sibling child => combine (root subtree) sibling child).

(** From which we define [map] as is standard. *)

Definition map_nodes {X Y} (fn:X -> Y) : tree X -> tree Y :=
  fold_nodes empty (compose branch fn).

Definition join_nodes {X}
  : tree (option X) -> option (tree X) := fix aux tr {struct tr} : option (tree X) :=
  match tr with
  | empty => Some empty
  | branch data sibling child =>
    data ← data;
    sibling ← aux sibling;
    child ← aux child;
    Some $ branch data sibling child
  end.

(** Quantifiers over trees, universal and existential.
    All of them are of course decidable. *)

Definition every_subtree {X} (prop:tbranch X -> Prop) (tr:tree X)
  := fold_subtrees True (fun sub lt rt => prop sub /\ lt /\ rt) tr.
Global Instance every_subtree_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (every_subtree prop tr).
Proof. intro. induction tr; solve_decision. Defined.

Definition exists_subtree {X} (prop:tbranch X -> Prop) (tr:tree X)
  := fold_subtrees False (fun sub lt rt => prop sub \/ lt \/ rt) tr.
Global Instance exists_subtree_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (exists_subtree prop tr).
Proof. intro. induction tr; solve_decision. Defined.

Definition every_node {X} (prop:X -> Prop) (tr:tree X) := fold_nodes True (fun data lt rt => prop data /\ lt /\ rt) tr.
Global Instance every_node_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (every_node prop tr).
Proof. intro. induction tr; solve_decision. Defined.

Definition exists_node {X} (prop:X -> Prop) (tr:tree X) := fold_nodes False (fun data lt rt => prop data \/ lt \/ rt) tr.
Global Instance exists_node_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (exists_node prop tr).
Proof. intro. induction tr; solve_decision. Defined.


(** Alternative to a quantifier, we can state exactly how many nodes
    satisfy a certain property. From this we derive unique existential quantification. *)
Definition count_nodes {X} (prop:X -> bool) :=
  fold_nodes 0 (fun data lt rt => (if prop data then 1 else 0) + lt + rt).

(* As a consequence of the representation, strict children are all
   the nodes from the right subtree. *)
Definition exists_strict_child {X} (prop:X -> Prop)
  : tbranch X -> Prop := fun '(_, _, child) => exists_node prop child.
Global Instance exists_strict_child_dec {X} prop (tr:tbranch X) :
  (forall u, Decision (prop u)) -> Decision (exists_strict_child prop tr).
Proof. intro. solve_decision. Defined.

Definition empty_children {X} (tr:tbranch X)
  : Prop :=
  let '(_, _, children) := tr in
  children = empty.

(** Other main tree operation is insertion.
    We use a somewhat nonstandard definition in which insertion occurs
    as a child of every node that satisfies a certain property.
    You will need quantifiers about the existence of nodes that satisfy
    [search_dec] if you want to make sure that the node is actually inserted. *)
Definition insert_child_at {X} (tr:tree X) (ins:X) (search:X -> Prop) {search_dec:forall x, Decision (search x)} : tree X :=
  (fix aux tr : tree X :=
    match tr with
    | empty => empty
    | branch data sibling child =>
      let sibling := aux sibling in
      let child := aux child in
      if decide (search data)
      then branch data sibling (branch ins child empty)
      else branch data sibling child
    end
  ) tr.

Definition fold_siblings {X Y} (empty:Y) (fn : X -> Y -> Y) (tr : tree X) : Y :=
  fold_nodes empty (λ this siblings _, fn this siblings) tr.

(** Immediate children are a bit more tricky to reason about.
    They are the entire leftmost *branch* of the right subtree. *)
Fixpoint fold_immediate_children_at {X Y} (prop:X -> bool) (empty:Y) (fn : X -> Y -> Y) (tr : tree X) : list Y :=
  match tr with empty => nil
    | branch x tl tr => (if prop x then [fold_siblings empty fn tr] else nil) ++
            fold_immediate_children_at prop empty fn tl ++ fold_immediate_children_at prop empty fn tr end.

Definition exists_sibling {X} (prop:X -> Prop) :=
  fold_siblings False (fun data lt => prop data \/ lt).
Global Instance exists_sibling_dec {X} prop (tr:tree X) : (forall x, Decision (prop x)) -> Decision (exists_sibling prop tr).
Proof. intro. induction tr; solve_decision. Defined.
Definition exists_immediate_child {X} (prop:X -> Prop)
  : tbranch X -> Prop := fun '(_, _, child) => exists_sibling prop child.
Global Instance exists_immediate_child_dec {X} prop (tr:tbranch X) :
  (forall u, Decision (prop u)) -> Decision (exists_immediate_child prop tr).
Proof. intro. solve_decision. Defined.

