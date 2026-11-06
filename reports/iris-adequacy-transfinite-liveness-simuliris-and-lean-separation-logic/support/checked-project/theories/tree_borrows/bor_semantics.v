(** Tree Borrows state machine and tree manipulation.
   This file defines the semantics of the operations of Tree Borrows.
   It more or less replicates
   - https://github.com/rust-lang/miri/blob/master/src/borrow_tracker/tree_borrows/mod.rs
   - https://github.com/rust-lang/miri/blob/master/src/borrow_tracker/tree_borrows/perms.rs
   (small differences come mostly from the underlying implementation of trees)

   Trivial lemmas are provided (e.g. countability of objects and decidability
   of properties), but the more involved lemmas are mostly in [bor_lemmas.v].

   This file has been adapted from [theories/stacked_borrows/bor_semantics.v],
   itself adapted from the original Stacked Borrows development available at
   https://gitlab.mpi-sws.org/FP/stacked-borrows.
*)

From Equations Require Import Equations.
From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.

From simuliris.tree_borrows Require Export lang_base notation tree locations.

(*** TREE BORROWS SEMANTICS ---------------------------------------------***)

Implicit Type (c:call_id) (cids:call_id_set).
Implicit Type (blk:block) (n sz:nat) (z:Z) (range:Z * nat).
Implicit Type (trs:trees) (t:tag).

Definition range'_contains (r:range') (l:loc') : Prop :=
  (r.1 ≤ l)%Z /\ (l < r.1 + r.2)%Z.
Global Instance decision_range'_contains (r:range') (l:loc') : Decision (range'_contains r l).
Proof. solve_decision. Defined.

Definition range_contains (r:range) (l:loc) : Prop :=
  r.1 = l.1 /\ range'_contains r.2 l.2.
Global Instance decision_range_contains (r:range) (l:loc) : Decision (range_contains r l).
Proof. solve_decision. Defined.

Lemma range'_contains_excludes_equal range z' :
  let '(z, sz) := range in
  range'_contains (z, S sz) z' -> ~(range'_contains ((z + 1)%Z, sz) z') -> z = z'.
Proof.
  destruct range.
  intros Contains Excludes.
  unfold range'_contains in *; simpl in *.
  lia.
Qed.

(* Applies a function [option X -> option X] to a single location in memory.
                                   ^^^^^^ computation may trigger UB.
                       ^^^^^^ location may be uninitialized *)
Definition mem_apply_loc {X} (fn : option X -> option X) z
  : gmap loc' X -> option (gmap loc' X) := fun map =>
    new ← fn (map !! z);
    Some (<[z := new]> map).

(* Applies a function to a range of memory.
   The whole operation is UB iff any of the per-location operations are UB.
   If the set of locations you want to access cannot be expressed as a range,
   see [mem_fold_apply]. *)
Fixpoint mem_apply_locs {X} (fn:option X -> option X) z sz
  {struct sz} : gmap loc' X -> option (gmap loc' X) := fun map =>
  match sz with
  | O => Some map
  | S sz' =>
      newmap ← mem_apply_loc fn z map;
      mem_apply_locs fn (z + 1)%Z sz' newmap
  end.

(* Collect the set of locations that satisfy a predicate.
   This is useful when we exit a function and need to perform an implicit
   access to all initialized locations. *)
Definition mem_enumerate_sat {X Y} (fn : X -> option Y)
  : gmap loc' X -> gmap Z Y :=
  map_fold (fun k v acc =>
    (match fn v with Some vv => <[ k := vv ]> acc | _ => acc end)
  ) ∅ .

(* Apply a function to all the locations passed as a list.
   The whole operation is UB iff any of the per-location operations are UB.
   If the set of locations you want to access can be expressed as a range,
   see [mem_apply_loc] which might be easier to reason about. *)
Fixpoint mem_fold_apply {X} (fn : option X -> option X) locs
  : gmap loc' X -> option (gmap loc' X) := fun map =>
  match locs with
  | [] => Some map
  | z::locs' =>
      newmap ← mem_apply_loc fn z map;
      mem_fold_apply fn locs' newmap
  end.

(* Part of the API for permission update. All memory accesses have an effect
   on the permissions that can be expressed by a faillible function from
   (optionally uninitialized) permissions to Parentpermissions lifted to the entire
   memory by means of [mem_apply_range']. *)
Definition mem_apply_range' {X} (fn:option X -> option X) (r:range')
  : gmap loc' X -> option (gmap loc' X) := mem_apply_locs fn r.1 r.2.

(* The behavior of [mem_apply_range'] is completely specified by
   [mem_apply_range'_spec] and [mem_apply_range'_success_condition].

   This one states what happens to each location inside aund outside of the
   range of the access. *)
Lemma mem_apply_range'_spec {X} fn r z' :
  forall (map newmap: gmap loc' X),
  (mem_apply_range' fn r map = Some newmap) ->
  if (decide (range'_contains r z'))
    (* Locations in range have been updated by [fn] *)
    then exists val, newmap !! z' = Some val /\ fn (map !! z') = Some val
    (* Locations out of range are unchanged *)
    else newmap !! z' = map !! z'.
Proof.
  unfold mem_apply_range'.
  destruct r as [z sz].
  generalize dependent z'.
  generalize dependent z.
  induction sz as [|sz IHsz]; intros z z' map newmap MemForeach.
  - unfold mem_apply_locs in MemForeach. injection MemForeach; intro; subst.
    destruct (decide (range'_contains (z, 0) z')) as [Contains | NotContains]; auto.
    unfold range'_contains in Contains; simpl in Contains. lia.
  (* Case 1: the item is at the beginning of the range.
     -> it will be unchanged by the aux function and written by the current one *)
  - destruct (decide (z = z')) as [Eql | Neq].
    + subst. assert (range'_contains (z', S sz) z') as ContainsS by (unfold range'_contains; simpl; lia).
      decide (decide (range'_contains (z', S sz) z')) with ContainsS.
      simpl in MemForeach.
      unfold mem_apply_loc in MemForeach.
      destruct (fn (map !! z')) as [x|]; simpl in *; [|inversion MemForeach].
      destruct (mem_apply_locs fn (z' + 1) sz _) eqn:Rec; [|inversion MemForeach]; simpl in *.
      injection MemForeach; intro; subst.
      exists x; split; auto.
      pose proof (IHsz _ z' _ _ Rec) as Unchanged.
      assert (~range'_contains ((z' + 1)%Z, sz) z') by (unfold range'_contains; simpl; lia).
      destruct (decide (range'_contains ((z'+1)%Z, sz) z')); [contradiction|].
      rewrite Unchanged.
      apply lookup_insert_eq.
  (* Case 2: the item is in the middle of the range or completely outside.
     -> the map we get from the aux call is not altered on the location that matters *)
    + simpl in MemForeach.
      unfold mem_apply_loc in MemForeach.
      destruct (fn (map !! z)) eqn:Fn; simpl in *; [|inversion MemForeach].
      destruct (mem_apply_locs fn (z + 1) sz _) eqn:Rec; simpl in *; [|inversion MemForeach].
      specialize (IHsz _ z' _ _ Rec).
      * destruct (decide (range'_contains ((z + 1)%Z, sz) z')) as [Contains' | NotContains'].
        all: destruct (decide (range'_contains (z, S sz) z')) as [ContainsS' | NotContainsS'].
        (* bad range *)
        all: try (exfalso; unfold range'_contains in *; simpl in *; lia).
        (* good case *)
        -- destruct IHsz as [x0 [z'val fnval]].
           injection MemForeach; intros; subst.
           exists x0; split; auto.
           rewrite lookup_insert_ne in fnval; auto.
        -- injection MemForeach; intros; subst.
           rewrite lookup_insert_ne in IHsz; auto.
Qed.

(* [mem_apply_range'] expects an [option lazy_permission -> option lazy_permission].
   In practice we prefer expressing the state machine as [lazy_permission -> option lazy_permission].
   The second can easily be lifted to the first when given the default permission
   (stored in [item]'s [initp] field). *)
Definition permissions_apply_range' (pdefault:lazy_permission) (range:range')
  (f:lazy_permission -> option lazy_permission)
  : permissions -> option permissions := fun ps =>
  mem_apply_range'
    (fun oldp => f (default pdefault oldp))
    range ps.

(* Special instance of [mem_apply_range'] when the function is infaillible. *)
Lemma mem_apply_range'_defined_isSome {X} (map:gmap Z X) (fn:option X -> X) :
  forall range, is_Some (mem_apply_range' (fun x => Some (fn x)) range map).
Proof.
  intros range; destruct range as [z sz].
  generalize dependent z.
  generalize dependent map.
  unfold mem_apply_range'; simpl.
  induction sz as [|sz IHsz]; intros map z; simpl in *.
  - exists map; auto.
  - destruct (IHsz (<[z := fn (map !! z)]> map) (z+1)%Z) as [res H].
    rewrite H; simpl.
    exists res.
    reflexivity.
Qed.

Definition mem_apply_range'_defined {X} (fn:option X -> X) range
  : gmap Z X -> gmap Z X := fun map =>
  is_Some_proj (mem_apply_range'_defined_isSome map fn range).

Lemma is_Some_proj_extract {X} (ox:option X) (sx:is_Some ox) y :
  is_Some_proj sx = y -> ox = Some y.
Proof.
  destruct ox; simpl in *.
  - intro; subst; reflexivity.
  - inversion sx as [? H]; inversion H.
Qed.

Lemma mem_apply_range'_defined_spec {X} fn r z :
  forall (map newmap: gmap Z X),
  (mem_apply_range'_defined fn r map = newmap) ->
  if (decide (range'_contains r z))
    then exists val, newmap !! z = Some val /\ fn (map !! z) = val
    else newmap !! z = map !! z.
Proof.
  intros map newmap MemForeach.
  unfold mem_apply_range'_defined in MemForeach.
  pose proof (is_Some_proj_extract _ _ _ MemForeach) as Foreach.
  pose proof (mem_apply_range'_spec _ _ z _ _ Foreach) as Spec.
  destruct (decide (range'_contains _ _)).
  - destruct Spec as [x [Mapz Appfn]].
    exists x; split; auto. injection Appfn; tauto.
  - assumption.
Qed.

Lemma mem_apply_range'_defined_lookup_Some {X} fn r (z:Z) (map : gmap Z X) x :
  (mem_apply_range'_defined fn r map) !! z = Some x →
  (range'_contains r z ∧ x = fn (map !! z)) ∨
  (¬range'_contains r z ∧ map !! z = Some x).
Proof.
  intros HH. opose proof (@mem_apply_range'_defined_spec X fn r z map _ _) as Hpp; first done.
  destruct decide.
  - left. split; first done. destruct Hpp as (xx&H1&H2). rewrite H2. congruence.
  - right. split; first done. rewrite -HH Hpp //.
Qed.

(** CORE SEMANTICS *)

Notation IsTag t := (fun it => it.(itag) = t) (only parsing).

Definition HasRootTag t : tbranch item -> Prop := fun br => IsTag t (root br).
Global Instance HasRootTag_dec t it : Decision (HasRootTag t it).
Proof. rewrite /HasRootTag. solve_decision. Defined.

Definition HasStrictChildTag t' : tbranch item -> Prop := exists_strict_child (IsTag t').
Global Instance HasStrictChildTag_dec t' tr : Decision (HasStrictChildTag t' tr).
Proof. rewrite /HasStrictChildTag. solve_decision. Defined.

Definition HasImmediateChildTag t' : tbranch item -> Prop := exists_immediate_child (IsTag t').
Global Instance HasImmediateChildTag_dec t' tr : Decision (HasImmediateChildTag t' tr).
Proof. rewrite /HasImmediateChildTag. solve_decision. Defined.

(* We define that [t] is a strict parent of [t'] when every subtree
   whose root is labeled [t] contains a strict child labeled [t'].
   When the tree is well-formed (tags are unique) and contains [t],
   this becomes equivalent to "there is a node labeled [t] with a strict
   child labeled [t']".

   WARNING: when the tree is not well-formed or does not contain the tags,
   [StrictParentChildIn] may not satisfy the axioms you expect of a parent-child
   relationship.

   Do not interpret [StrictParentChildIn t t' tr] too literally unless you know
   - [tree_unique t tr]
   - [tree_unique t' tr]

   Well-formedness will usually put you in a position where you know
   - [tree_contains t tr]
   - [tree_contains t' tr]
   - [WF : forall tg, tree_contains tg tr -> tree_unique tg tr]
   which is obviously sufficient. *)
Definition StrictParentChildIn t t' : tree item -> Prop
  := every_subtree (fun br => (IsTag t (root br)) -> (HasStrictChildTag t' br)).
Global Instance StrictParentChildIn_dec t t' tr : Decision (StrictParentChildIn t t' tr).
Proof. rewrite /StrictParentChildIn. solve_decision. Defined.

(* Reflexive closure of [StrictParentChildIn]. *)
Definition ParentChildIn t t' : tree item -> Prop
  := fun tr => t = t' \/ StrictParentChildIn t t' tr.
Global Instance ParentChildIn_dec t t' tr : Decision (ParentChildIn t t' tr).
Proof. rewrite /ParentChildIn. solve_decision. Defined.

Definition ImmediateParentChildIn t t' : tree item -> Prop
  := every_subtree (fun br => (IsTag t (root br)) -> (HasImmediateChildTag t' br)).
Global Instance ImmediateParentChildIn_dec t t' tr : Decision (ImmediateParentChildIn t t' tr).
Proof. rewrite /ImmediateParentChildIn. solve_decision. Defined.

(* Decide the relative position (parent/child/other) of two tags.
   Read this as "t1 is a `rel_dec tr t1 t2` of t2", i.e.
   `rel_dec tr t1 t2 = Child Strict` means `t1` is a strict child of `t2` in `tr`,
   `rel_dec tr t1 t2 = Foreign Cousin` means `t1` is a cousin of `t2` in `tr`.

   Naturally `Child This` and `Foreign Cousin` are symmetric,
   while `Foreign Parent` and `Child Strict`,
   because they are strict, are inverses of each other.

   Recall that we are using the toplevel distinction
   [Foreign] / [Child] so that statements compute better, and the specifics
   [Strict]/[This]/[Parent]/[Cousin] because some invariants need to be able
   to make the distinction. *)
Definition rel_dec (tr:tree item) := fun t t' =>
  if decide (ParentChildIn t' t tr)
  then Child (if decide (ParentChildIn t t' tr) then This else Strict (if decide (ImmediateParentChildIn t' t tr) then Immediate else FurtherAway))
  else Foreign (if decide (ParentChildIn t t' tr) then Parent (if decide (ImmediateParentChildIn t t' tr) then Immediate else FurtherAway) else Cousin).

Definition rel_pos_inv (r : rel_pos) : rel_pos := match r with
  Child This => Child This
| Child (Strict b) => Foreign (Parent b)
| Foreign (Parent b) => Child (Strict b)
| Foreign Cousin => Foreign Cousin end.

Lemma rel_pos_inv_inv r : rel_pos_inv (rel_pos_inv r) = r.
Proof. by destruct r as [[]|[]]. Qed.

Lemma rel_dec_flip tr t t' r : rel_dec tr t t' = r -> rel_dec tr t' t = rel_pos_inv r.
Proof. rewrite /rel_dec. do 2 destruct (decide (ParentChildIn _ _ _)); intro; subst r; simpl; rewrite ?decide_bool_decide; congruence. Qed.
Lemma rel_dec_flip2 tr t t' : rel_dec tr t t' = rel_pos_inv (rel_dec tr t' t).
Proof. by eapply rel_dec_flip. Qed.

(* These are simple properties of [rel_dec] that hold regardless of well-formedness.

   Other such properties include
   - transitivity (proven in [bor_lemmas.v] as [StrictParentChildIn_transitive]

   On the other hand some properties DO NOT HOLD WITHOUT WELL-FORMEDNESS, such as
   - cousins have disjoint children (proven in [bor_lemmas.v] as [cousins_have_disjoint_children])
   - cousins have some common ancestor (proven in [bor_lemmas.v] as [cousins_find_common_ancestor])
 *)
Lemma rel_dec_cousin_sym tr t t' : rel_dec tr t t' = Foreign Cousin -> rel_dec tr t' t = Foreign Cousin.
Proof. eapply rel_dec_flip. Qed.
Lemma rel_dec_this_sym tr t t' : rel_dec tr t t' = Child This -> rel_dec tr t' t = Child This.
Proof. eapply rel_dec_flip. Qed.
Lemma rel_dec_parent_antisym tr t t' b: rel_dec tr t t' = Foreign (Parent b) -> rel_dec tr t' t = Child (Strict b).
Proof. eapply rel_dec_flip. Qed.
Lemma rel_dec_child_antisym tr t t' b : rel_dec tr t t' = Child (Strict b) -> rel_dec tr t' t = Foreign (Parent b).
Proof. eapply rel_dec_flip. Qed.

Implicit Type (kind:access_kind) (rel:rel_pos).
Implicit Type (it:item).
Implicit Type (p1rot:option protector).

(* Tells if an access requires you to initialize the permission afterwards.
   This is exactly child accesses. *)
Definition requires_init (rel:rel_pos)
  : perm_init :=
  match rel with
  | Child _ => PermInit
  | Foreign _ => PermLazy
  end.

(* State machine without protector UB.
   Protector UB is handled later in [apply_access_perm]. *)
Definition apply_access_perm_inner (kind:access_kind) (rel:rel_pos) (isprot:bool)
  : permission -> option permission := fun perm =>
  match kind, rel with
  | AccessRead, Foreign _ =>
      (* Foreign read. Makes [Reserved] conflicted, freezes [Active]. *)
      match perm with
      | Cell => Some Cell
      | Reserved ResActivable => Some (Reserved (if isprot then ResConflicted else ResActivable))
      | Active => if isprot then
        (* So that the function is commutative on all states and not just on reachable states,
           we change the transition into [Active -> Disabled] when a protector is present.
           This happens to slightly simplify the protector check. *)
        (* This is also crucial, otherwise concurrent reads make things annoying *)
        Some Disabled else Some Frozen
      | Reserved ResConflicted | ReservedIM | Frozen | Disabled  => Some perm
      end
  | AccessWrite, Foreign _ =>
      (* Foreign write. Disables everything except interior mutable [Reserved]. *)
      match perm with
      | Cell => Some Cell
      (* NOTE: this can never happen, but having it simplifies theorems. *)
      | ReservedIM => if isprot then Some Disabled else Some $ ReservedIM
      | Disabled => Some Disabled
      | _ => Some Disabled
      end
  | AccessRead, Child _ =>
      (* Child read. Mostly noop. (not visible here: this access is [requires_init] and will have
         an effect on the [lazy_permission]). *)
      match perm with
      | Disabled => None
      | _ => Some perm
      end
  | AccessWrite, Child _ =>
      (* Child write. Activates unconflicted [Reserved]. *)
      match perm with
      | Cell => Some Cell
      | Reserved ResConflicted => if isprot then None else Some Active
      | Reserved ResActivable | ReservedIM | Active => Some Active
      | _ => None
      end
  end.

(* A protector is active when the call id it contains is currently part of
   the set of active call ids. *)
Definition call_is_active c cids := (c ∈ cids).
Global Instance call_is_active_dec c cids : Decision (call_is_active c cids).
Proof. rewrite /call_is_active. solve_decision. Defined.

Definition call_of_protector (prot:option protector) :=
  match prot with
  | Some (mkProtector _ c) => Some c
  | _ => None
  end.

Definition protector_is_for_call c prot := call_of_protector prot = Some c.
Global Instance protector_is_for_call_dec c prot : Decision (protector_is_for_call c prot).
Proof. rewrite /protector_is_for_call /call_of_protector. case_match; [case_match|]; solve_decision. Defined.

Definition protector_is_active prot cids :=
  exists c, protector_is_for_call c prot /\ call_is_active c cids.

Definition witness_protector_is_active prot cids :=
  match prot with
  | Some (mkProtector _ c) => call_is_active c cids
  | _ => False
  end.

Global Instance witness_protector_is_active_dec prot cids :
  Decision (witness_protector_is_active prot cids).
Proof.
  rewrite /witness_protector_is_active.
  case_match; [case_match|]; solve_decision.
Defined.

Lemma protector_is_active_matches_witness prot cids :
  witness_protector_is_active prot cids <-> protector_is_active prot cids.
Proof.
  rewrite /protector_is_active /witness_protector_is_active /protector_is_for_call /call_of_protector.
  split; intro Hyp.
  - destruct prot as [p|]; [destruct p as [prot call]|].
    * exists call; auto.
    * inversion Hyp.
  - destruct Hyp as [c [IsProt IsActive]].
    destruct prot as [p|]; [destruct p as [prot call]|].
    * injection IsProt; intros; subst; assumption.
    * inversion IsProt.
Defined.

Lemma decision_equiv (P Q:Prop) :
  (P <-> Q) ->
  Decision P ->
  Decision Q.
Proof.
  unfold Decision. tauto.
Defined.

Global Instance protector_is_active_dec prot cids :
  Decision (protector_is_active prot cids).
Proof.
  eapply decision_equiv; [eapply protector_is_active_matches_witness|].
  solve_decision.
Defined.

Definition protector_is_strong prot :=
  match prot with
  | Some (mkProtector weak _) => weak = ProtStrong
  | _ => False
  end.
Global Instance protector_is_strong_dec prot : Decision (protector_is_strong prot).
Proof. rewrite /protector_is_strong. try repeat case_match; solve_decision. Defined.

(* State machine including protector UB.
   After applying [apply_access_perm_inner] we still need to
   - trigger the protector if it is active and if the transition performed [_ -> Disabled]
   - update the [initialized] status of the permission. *)
Definition apply_access_perm kind rel (isprot:bool)
  : lazy_permission -> option lazy_permission := fun operm =>
  let old := operm.(perm) in
  new ← apply_access_perm_inner kind rel isprot old;
  (* can only become more initialized *)
  let new_init := (most_init operm.(initialized) (requires_init rel)) in
  validated ← if new_init then (
    (* only if the permission is initialized do we possibly trigger protector UB *)
    if isprot then (
      if new is Disabled then (
        None
      ) else Some new
    ) else Some new
  ) else Some new;
  Some $ mkPerm
    new_init
    validated.

(* The effect of an access on an item is to apply it to the permissions while
   keeping the metadata (tag, protector, default permission) unchanged. *)
Definition item_apply_access (fn : rel_pos -> bool -> lazy_permission -> option lazy_permission) cids rel range
  : item -> option item := fun it =>
  let oldps := it.(iperm) in
  let protected := bool_decide (protector_is_active it.(iprot) cids) in
  newps ← permissions_apply_range' (mkPerm PermLazy it.(initp)) range
    (fn rel protected) oldps;
  Some $ mkItem it.(itag) it.(iprot) it.(initp) newps.

(* For function exit we need to apply a transformation only to nonchildren nodes.
   This function filters out strict children to turn any function into a function
   that operates only on nonchildren. *)
Definition nonchildren_only
  (fn : rel_pos -> bool -> lazy_permission -> option lazy_permission)
  : rel_pos -> bool -> lazy_permission -> option lazy_permission := fun rel isprot perm =>
  match rel with
  | Foreign (Parent _) => Some perm
  | _ => fn rel isprot perm
  end.

(* Lift a function on nodes to a function on trees.
   Returns [None] if and only if the image by at least one of the nodes returns [None]. *)
Definition tree_apply_access
  (fn:rel_pos -> bool -> lazy_permission -> option lazy_permission)
  cids (access_tag:tag) range (tr:tree item)
  : option (tree item) :=
  let app : item -> option item := fun it => (
    item_apply_access fn cids (rel_dec tr access_tag it.(itag)) range it
  ) in
  join_nodes (map_nodes app tr).

(* Initial permissions. *)
Definition init_perms perm off sz
  : permissions := mem_apply_range'_defined (fun _ => mkPerm PermInit perm) (off, sz) ∅.

(* Initial tree is a single root whose default permission is [Active]. *)
Definition initial_item t off sz := (mkItem t None Disabled (init_perms Active off sz)).
Definition init_tree t off sz
  : tree item := branch (initial_item t off sz) empty empty.

(* Create a new allocation. *)
Definition extend_trees t blk off sz
  : trees -> trees := fun ts =>
  <[blk := init_tree t off sz]>ts.

(* Perform the access check on a block of continuous memory.
   Combines together the previously defined
   - [apply_access_perm] function on permissions (including protector UB), with
   - [tree_apply_access] that lifts functions on permissions to functions on trees.
   This implements Tree::before_memory_{read,write,deallocation}. *)

Definition maybe_non_children_only (b:bool) := if b then nonchildren_only else λ x, x.

Lemma maybe_non_children_only_no_effect b1 fn rel ip perm :
  (∀ b, rel ≠ Foreign (Parent b)) →
  maybe_non_children_only b1 fn rel ip perm =
  fn rel ip perm.
Proof.
  destruct b1, rel as [[]|[]]; try done.
  intros H. exfalso. by eapply H.
Qed.

Lemma maybe_non_children_only_effect_or_nop b1 fn rel :
  (∀ ip perm, maybe_non_children_only b1 fn rel ip perm = fn rel ip perm) ∨
  (∀ ip perm, maybe_non_children_only b1 fn rel ip perm = Some perm).
Proof.
  destruct b1, rel as [[]|[]]; simpl; eauto.
Qed.

Lemma maybe_non_children_only_effect_or_nop_strong b1 fn rel :
  (∀ ip perm, maybe_non_children_only b1 fn rel ip perm = fn rel ip perm ∧ (b1 ≠ true ∨ (∀ b, rel ≠ Foreign (Parent b)))) ∨
  (∀ ip perm, maybe_non_children_only b1 fn rel ip perm = Some perm ∧ b1 = true ∧ ∃ b, rel = Foreign (Parent b)).
Proof.
  destruct b1, rel as [[]|[]]; simpl; eauto.
Qed.

Definition memory_access_maybe_nonchildren_only b kind cids tg range
  : tree item -> option (tree item) := fun tr =>
  tree_apply_access (maybe_non_children_only b (apply_access_perm kind)) cids tg range tr.

Definition memory_access := memory_access_maybe_nonchildren_only false.
(* Same thing but only to nonchildren, provides the access to perform on function exit. *)
Definition memory_access_nonchildren_only := memory_access_maybe_nonchildren_only true.

Definition protector_end_action (ls : lazy_permission) : option access_kind := 
  if ls.(initialized) then match ls.(perm) with
    Cell => None
  | Active => Some AccessWrite
  | _ => Some AccessRead
  end else None.

(* The transformation to apply on function exit doesn't actually do anything
   except trigger UB if there is still a protector, but it's simpler to express it
   in terms of functions that we already have. *)
Definition memory_deallocate cids t range
  : tree item -> option (tree item) := fun tr =>
  (* Implicit write on deallocation. *)
  let post_write := memory_access AccessWrite cids t range tr in
  (* Then strong protector UB. *)
  let find_strong_prot : item -> option item := fun it => (
    if bool_decide (protector_is_strong it.(iprot))
    && bool_decide (protector_is_active it.(iprot) cids)
       (* Check if the protector is actually relevant anywhere *)
       (* Note that for "default" lazy_perms, protector_end_action lp would be None as they are lazy *)
    && bool_decide (map_Exists (λ _ lp, is_Some (protector_end_action lp)) it.(iperm))
    then None
    else Some it
  ) in
  (* Triggers UB iff some node triggers UB. *)
  option_bind
    (fun tr' => join_nodes (map_nodes find_strong_prot tr'))
    post_write.

(* We want to reason about reachability of states in the state machine.
   The default definition doesn't compute well, so we define
   1. a definition that computes
   2. a definition by the reflexive transitive closure of some much more
      easy to verify step.
   The two are provably equivalent. *)
Definition witness_transition p p' : Prop :=
  match p, p' with
  | Reserved ResActivable, Reserved ResConflicted
  | Reserved _, Active
  | ReservedIM, Active
  | Active, Frozen
  | Frozen, Disabled
  => True
  | _, _ => False
  end.

(* FIXME: using builtin reflexive transitive closure could simplify some proofs. *)
Inductive witness_reach p p' : Prop :=
  | witness_reach_refl : p = p' -> witness_reach p p'
  | witness_reach_step p'' : witness_transition p p'' ->  witness_reach p'' p' -> witness_reach p p'
  .

Definition reach p p' : Prop :=
  match p, p' with
  | ReservedIM, (ReservedIM | Active | Frozen | Disabled)
  | Reserved ResActivable, (Reserved ResActivable | Reserved ResConflicted | Active | Frozen | Disabled)
  | Reserved ResConflicted, (Reserved ResConflicted | Active | Frozen | Disabled)
  | Active, (Active | Frozen | Disabled)
  | Frozen, (Frozen | Disabled)
  | Disabled, (Disabled)
  | Cell, Cell
  => True
  | _, _ => False
  end.

(* Denotes a permission that "acts like Frozen" for the purpose
   of a later invariant. Concretely this contains
   [Frozen], [Disabled], [Reserved ResConflicted],
   which are the 3 permissions that are not affected by a foreign read,
   so "acts like frozen" can mean "is allowed to coexist with shared references". *)
Definition freeze_like p : Prop :=
  reach Frozen p \/ p = Reserved ResConflicted.

(* Now we check that the two definitions of reachability are equivalent,
   so that the clean definition acts as a witness for the easy-to-do-case-analysis
   definition *)

Ltac destruct_permission :=
  match goal with
  | p : permission |- _ => destruct p as [|[]| | | |]
  end.

Ltac invert_reach :=
  match goal with
  | H : witness_reach _ _ |- _ =>
    let eql := fresh "Eql" in
    inversion H as [eql|]; clear H;
    try (inversion eql; clear eql)
  end.

Ltac invert_transition :=
  match goal with
  | H : witness_transition _ _ |- _ =>
    let eql := fresh "Eql" in
    inversion H; clear H
  end.

Ltac reach_inversion_strategy :=
  multimatch goal with
  | _ => destruct_permission
  | _ => invert_transition
  | _ => invert_reach
  end.

Lemma reach_complete p p' :
  witness_reach p p' -> reach p p'.
Proof.
  repeat destruct_permission; simpl; intro WReach; try tauto.
  all: do 20 reach_inversion_strategy.
Qed.

Ltac witness_reach_solve :=
  let p := fresh "p" in
  let p' := fresh "p'" in
  let p'' := fresh "p''" in
  match goal with
  | |- witness_reach ?p ?p => apply witness_reach_refl; reflexivity
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ (Reserved ResConflicted)); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ Active); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ Frozen); simpl; [tauto|]
  | |- witness_reach ?p ?p' => apply (witness_reach_step _ _ Disabled); simpl; [tauto|]
  end.

Lemma reach_sound p p' :
  reach p p' -> witness_reach p p'.
Proof.
  destruct p as [|[]| | | |], p' as [|[]| | | |]; simpl; intro; try tauto.
  all: do 10 witness_reach_solve.
Qed.

(* This is the important lemma of this section.
   The [reach] definition that computes well is correct. *)
Lemma reach_correct p p' :
  reach p p' <-> witness_reach p p'.
Proof.
  split; [apply reach_sound|apply reach_complete].
Qed.

Lemma reach_reflexive p q : p = q -> reach p q.
Proof. rewrite reach_correct. apply witness_reach_refl. Qed.

Lemma reach_transitive p p' p'' : reach p p' -> reach p' p'' -> reach p p''.
Proof.
  repeat rewrite reach_correct.
  intros Reachpp' Reachp'p''.
  induction Reachpp'.
  - subst; tauto.
  - eapply witness_reach_step; [eassumption|auto].
Qed.

(** CONSISTENCY *)

(* General *)

Lemma not_is_negb (b:bool) :
  b = false <-> ~b = true.
Proof. by destruct b. Qed.

Lemma IsTag_reverse it it' :
  IsTag it.(itag) it' -> IsTag it'.(itag) it.
Proof. simpl. auto. Qed.

Lemma apply_access_idempotent
  {kind rel} (isprot isprot' : bool) {perm perm'}
  (ProtIncr : if isprot then True else isprot' = false)
  (Acc1 : apply_access_perm kind rel isprot perm = Some perm')
  (Witness : exists x, x = (kind, rel, perm, perm', isprot, isprot'))
  : apply_access_perm kind rel isprot' perm' = Some perm'.
Proof.
  destruct perm as [init perm]; destruct perm' as [init' perm'].
  unfold apply_access_perm in *.
  (* This is going to be a big case analysis, we essentially have to destruct
     everything. Still, let's try to do it in a smart order otherwise it'll generate
     upwards of 2000 cases *)
  destruct kind, rel.
  all: destruct isprot.
  all: destruct init, perm as [|[]| | | |]; simpl in *; inversion Acc1; subst.
  all: simpl; try auto.
  all: destruct isprot'; simpl; try auto.
Qed.

(** Some important predicates on trees. *)

(** There is a node with tag [tg]. *)
Definition tree_contains tg tr
  : Prop :=
  exists_node (IsTag tg) tr.

(** All nodes with tag [tg] equal [it].
    This is often useless on its own if you don't also own a [tree_contains tg]. *)
Definition tree_item_determined tg it tr
  : Prop :=
  every_node (fun it' => IsTag tg it' -> it' = it) tr.

Notation has_tag tg := (fun it => bool_decide (IsTag tg it)) (only parsing).

(** Counting how many nodes in a tree have a certain tag. *)
Definition tree_count_tg tg tr : nat := count_nodes (has_tag tg) tr.
Definition tree_unique tg tr : Prop := tree_count_tg tg tr = 1.

(** Capable of lifting any of the above predicates to [trees]. *)
Definition trees_at_block prop trs blk
  : Prop :=
  match trs !! blk with
  | None => False
  | Some tr => prop tr
  end.

Lemma trees_at_block_char prop trs blk :
  trees_at_block prop trs blk ↔ ∃ tr, trs !! blk = Some tr ∧ prop tr.
Proof.
  rewrite /trees_at_block. 
  destruct (trs !! blk) as [tr|]; split; intros H.
  - by eexists.
  - by destruct H as (? & [= ->] & H).
  - done.
  - by destruct H as (? & [=] & _).
Qed.

Definition trees_contain tg trs blk :=
  trees_at_block (tree_contains tg) trs blk.

Definition trees_item_determined tg trs blk it :=
  trees_at_block (tree_item_determined tg it) trs blk.

Definition trees_unique tg trs blk it :=
  trees_at_block (tree_unique tg) trs blk.

Definition ParentChildInBlk tg tg' trs blk :=
  trees_at_block (ParentChildIn tg tg') trs blk.

(* FIXME: Future refactoring: improve consistency of argument ordering *)

(** Reborrow *)

(* None indicates an identity retag *)
Definition retag_perm (pk : pointer_kind) (im : interior_mut) (rk : retag_kind) : option permission :=
  match pk, im, rk with
  | ShrRef, InteriorMut, _ => Some Cell
  | ShrRef, _, _ => Some Frozen
  | (MutRef | Box), InteriorMut, Default => Some (ReservedIM)
  | (MutRef | Box), _, _ => Some (Reserved ResActivable)
  end.

Definition pointer_kind_to_strength (pk : pointer_kind) : prot_strong := 
  match pk with
    Box => ProtWeak
  | _ => ProtStrong
  end.

Definition retag_kind_to_prot (cid : call_id) (rk : retag_kind) (s : prot_strong) : option protector := 
  match rk with
    Default => None
  | FnEntry => Some (mkProtector s cid)
  end.

Definition create_new_item tg pk im rk (cid : call_id) :=
      perm ← retag_perm pk im rk;
  let s := pointer_kind_to_strength pk in
  let prot := retag_kind_to_prot cid rk s in
  Some {| itag:=tg; iprot:=prot; initp:=perm; iperm:=∅ |}.

Definition create_child cids (oldt:tag) (newt:tag) pk im rk (cid : call_id)
  : tree item -> option (tree item) := fun tr =>
  it ← create_new_item newt pk im rk cid;
  Some $ insert_child_at tr it (IsTag oldt).

Definition item_lazy_perm_at_loc it (l:loc')
  : lazy_permission := item_lookup it l.

Definition item_perm_at_loc it z
  : permission :=
  perm (item_lazy_perm_at_loc it z).

Definition every_tagged t (P:item -> Prop) tr
  : Prop :=
  every_node (fun it => IsTag t it -> P it) tr.

Definition apply_within_trees (fn:tree item -> option (tree item)) blk
  : trees -> option trees := fun trs =>
  oldtr ← trs !! blk;
  newtr ← fn oldtr;
  Some $ <[blk := newtr]> trs.

Definition item_fresh_call cid it :=
  ~protector_is_for_call cid (iprot it).

Definition tree_fresh_call cid tr :=
  every_node (item_fresh_call cid) tr.

Definition trees_fresh_call cid trs blk :=
  forall tr,
  trs !! blk = Some tr ->
  tree_fresh_call cid tr.

(* Traverse the entire tree and get for each tag protected by cid its currently initialized locations.
   Those are all the locations that we'll do a read access through, or even a write access if it is Active *)
Definition tree_get_all_protected_tags_initialized_locs (cid : nat) (tr : tree item)
  : gset (tag * gmap Z access_kind) :=
  fold_nodes ∅ (fun it lacc racc =>
    (if decide (Some cid = option_map call it.(iprot)) then
      {[(it.(itag), mem_enumerate_sat protector_end_action it.(iperm))]} else ∅)
    ∪ lacc
    ∪ racc
  ) tr.

Definition tree_access_all_protected_initialized (cids : call_id_set) (cid : nat)
  : tree item -> option (tree item) := fun tr =>
    (* read one loc by doing a memory_access *)
    let reader_loc (tg : tag) (loc : Z) acc : tree item -> option (tree item) := fun tr =>
      memory_access_nonchildren_only acc cids tg (loc, 1) tr in
    (* read several locs of the same tag, propagate failures *)
    let reader_locs (tg : tag) (locs : gmap Z access_kind) : tree item -> option (tree item) := fun tr =>
     map_fold (fun loc acc (tr:option (tree item)) => tr ← tr; reader_loc tg loc acc tr) (Some tr) locs in
    (* get all initialized locs as defined above, these are what we need to read *)
    let init_locs := tree_get_all_protected_tags_initialized_locs cid tr in
    (* finally we can combine this all *)
    set_fold (fun '(tg, init_locs) (tr:option (tree item)) => tr ← tr; reader_locs tg init_locs tr) (Some tr) init_locs.

(* WARNING: don't make the access visible to children!
    You can check in `trees_access_all_protected_initialized` that we properly use
    `memory_access_nonchildren_only`. *)
(* Finally we read all protected initialized locations on the entire trees by folding it
   for each tree separately.
   NOTE: be careful about how other properties assume the uniqueness of tags intra- and inter- trees,
   because this may have a weird behavior if you have the same tag across two trees and e.g. only one
   of them is protected, which shouldn't happen but isn't impossible by construction. *)
Definition trees_access_all_protected_initialized (cids : call_id_set) (cid : nat) (trs : trees) : option trees :=
  set_fold (fun k (trs : option trees) =>
    trs ← trs;
    apply_within_trees (tree_access_all_protected_initialized cids cid) k trs
  ) (Some trs) (dom trs).

Inductive bor_step (trs : trees) (cids : call_id_set) (nxtp : nat) (nxtc : call_id)
  : event -> trees -> call_id_set -> nat -> call_id -> Prop :=
  | AllocIS (blk : block) (off : Z) (sz : nat)
    (* Memory allocation *)
    (FRESH : trs !! blk = None)
    (NONZERO : (sz > 0)%nat) :
    bor_step
      trs cids nxtp nxtc
      (AllocEvt blk nxtp (off, sz))
      (extend_trees nxtp blk off sz trs) cids (S nxtp) nxtc
  | CopyIS trs' (alloc : block) range tg val
    (* Successful read access *)
    (EXISTS_TAG: trees_contain tg trs alloc)
    (ACC: apply_within_trees (memory_access AccessRead cids tg range) alloc trs = Some trs')
    (RANGE_SIZE: range.2 ≠ 0) :
    bor_step
      trs cids nxtp nxtc
      (CopyEvt alloc tg range val)
      trs' cids nxtp nxtc
  | ZeroCopyIS (alloc : block) range tg val
    (* zero-sized read *)
    (RANGE_SIZE: range.2 = 0) :
    bor_step
      trs cids nxtp nxtc
      (CopyEvt alloc tg range val)
      trs cids nxtp nxtc
(*  | FailedCopyIS (alloc : block) range tg
    (* Unsuccessful read access just returns poison instead of causing UB *)
    (* WARNING: SB works like this, having failed reads return poison
       instead of triggering UB. We can't do this for Tree Borrows.
       This was a hack for SB anyway, and not having it gives a stronger result.
     *)
    (EXISTS_TAG : trees_contain tg trs alloc)
    (ACC : apply_within_trees (memory_access AccessRead cids tg range) alloc trs = None) :
    bor_step
      trs cids nxtp nxtc
      (FailedCopyEvt alloc tg range)
      trs cids nxtp nxtc *)
  | WriteIS trs' (alloc : block) range tg val
    (* Successful write access *)
    (EXISTS_TAG: trees_contain tg trs alloc)
    (ACC: apply_within_trees (memory_access AccessWrite cids tg range) alloc trs = Some trs')
    (RANGE_SIZE: range.2 ≠ 0) :
    bor_step
      trs cids nxtp nxtc
      (WriteEvt alloc tg range val)
      trs' cids nxtp nxtc
  | ZeroWriteIS (alloc : block) range tg val
    (* Zero-sized write access *)
    (RANGE_SIZE: range.2 = 0) :
    bor_step
      trs cids nxtp nxtc
      (WriteEvt alloc tg range val)
      trs cids nxtp nxtc
  | RetagIS trs' trs'' parentt (alloc : block) range pk im cid rk
      (* For a retag we require that the parent exists and the introduced tag is fresh, then we do a read access.
         NOTE: create_child does not read, it only inserts, so the read needs to be explicitly added.
               We want to do the read *after* the insertion so that it properly initializes the locations of the range. *)
    (EL: cid ∈ cids)
    (EXISTS_TAG: trees_contain parentt trs alloc)
    (FRESH_CHILD: ~trees_contain nxtp trs alloc)
    (RETAG_EFFECT: apply_within_trees (create_child cids parentt nxtp pk im rk cid) alloc trs = Some trs')
    (READ_ON_REBOR: apply_within_trees (memory_access AccessRead cids nxtp range) alloc trs' = Some trs'') :
    bor_step
      trs cids nxtp nxtc
      (RetagEvt alloc range parentt nxtp pk im cid rk)
      trs'' cids (S nxtp) nxtc
  | RetagNoopIS parentt (alloc : block) range pk im cid rk
      (* This is a noop retag. Some "retagging" operations don't actually do anything,
         e.g. raw pointer retags. *)
    (EL: cid ∈ cids)
    (EXISTS_TAG: trees_contain parentt trs alloc)
    (IS_NOOP: retag_perm pk im rk = None) :
    bor_step
      trs cids nxtp nxtc
      (RetagEvt alloc range parentt parentt pk im cid rk)
      trs cids nxtp nxtc
  | DeallocIS trs' (alloc : block) (tg : tag) range
    (EXISTS_TAG: trees_contain tg trs alloc)
    (ACC: apply_within_trees (memory_deallocate cids tg range) alloc trs = Some trs') :
    (* We are deleting the entire allocation to make sure that the tree has the same blocks as the heap *)
    bor_step
      trs cids nxtp nxtc
      (DeallocEvt alloc tg range)
      (delete alloc trs') cids nxtp nxtc
  | InitCallIS :
    bor_step
      trs cids nxtp nxtc
      (InitCallEvt nxtc)
      trs ({[nxtc]} ∪ cids) nxtp (S nxtc)
  | EndCallIS c trs'
    (EL: c ∈ cids)
    (* Don't forget the implicit read on function exit through all initialized locations *)
    (READ_ON_UNPROT : trees_access_all_protected_initialized cids c trs = Some trs') :
    bor_step
      trs cids nxtp nxtc
      (EndCallEvt c)
      trs' (cids ∖ {[c]}) nxtp nxtc
  .

Inductive bor_steps trs cids nxtp nxtc
  : list event -> trees -> call_id_set -> nat -> call_id -> Prop :=
  | BorStepsDone :
      bor_steps
        trs cids nxtp nxtc
        []
        trs cids nxtp nxtc
  | BorStepsMore evt evts
      trs1 cids1 nxtp1 nxtc1
      trs2 cids2 nxtp2 nxtc2
      (HEAD : bor_step trs cids nxtp nxtc evt trs1 cids1 nxtp1 nxtc1)
      (REST : bor_steps trs1 cids1 nxtp1 nxtc1 evts trs2 cids2 nxtp2 nxtc2) :
      bor_steps
        trs cids nxtp nxtc
        (evt :: evts)
        trs2 cids2 nxtp2 nxtc2
  .

(** Unit test for the tree relation definition, showing how it works *)
(* conversion is magic *)
Local Definition unpack_option {A:Type} (o : option A) {oo : A} (Heq : o = Some oo) : A := oo.
Local Notation unwrap K := (unpack_option K eq_refl).

Local Definition initial_tree := init_tree 1 0 4.
Local Definition with_one_child :=
  unwrap (create_child ∅ 1 2 MutRef TyFrz Default 0 initial_tree).
Local Definition with_two_children :=
  unwrap (create_child ∅ 1 3 MutRef TyFrz Default 0 with_one_child).
Local Definition with_three_children :=
  unwrap (create_child ∅ 2 4 MutRef TyFrz Default 0 with_two_children).

(*
   1
  / \
 2   3
 |
 4
In particular, 4 is a non-immediate child of 1, but all other child relations are immediate.

*)

(** Having constructed the above tree, we can now check that all relations are computed correctly *)
(* conversion keeps being magical *)
Succeed Example foo : rel_dec with_three_children 1 1 = Child This                   := eq_refl.
Succeed Example foo : rel_dec with_three_children 1 2 = Foreign (Parent Immediate)   := eq_refl.
Succeed Example foo : rel_dec with_three_children 1 3 = Foreign (Parent Immediate)   := eq_refl.
Succeed Example foo : rel_dec with_three_children 1 4 = Foreign (Parent FurtherAway) := eq_refl.
Succeed Example foo : rel_dec with_three_children 2 1 = Child (Strict Immediate)     := eq_refl.
Succeed Example foo : rel_dec with_three_children 2 2 = Child This                   := eq_refl.
Succeed Example foo : rel_dec with_three_children 2 3 = Foreign Cousin               := eq_refl.
Succeed Example foo : rel_dec with_three_children 2 4 = Foreign (Parent Immediate)   := eq_refl.
Succeed Example foo : rel_dec with_three_children 3 1 = Child (Strict Immediate)     := eq_refl.
Succeed Example foo : rel_dec with_three_children 3 2 = Foreign Cousin               := eq_refl.
Succeed Example foo : rel_dec with_three_children 3 3 = Child This                   := eq_refl.
Succeed Example foo : rel_dec with_three_children 3 4 = Foreign Cousin               := eq_refl.
Succeed Example foo : rel_dec with_three_children 4 1 = Child (Strict FurtherAway)   := eq_refl.
Succeed Example foo : rel_dec with_three_children 4 2 = Child (Strict Immediate)     := eq_refl.
Succeed Example foo : rel_dec with_three_children 4 3 = Foreign Cousin               := eq_refl.
Succeed Example foo : rel_dec with_three_children 4 4 = Child This                   := eq_refl.

