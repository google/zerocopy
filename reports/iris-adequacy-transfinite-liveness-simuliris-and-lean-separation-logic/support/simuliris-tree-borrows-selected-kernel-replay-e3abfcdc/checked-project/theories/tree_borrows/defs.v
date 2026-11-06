From iris.prelude Require Export prelude.
From simuliris.tree_borrows Require Export tactics notation lang bor_semantics bor_lemmas.

(* Henceforth also in the files importing us we want to use Z_scope. *)
Global Open Scope Z_scope.

Definition wf_mem_tag (h: mem) (nxtp: tag) :=
  ∀ (l l':loc) pid, h !! l = Some (ScPtr l' pid) →
    (pid < nxtp)%nat.

Definition lazy_perm_wf (lp : lazy_permission) :=
  lp.(perm) = Active → lp.(initialized) = PermInit.

(** Well-formedness constraints on items *)
Record item_wf (it:item) (nxtp:tag) (nxtc:call_id) := {
  (** Tag is valid *)
  item_tag_valid : forall tg, IsTag tg it -> (tg < nxtp)%nat;
  (** Callid is valid *)
  item_cid_valid : forall cid, protector_is_for_call cid (iprot it) -> (cid < nxtc)%nat;
  (** Permission registered as "default" can't be Active *)
  item_default_perm_valid : it.(initp) ≠ Active;
  (** Only protected items can have ReservedIM somewhere in their permissions *)
  item_perms_reserved_im_protected : is_Some (it.(iprot)) → ∀ off, (default (mkPerm PermLazy it.(initp)) (it.(iperm) !! off)).(perm) = ReservedIM → False;
  (** Active implies initialized *)
  item_perms_valid : map_Forall (λ _, lazy_perm_wf) it.(iperm);
  (** Current permission is reachable from initial permission. (This guarantees no Active on shared references) *)
  item_perm_reachable : it.(initp) ≠ Disabled → map_Forall (λ k v, reach it.(initp) (perm v)) it.(iperm)
}.

(** Relating the state of the current item with that of its parents.
    The important properties are:
    - an initialized item must have initialized parents,
    - an Active item must have Active parents (or Cell parents),
    - a protected must not have Disabled parents (except if the protected item is Cell).
 *)
Definition item_all_more_init itp itc := ∀ l, initialized (item_lookup itc l) = PermInit → initialized (item_lookup itp l) = PermInit.
Definition parents_more_init (tr : tree item) := ∀ tg, every_child tg item_all_more_init tr.
Definition item_all_more_active itp itc := ∀ l, perm (item_lookup itc l) = Active → perm (item_lookup itp l) = Active ∨ perm (item_lookup itp l) = Cell.
Definition parents_more_active (tr : tree item) := ∀ tg, every_child tg item_all_more_active tr.

Definition item_protected_all_parents_not_disabled C l itp itc := initialized (item_lookup itc l) = PermInit → protector_is_active (iprot itc) C → perm (item_lookup itp l) ≠ Disabled ∨ perm (item_lookup itc l) = Cell.
Definition protected_parents_not_disabled C (tr : tree item) := ∀ tg l, every_child tg (item_protected_all_parents_not_disabled C l) tr.

Definition active_or_prot_init C it off := 
  perm (item_lookup it off) = Active ∨
  ((protector_is_active it.(iprot) C ∧ perm (item_lookup it off) ≠ Cell) ∨ let p := perm (item_lookup it off) in (p = Frozen ∨ p = Reserved ResActivable ∨ p = Reserved ResConflicted)) ∧ initialized (item_lookup it off) = PermInit.
(* the definition is asymmetric: an active tag only has very restricted foreign cousins *)
Definition no_active_cousins C tr := ∀ tg1 it1 tg2 it2 off, tree_lookup tr tg1 it1 → tree_lookup tr tg2 it2 → rel_dec tr tg1 tg2 = Foreign Cousin → active_or_prot_init C it1 off → perm (item_lookup it2 off) = Active → False.

Definition tree_items_unique (tr:tree item) :=
  forall tg,
  tree_contains tg tr -> tree_unique tg tr.

Definition tree_items_compat_nexts (tr:tree item) (nxtp:tag) (nxtc: call_id) :=
  every_node (λ it, item_wf it nxtp nxtc) tr.
  (* FIXME: Improve consistency of naming conventions *)

Definition wf_tree (tr:tree item) :=
  tree_items_unique tr.
Definition each_tree_wf (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → wf_tree tr.
Definition each_tree_parents_more_init (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → parents_more_init tr.
Definition each_tree_parents_more_active (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → parents_more_active tr.
Definition each_tree_protected_parents_not_disabled C (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → protected_parents_not_disabled C tr.
Definition each_tree_no_active_cousins C (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → no_active_cousins C tr.
Definition tags_unique_per_location (trs:trees) :=
  ∀ blk1 blk2 tr1 tr2 tg, trs !! blk1 = Some tr1 → trs !! blk2 = Some tr2 →
          tree_contains tg tr1 → tree_contains tg tr2 → blk1 = blk2.
Definition wf_trees (trs:trees) :=
  each_tree_wf trs ∧ tags_unique_per_location trs.
Definition trees_compat_nexts (trs:trees) (nxtp:tag) (nxtc: call_id) :=
  ∀ blk tr, trs !! blk = Some tr → tree_items_compat_nexts tr nxtp nxtc.
Definition wf_non_empty (trs:trees) :=
  ∀ blk tr, trs !! blk = Some tr → tr ≠ empty.

Definition wf_cid_incl (cids: call_id_set) (nxtc: call_id) :=
  ∀ c : call_id, c ∈ cids → (c < nxtc)%nat.
Definition wf_scalar t sc := ∀ t' l, sc = ScPtr l t' → t' < t.

Definition same_blocks (hp:mem) (trs:trees) :=
  dom trs =@{gset _} set_map fst (dom hp).
Arguments same_blocks / _ _.
(* Formerly: map fst (dom hp) === dom trs
   However this is no longer accurate. *)

Definition root_invariant blk it (shp : mem) :=
  it.(iprot) = None ∧ it.(initp) = Disabled ∧
  ∀ off, match it.(iperm) !! off with
    Some (mkPerm PermInit Active) => is_Some (shp !! (blk, off))
  | Some (mkPerm PermLazy Disabled) | None => shp !! (blk, off) = None
  | _ => False end.

Definition tree_root_compatible (tr : tree item) blk shp := 
  match tr with empty => False | branch it sib _ => root_invariant blk it shp ∧ sib = empty end.

Definition tree_roots_compatible (trs : trees) shp := 
  ∀ blk tr, trs !! blk = Some tr → tree_root_compatible tr blk shp.


(* A State is well-formed if... *)
Record state_wf (s: state) := {
  (*state_wf_dom : dom s.(shp) ≡ dom s.(strs);
     This was included in SB but we don't care anymore because TB
     is very permissive about the range so out-of-bounds UB is *always*
     triggered by `expr_semantics` not `bor_semantics`. *)

  (* The heap and the trees talk of the same allocations *)
  state_wf_dom : same_blocks s.(shp) s.(strs);
  (* Every tree is well-formed (includes uniqueness of tags) *)
  state_wf_tree_unq : wf_trees s.(strs);
  (* The child-parent constraints relating to initialization etc. hold *)
  state_wf_tree_more_init : each_tree_parents_more_init s.(strs);
  state_wf_tree_more_active : each_tree_parents_more_active s.(strs);
  state_wf_tree_not_disabled :  each_tree_protected_parents_not_disabled s.(scs) s.(strs);
  (* Some other constraints on relations (cousins can't be simultaneously active) *)
  state_wf_tree_no_active_cousins : each_tree_no_active_cousins s.(scs) s.(strs);
  (* "next fresh tag" is fresh. *)
  state_wf_tree_compat : trees_compat_nexts s.(strs) s.(snp) s.(snc);
  (* Every root pointer is active *)
  state_wf_roots_active : tree_roots_compatible s.(strs) s.(shp);
  (* "next fresh callid" is fresh. *)
  state_wf_cid_agree: wf_cid_incl s.(scs) s.(snc);
}.

Definition init_state := (mkState ∅ ∅ {[O]} O 1).

(** Tag kinds:
    - `tk_pub`: this tag is public
    - `tk_unq tk_res` and `tk_unq tk_act`: split from the `tk_unq` in Stacked Borrows.
      We need two of them to support the two stages of 2-phase borrows.
      The intent is that whatever mutable reference is reborrowed gets a
      `tk_unq tk_res` initially and on the first child write we can change it to a
      `tk_unq tk_act`.
    - `tk_local`: locally owned tag without any references (not even local reborrows). *)
Inductive tk_activation_kind := tk_res | tk_act.
Global Instance tk_activation_kind_eq_dec : EqDecision tk_activation_kind.
Proof. solve_decision. Defined.
Inductive tag_kind := tk_pub | tk_unq (act : tk_activation_kind) | tk_local.
Global Instance tk_kind_eq_dec : EqDecision tag_kind.
Proof. solve_decision. Defined.

Definition state_upd_mem (f : mem → mem) σ :=
  mkState (f σ.(shp)) σ.(strs) σ.(scs) σ.(snp) σ.(snc).
Definition state_upd_trees (f : trees → trees) σ :=
  mkState σ.(shp) (f σ.(strs)) σ.(scs) σ.(snp) σ.(snc).
Definition state_upd_calls (f : call_id_set → call_id_set) σ :=
  mkState σ.(shp) σ.(strs) (f σ.(scs)) σ.(snp) σ.(snc).
