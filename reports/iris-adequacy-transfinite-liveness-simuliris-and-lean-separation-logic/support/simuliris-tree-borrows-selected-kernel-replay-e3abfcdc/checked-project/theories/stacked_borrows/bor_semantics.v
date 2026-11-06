(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From Equations Require Import Equations.
From iris.prelude Require Import prelude options.
From stdpp Require Export gmap.
From simuliris.stacked_borrows Require Export lang_base notation.



(*** STACKED BORROWS SEMANTICS ---------------------------------------------***)

Implicit Type (α: stacks) (t: ptr_id) (c: call_id) (T: type).

(** CORE SEMANTICS *)

Inductive access_kind := AccessRead | AccessWrite.

Definition grants (perm: permission) (access: access_kind) : bool :=
  match perm, access with
  | Disabled, _ => false
  (* All items grant read access.
    All items except SharedReadOnly grant write access. *)
  | SharedReadOnly, AccessWrite => false
  | _, _ => true
  end.

Definition matched_grant (access: access_kind) (bor: tag) (it: item) :=
  grants it.(perm) access ∧ it.(tg) = bor.
Global Instance matched_grant_dec (access: access_kind) (bor: tag) (it : item) :
  Decision (matched_grant access bor it) := _.

(** Difference from the paper/Miri in indexing of stacks: *)
(** In the paper, we represent stacks as lists with their bottom at the left end
  (head) of the list. That is, in terms of indexing, 0 is the bottom of
  the stack `stk`, and `|stk| - 1` is the top of `stk`.
  In Coq, however, to conveniently perform induction on stacks, we pick the head
  of the list as the top, and the tail of the list as the bottom of the stack.
  In terms of indexing, 0 is thus the top of the stack, and `|stk| - 1` is the
  bottom.  In this case, a smaller index means a higher item in the stack. *)

(* Return the index of the granting item *)
Definition find_granting (stk: stack) (access: access_kind) (bor: tag) :
  option (nat * permission) :=
  (λ nit, (nit.1, nit.2.(perm))) <$> (list_find (matched_grant access bor) stk).

Definition is_active (cids: call_id_set) (c: call_id) : bool :=
  bool_decide (c ∈ cids).
(* FIXME: this one should exclude protectors of Disabled items. @LG fixed this*)
Definition is_active_protector cids (it: item) :=
  match it.(protector) with
  | Some c => Is_true (is_active cids c) ∧ it.(perm) ≠ Disabled
  | _ => False
  end.
Global Instance is_active_protector_dec cids it : Decision (is_active_protector cids it).
Proof. rewrite /is_active_protector. case_match; solve_decision. Qed.

(* Find the top active protector *)
Definition find_top_active_protector cids (stk: stack) :=
  list_find (is_active_protector cids) stk.

(* Checks to deallocate a location: Like a write access, but also there must be
  no active protectors at all. *)
Definition dealloc1 (stk: stack) (bor: tag) cids : option unit :=
  (* Step 1: Find granting item. *)
  found ← find_granting stk AccessWrite bor;
  (* Step 2: Check that there are no active protectors left. *)
  if find_top_active_protector cids stk then None else Some ().

(* Find the index RIGHT BEFORE the first incompatible item.
   Remember that 0 is the top of the stack. *)
Definition find_first_write_incompatible
  (stk: stack) (pm: permission) : option nat :=
  match pm with
  | Unique => Some (length stk)
  | SharedReadWrite =>
      match (list_find (λ it, it.(perm) ≠ SharedReadWrite) (reverse stk)) with
      | Some (idx, _) => Some ((length stk) - idx)%nat
      | _ => Some O
      end
  | SharedReadOnly | Disabled => None
  end.

(* Check if `it` has an active protector -- if so, return false, otherwise true. *)
Definition check_protector cids (it: item) : bool :=
  match it.(protector) with
  | None => true
  | Some c => if is_active cids c then false else true
  end.

(* Remove from `stk` the items before `idx`.
  Check that removed items do not have active protectors.
  The check is run from the top to before the `idx`. *)
Fixpoint remove_check cids (stk: stack) (idx: nat) : option stack :=
  match idx, stk with
  (* Assumption: idx ≤ length stk *)
  | S _, [] => None
  | O, stk => Some stk
  | S idx, it :: stk =>
      if check_protector cids it then remove_check cids stk idx else None
  end.

(* Replace any Unique permission with Disabled, starting from the top of the
  stack. Check that replaced item do not have active protectors. *)
Fixpoint replace_check' cids (acc stk : stack) : option stack :=
  match stk with
  | [] => Some acc
  | it :: stk =>
      if decide (it.(perm) = Unique) then
        if check_protector cids it
        then let new := mkItem Disabled it.(tg) it.(protector) in
             replace_check' cids (acc ++ [new]) stk
        else None
      else replace_check' cids (acc ++ [it]) stk
  end.
Definition replace_check cids (stk: stack) : option stack :=
  replace_check' cids [] stk.

(* Test if a memory `access` using pointer tagged `tg` is granted.
   If yes, return the index (in the old stack) of the item that granted it,
   as well as the new stack. *)
Definition access1 (stk: stack) (access: access_kind) (tg: tag) cids
  : option (nat * stack) :=
  (* Step 1: Find granting item. *)
  idx_p ← find_granting stk access tg;
  (* Step 2: Remove incompatible items. *)
  match access with
  | AccessWrite =>
      (* Remove everything above the write-compatible items, like a proper stack. *)
      incompat_idx ← find_first_write_incompatible (take idx_p.1 stk) idx_p.2;
      stk' ← remove_check cids (take idx_p.1 stk) incompat_idx;
      Some (idx_p.1, stk' ++ drop idx_p.1 stk)
  | AccessRead =>
      (* On a read, *disable* all `Unique` above the granting item. *)
      stk' ← replace_check cids (take idx_p.1 stk);
      Some (idx_p.1, stk' ++ drop idx_p.1 stk)
  end.

(* Initialize [l, l + n) with singleton stacks of `tg` *)
Definition init_stack (t: tag) : stack := [mkItem Unique t None].
Fixpoint init_stacks α (l:loc) (n:nat) (tg: tag) : stacks :=
  match n with
  | O => α
  | S n => <[l:= init_stack tg]>(init_stacks α (l +ₗ 1) n tg)
  end.

Fixpoint for_each α (l:loc) (n:nat) (dealloc: bool) (f: stack → option stack)
  : option stacks :=
  match n with
  | O => Some α
  | S n =>
      let l' := (l +ₗ n) in
      stk ← α !! l'; stk' ← f stk ;
      if dealloc
      then for_each (delete l' α) l n dealloc f
      else for_each (<[l':=stk']> α) l n dealloc f
  end.

(* Perform the access check on a block of continuous memory.
 * This implements Stacks::memory_read/memory_written/memory_deallocated. *)
Definition memory_read α cids l (tg: tag) (n: nat) : option stacks :=
  for_each α l n false (λ stk, nstk' ← access1 stk AccessRead tg cids; Some nstk'.2).
Definition memory_written α cids l (tg: tag) (n: nat) : option stacks :=
  for_each α l n false (λ stk, nstk' ← access1 stk AccessWrite tg cids; Some nstk'.2).
Definition memory_deallocated α cids l (tg: tag) (n: nat) : option stacks :=
  for_each α l n true (λ stk, dealloc1 stk tg cids ;; Some []).

Definition unsafe_action
  {A: Type} (f: A → loc → nat → bool → option A) (a: A) (l: loc)
  (last frozen_size unsafe_size: nat) :
  option (A * (nat * nat)) :=
  (* Anything between the last UnsafeCell and this UnsafeCell is frozen *)
  a' ← f a (l +ₗ last) frozen_size true;
  (* This UnsafeCell is not frozen *)
  let cur_off := (last + frozen_size)%nat in
    a'' ← f a' (l +ₗ cur_off) unsafe_size false ;
    Some (a'', ((cur_off + unsafe_size)%nat, O))
  .

(** Reborrow *)

(* visit the type left-to-right and apply the action `f`.
 + `last` is the offset of `l` from the last UnsafeCell,
 + `cur_dist` is the distance between `last` and the current offset of the
   visit, which is also the start of the sub-type `T`.
 + a` of type A is the accumulator for the visit.
 When an UnsafeCell is found, the action `f` is applied twice, through
 `unsafe_action`:
 - First `f` is applied for the frozen block, which is the range
   [last, last + cur_dist). `f` is applied with the boolean flag `true`
   (for frozen).
 - Then `f` is applied for the unfrozen block, which is the range
   [last + cur_dist, last + cur_dist + unsafe_block_size). `f` is applied with
   the boolean flag `false`. *)
Section def.
Context {A: Type}.
Local Unset Mangle Names. (* work around https://github.com/mattam82/Coq-Equations/issues/407 *)
Equations visit_freeze_sensitive'
  (l: loc) (f: A → loc → nat → bool → option A)
  (a: A) (last cur_dist: nat) (T: type) : option (A * (nat * nat)) :=
  visit_freeze_sensitive' l f a last cur_dist (FixedSize n) :=
    (* consider frozen, simply extend the distant by n *)
      Some (a, (last, cur_dist + n)%nat) ;
  visit_freeze_sensitive' l f a last cur_dist (Reference _ _) :=
    (* consider frozen, extend the distant by 1 *)
      Some (a, (last, S cur_dist)) ;
  visit_freeze_sensitive' l f a last cur_dist (Unsafe T) :=
    (* reach an UnsafeCell, apply the action `f` and return new `last` and
        `cur_dist` *)
      unsafe_action f a l last cur_dist (tsize T) ;
  visit_freeze_sensitive' l f a last cur_dist (Union Ts) :=
    (* If it's a union, look at the type to see if there is UnsafeCell *)
      if is_freeze (Union Ts)
      (* No UnsafeCell, consider the whole block frozen and simply extend the
          distant. *)
      then Some (a, (last, cur_dist + (tsize (Union Ts)))%nat)
      (* There can be UnsafeCell, consider the whole block of [Union Ts]
          unfrozen and perform `f a _ _ false` on the whole block.
          `unsafe_action` will return the offsets for the following visit. *)
      else unsafe_action f a l last cur_dist (tsize (Union Ts)) ;
  visit_freeze_sensitive' l f a last cur_dist (Product Ts) :=
    (* Try a shortcut *)
      if is_freeze (Product Ts)
      (* No UnsafeCell, consider the whole block frozen and simply extend the
        distant. *)
      then Some (a, (last, cur_dist + (tsize (Product Ts)))%nat)
      (* Perform a left-to-right search on [Product Ts], which guarantees
        that the offsets are increasing. *)
      else visit_LR a last cur_dist Ts
        where visit_LR (a: A) (last cur_dist: nat) (Ts: list type)
          : option (A * (nat * nat)) :=
          { visit_LR a' last' cur_dist' [] := Some (a', (last', cur_dist')) ;
            visit_LR a' last' cur_dist' (T' :: Ts') :=
              alc ← visit_freeze_sensitive' l f a' last' cur_dist' T' ;
              visit_LR alc.1 alc.2.1 alc.2.2 Ts' } ;
  visit_freeze_sensitive' l f a last cur_dist (Sum Ts) :=
    (* Try a shortcut *)
      if is_freeze (Sum Ts)
      (* No UnsafeCell, consider the whole block frozen and simply extend the
          distant. *)
      then Some (a, (last, cur_dist + (tsize (Sum Ts)))%nat)
      (* There can be UnsafeCell, consider the whole block of [Sum Ts] unfrozen
          and perform `f a _ _ false` on the whole block. `unsafe_action` will
          return the offsets for the following visit. *)
      else unsafe_action f a l last cur_dist (tsize (Sum Ts))
  .
End def.

Definition visit_freeze_sensitive {A: Type}
  (l: loc) (T: type) (f: A → loc → nat → bool → option A) (a: A) : option A :=
  match visit_freeze_sensitive' l f a O O T with
  | Some (a', (last', cur_dist')) =>
      (* the last block is frozen *)
      f a' (l +ₗ last') cur_dist' true
  | _ => None
  end.


(* Insert `it` into `stk` at `idx` unless `it` is equal to its neighbors. *)
Definition item_insert_dedup (stk: stack) (new: item) (idx: nat) : stack :=
  match idx with
  | O =>
    match stk with
    | [] => [new]
    | it' :: stk' => if decide (new = it') then stk else new :: stk
    end
  | S idx' =>
    match stk !! idx', stk !! idx with
    | None, None => take (S idx') stk ++ [new] ++ drop (S idx') stk
    | Some it_l, Some it_r =>
        if decide (new = it_l) then stk
        else if decide (new = it_r) then stk
             else take (S idx') stk ++ [new] ++ drop (S idx') stk
    | Some it, None | None, Some it =>
        if decide (new = it) then stk
        else take (S idx') stk ++ [new] ++ drop (S idx') stk
    end
  end.

(* Insert a `new` tag derived from a parent tag `derived_from`. *)
Definition grant
  (stk: stack) (derived_from: tag) (new: item) cids : option stack :=
  (* Figure out which access `new` allows *)
  let access := if grants new.(perm) AccessWrite then AccessWrite else AccessRead in
  (* Figure out which item grants our parent (`derived_from`) this kind of access *)
  idx_p ← find_granting stk access derived_from;
  match new.(perm) with
  | SharedReadWrite =>
    (* access is AccessWrite *)
    new_idx ← find_first_write_incompatible (take idx_p.1 stk) idx_p.2;
    Some (item_insert_dedup stk new new_idx)
  | _ =>
    (* an actual access check! *)
    nstk' ← access1 stk access derived_from cids;
    Some (item_insert_dedup nstk'.2 new O)
  end.

Definition reborrowN α cids l n old_tag new_tag pm prot :=
  let it := mkItem pm new_tag prot in
  for_each α l n false (λ stk, grant stk old_tag it cids).

(* This implements EvalContextPrivExt::reborrow *)
(* TODO?: alloc.check_bounds(this, ptr, size)?; *)
Definition reborrow α cids l (old_tag: tag) T (kind: ref_kind)
  (new_tag: tag) (protector: option call_id) :=
  match kind with
  | SharedRef | RawRef false =>
      (* for shared refs and const raw pointer, treat Unsafe as SharedReadWrite
        and Freeze as SharedReadOnly *)
      visit_freeze_sensitive l T
        (λ α' l' sz frozen,
          (* If is in Unsafe, use SharedReadWrite, otherwise SharedReadOnly *)
          let perm := if frozen then SharedReadOnly else SharedReadWrite in
          reborrowN α' cids l' sz old_tag new_tag perm protector) α
  | UniqueRef false =>
      (* mutable refs or Box use Unique *)
      reborrowN α cids l (tsize T) old_tag new_tag Unique protector
  | UniqueRef true | RawRef true =>
      (* mutable raw pointer uses SharedReadWrite *)
      reborrowN α cids l (tsize T) old_tag new_tag SharedReadWrite protector
  end.

(* Retag one pointer *)
(* This implements EvalContextPrivExt::retag_reference *)
Definition retag_ref α cids (nxtp: ptr_id) l (old_tag: tag) T
  (kind: ref_kind) (protector: option call_id)
  : option (tag * stacks * ptr_id) :=
  match tsize T with
  | O => (* Nothing to do for zero-sized types *)
      (* TODO: this can be handled by reborrow *)
      Some (old_tag, α, nxtp)
  | _ =>
      let new_tag := match kind with
                     | RawRef _ => Untagged
                     | _ => Tagged nxtp
                     end in
      (* reborrow old_tag with new_tag *)
      α' ← reborrow α cids l old_tag T kind new_tag protector;
      (* TODO: this always increments the [nxtp] field, even though that is not
        necessary when new_tag = Untagged *)
      Some (new_tag, α', S nxtp)
  end.

Definition adding_protector (kind: retag_kind) (c: call_id) : option call_id :=
  match kind with FnEntry => Some c | _ => None end.

(* This *partly* implements EvalContextExt::retag *)
(* Assumption: ct ∈ cids *)
Definition retag α (nxtp: ptr_id) (cids: call_id_set) (ct: call_id)
  (l: loc) (otag: tag) (kind: retag_kind) pk Tr :
  option (tag * stacks * ptr_id) :=
    let qualify : option (ref_kind * option call_id) :=
      match pk, kind with
      (* Mutable reference *)
      | RefPtr Mutable, _ =>
          Some (UniqueRef (is_two_phase kind), adding_protector kind ct)
      (* Immutable reference *)
      | RefPtr Immutable, _ => Some (SharedRef, adding_protector kind ct)
      (* If is both raw ptr and Raw retagging, no protector *)
      | RawPtr mut, RawRt => Some (RawRef (bool_decide (mut = Mutable)), None)
      (* Box pointer, no protector *)
      | BoxPtr, _ => Some (UniqueRef false, None)
      (* Ignore Raw pointer otherwise *)
      | RawPtr _, _ => None
      end in
    match qualify with
    | Some (rkind, protector) => retag_ref α cids nxtp l otag Tr rkind protector
    | None => Some (otag, α, nxtp)
    end
    .

Definition tag_included (tg: tag) (nxtp: ptr_id) : Prop :=
  match tg with
  | Tagged t => (t < nxtp)%nat
  | _ => True
  end.
Infix "<t" := tag_included (at level 60, no associativity).
Definition tag_values_included (v: value) nxtp :=
  ∀ l tg, ScPtr l tg ∈ v → tg <t nxtp.
Infix "<<t" := tag_values_included (at level 60, no associativity).

Global Instance tag_included_dec tg nxtp : Decision (tag_included tg nxtp).
Proof. destruct tg; cbn; apply _. Qed.
Global Instance tag_values_included_dec v nxtp : Decision (tag_values_included v nxtp).
Proof.
  rewrite /tag_values_included. induction v as [ | sc v IH].
  - left; intros l tg Ha. exfalso. by eapply not_elem_of_nil.
  - destruct sc as [| |l tg| |].
    1,2,4,5: destruct IH as [IH | IH]; [left | right]; setoid_rewrite elem_of_cons; [intros ?? [ [=] | ]| contradict IH]; eauto.
    destruct (decide (tg <t nxtp)) as [Hd | Hd]; destruct IH as [IH | IH]; [left | right | right | right]; setoid_rewrite elem_of_cons; [ | by eauto..].
    intros ?? [[= -> ->] | He]; [done | by eapply IH].
Qed.

(** Instrumented step for the stacked borrows *)
(* This ignores CAS for now. *)
Inductive bor_step (α : stacks) (cids: gset call_id) (nxtp: ptr_id) (nxtc: call_id):
  event → stacks → call_id_set → ptr_id → call_id → Prop :=
(* | SysCallIS id :
    bor_step h α β nxtp (SysCallEvt id) h α β nxtp *)
(* This implements EvalContextExt::new_allocation. *)
| AllocIS x T :
    (* Tagged nxtp is the first borrow of the variable x,
       used when accessing x directly (not through another pointer) *)
    bor_step α cids nxtp nxtc
              (AllocEvt x (Tagged nxtp) T)
              (init_stacks α x (tsize T) (Tagged nxtp)) cids (S nxtp) nxtc
(* This implements AllocationExtra::memory_read. *)
| CopyIS α' l lbor T vl
    (ACC: memory_read α cids l lbor (tsize T) = Some α') :
    bor_step α cids nxtp nxtc (CopyEvt l lbor T vl) α' cids nxtp nxtc
(* Failing Copy when the stack access is not granted, yielding poison *)
| CopyFailIS l lbor T
    (ACC : memory_read α cids l lbor (tsize T) = None) :
    bor_step α cids nxtp nxtc (FailedCopyEvt l lbor T) α cids nxtp nxtc
(* This implements AllocationExtra::memory_written. *)
| WriteIS α' l lbor T vl
    (ACC: memory_written α cids l lbor (tsize T) = Some α') :
    bor_step α cids nxtp nxtc (WriteEvt l lbor T vl) α' cids nxtp nxtc
(* This implements AllocationExtra::memory_deallocated. *)
| DeallocIS α' l lbor T
    (ACC: memory_deallocated α cids l lbor (tsize T) = Some α') :
    bor_step α cids nxtp nxtc (DeallocEvt l lbor T) α' cids nxtp nxtc
| InitCallIS :
    bor_step α cids nxtp nxtc (InitCallEvt nxtc) α ({[nxtc]} ∪ cids) nxtp (S nxtc)
| EndCallIS c
    (EL: c ∈ cids) :
    bor_step α cids nxtp nxtc (EndCallEvt c) α (cids ∖ {[c]}) nxtp nxtc
| RetagIS α' nxtp' l otag ntag T kind pkind c
    (EL: c ∈ cids)
    (RETAG: retag α nxtp cids c l otag kind pkind T = Some (ntag, α', nxtp')) :
    bor_step α cids nxtp nxtc (RetagEvt l otag ntag pkind T kind c) α' cids nxtp' nxtc.

