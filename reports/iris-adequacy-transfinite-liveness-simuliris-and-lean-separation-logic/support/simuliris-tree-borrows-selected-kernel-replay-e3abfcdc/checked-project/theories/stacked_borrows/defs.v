(** This file has been adapted from the Stacked Borrows development, available at 
  https://gitlab.mpi-sws.org/FP/stacked-borrows
*)

From iris.prelude Require Export prelude.
From simuliris.stacked_borrows Require Export tactics notation lang bor_semantics.

(* Henceforth also in the files importing us we want to use Z_scope. *)
Global Open Scope Z_scope.

Definition wf_mem_tag (h: mem) (nxtp: ptr_id) :=
  ∀ l l' pid, h !! l = Some (ScPtr l' (Tagged pid)) → (pid < nxtp)%nat.

Definition stack_item_included (stk: stack) (nxtp: ptr_id) (nxtc: call_id) :=
  ∀ si, si ∈ stk → match si.(tg) with
                    | Tagged t => (t < nxtp)%nat
                    | _ => True
                   end ∧
                   match si.(protector) with
                    | Some c => (c < nxtc)%nat
                    | _ => True
                   end.

Definition is_tagged (it: item) :=
  match it.(tg) with Tagged _ => True | _ => False end.
Global Instance is_tagged_dec it: Decision (is_tagged it).
Proof. intros. rewrite /is_tagged. case tg; solve_decision. Defined.
Definition stack_item_tagged_NoDup (stk : stack) :=
  NoDup (fmap tg (filter is_tagged stk)).

Definition wf_stack (stk: stack) (nxtp: ptr_id) (nxtc: call_id) :=
  stack_item_included stk nxtp nxtc ∧ stack_item_tagged_NoDup stk.
Definition wf_stacks (α: stacks) (nxtp: ptr_id) (nxtc: call_id) :=
  ∀ l stk, α !! l = Some stk → wf_stack stk nxtp nxtc.
Definition wf_non_empty (α: stacks) :=
  ∀ l stk, α !! l = Some stk → stk ≠ [].
Definition wf_no_dup (α: stacks) :=
  ∀ l stk, α !! l = Some stk → NoDup stk.
Definition wf_cid_incl (cids: call_id_set) (nxtc: call_id) :=
  ∀ c : call_id, c ∈ cids → (c < nxtc)%nat.
Definition wf_scalar t sc := ∀ t' l, sc = ScPtr l t' → t' <t t.

Record state_wf (s: state) := {
  state_wf_dom : dom s.(shp) ≡ dom s.(sst);
  (*state_wf_mem_tag : wf_mem_tag s.(shp) s.(snp);*)
  state_wf_stack_item : wf_stacks s.(sst) s.(snp) s.(snc);
  state_wf_non_empty : wf_non_empty s.(sst);
  (*state_wf_cid_no_dup : NoDup s.(scs) ;*)
  state_wf_cid_agree: wf_cid_incl s.(scs) s.(snc);
  (* state_wf_cid_non_empty : s.(scs) ≠ []; *)
  (* state_wf_no_dup : wf_no_dup σ.(cst).(sst); *)
}.

Fixpoint active_SRO (stk: stack) : gset ptr_id :=
  match stk with
  | [] => ∅
  | it :: stk =>
    match it.(perm) with
    | SharedReadOnly => match it.(tg) with
                        | Tagged t => {[t]} ∪ active_SRO stk
                        | Untagged => active_SRO stk
                        end
    | _ => ∅
    end
  end.


Definition init_state := (mkState ∅ ∅ {[O]} O 1).


Inductive tag_kind := tk_pub  | tk_unq | tk_local.

Definition state_upd_mem (f : mem → mem) σ :=
  mkState (f σ.(shp)) σ.(sst) σ.(scs) σ.(snp) σ.(snc).
Definition state_upd_stacks (f : stacks → stacks) σ :=
  mkState σ.(shp) (f σ.(sst)) σ.(scs) σ.(snp) σ.(snc).
Definition state_upd_calls (f : call_id_set → call_id_set) σ :=
  mkState σ.(shp) σ.(sst) (f σ.(scs)) σ.(snp) σ.(snc).
