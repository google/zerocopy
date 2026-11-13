/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Compositional Reborrow and Two-Stage Tree Borrows Protector Release

This self-contained Lean 4 module mechanizes:

1. The 5-state Tree Borrows permission automaton (`Permission`: `reserved`,
   `active`, `frozen`, `cell`, `disabled`), per-byte `LocationState` (`perm`,
   `accessed`), `ProtectorKind` (`weak`, `strong`), `AccessKind` (`read`,
   `write`), `AccessRelatedness` (`localAccess`, `foreignAccess`), and
   `Permission.associatedAccess` matching
   `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`
   (`Miri/TreeBorrows/Permissions.lean`, `Miri/TreeBorrows/LocationState.lean`)
   and `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`
   (`src/borrow_tracker/tree_borrows/perms.rs`).
2. Arbitrary-depth, arbitrary-branching `BorrowTree` with `retag` child
   insertion (`enterCallBoundary` with `FnEntry` protector and unprotected
   `Default` reborrows on sub-ranges) and two-stage protector release
   (`releaseProtector` with `SkipChildrenOfAccessed` while the tag's frame is
   still protected, followed by removing the frame from `activeProtectors`).
3. The compositional relational invariant
   `HasUniqueWritePerm tree tag range activeProtectors`.
4. Kernel-checked proofs of:
   - `reborrow_return_unique_write_perm`: Calling a function
     `get_mut(x: &mut Pair) -> &mut u32` that retags `x` (`t_parent`) into a
     `FnEntry`-protected child `t_arg` on `parentRange`, creates an unprotected
     child `t_ret` under `t_arg` on `subRange ⊆ parentRange` without writing,
     and runs two-stage `releaseProtector` on `t_arg` succeeds without
     undefined behavior (UB) and establishes
     `HasUniqueWritePerm tree_post t_ret subRange activeCaller` in the
     caller—even when `t_parent` or an outer ancestor `t_outer` is
     `Strong`-protected by an enclosing caller frame—and subsequent caller
     writes through `t_ret` on `subRange` activate `t_ret`, `t_arg`,
     `t_parent`, and `t_outer` without protector UB.
   - `reborrow_return_after_callee_write_unique_write_perm`: The same guarantee
     when the callee writes through `t_ret` on `subRange` before returning (so
     `t_arg` is `.active` on `subRange` and `.reserved` on
     `parentRange \ subRange`, emitting an implicit `Write` on `subRange` and
     an implicit `Read` on `parentRange \ subRange` under
     `SkipChildrenOfAccessed`).
   - `split_at_mut_unique_write_perm`: Creating two disjoint child tags
     `t_left` on `leftRange` and `t_right` on `rightRange`
     (`leftRange ∩ rightRange = ∅`, `leftRange ∪ rightRange ⊆ parentRange`)
     under `t_arg` and releasing `t_arg`'s protector establishes **both**
     `HasUniqueWritePerm tree_post t_left leftRange activeCaller` and
     `HasUniqueWritePerm tree_post t_right rightRange activeCaller`
     simultaneously, and writing through (or `FnEntry`-retagging) `t_left` on
     `leftRange` preserves `HasUniqueWritePerm` for `t_right` on `rightRange`
     (and vice versa).
   - `same_tag_split_unsound_control` and `trustedSpec_reborrow_equivalence`:
     Negative-control theorem demonstrating why modular function contracts
     (`TrustedFnSpec`) for functions returning reborrowed references
     (`get_mut`, `slice::split_at_mut`, `IterMut::next`) must include a
     deterministic `ReborrowEdge` / `ReborrowSpec` transition that mints fresh
     child tags rather than reusing `t_arg` or leaving `BorrowTree` unchanged.
-/

namespace CompositionalReborrowProtectorProbe

abbrev BorTag := Nat
abbrev CallId := Nat
abbrev ByteOffset := Nat
abbrev ByteRange := ByteOffset → Bool

def SubRange (r1 r2 : ByteRange) : Prop :=
  ∀ b, r1 b = true → r2 b = true

def DisjointRange (r1 r2 : ByteRange) : Prop :=
  ∀ b, r1 b = true → r2 b = false

theorem disjointRange_symm {r1 r2 : ByteRange} (h : DisjointRange r1 r2) : DisjointRange r2 r1 := by
  intro b hb2
  cases hb1 : r1 b with
  | false => rfl
  | true =>
    have h2f := h b hb1
    rw [hb2] at h2f
    contradiction

/-! ## 1. 5-State Permission Lattice & Per-Location Automaton -/

/-- The 5 permission states of Tree Borrows (with `reserved` parameterized by
`tyIsFreeze` and `conflicted`, matching `Permission.ReservedFrz` /
`Permission.ReservedIM` in `lean-miri` and
`Reserved { ty_is_freeze, conflicted }` in `rust-lang/miri`). -/
inductive Permission where
  | reserved (tyIsFreeze : Bool) (conflicted : Bool)
  | active
  | frozen
  | cell
  | disabled
  deriving DecidableEq, Repr

/-- Per-location (per-byte) state of a `BorTag` in a `BorrowTree`. -/
structure LocationState where
  perm : Permission
  accessed : Bool
  deriving DecidableEq, Repr

inductive AccessKind where
  | read
  | write
  deriving DecidableEq, Repr

inductive AccessRelatedness where
  | localAccess
  | foreignAccess
  deriving DecidableEq, Repr

inductive ProtectorKind where
  | weak (callId : CallId)
  | strong (callId : CallId)
  deriving DecidableEq, Repr

def ProtectorKind.callId : ProtectorKind → CallId
  | .weak id => id
  | .strong id => id

/-- Implicit access kind emitted on protector release for an `accessed = true`
location. Matches `Permission.associatedAccess` in
`Miri/TreeBorrows/Permissions.lean:268-271` and
`Permission::protector_end_access` in
`src/borrow_tracker/tree_borrows/perms.rs:311-319`. -/
def Permission.associatedAccess : Permission → Option AccessKind
  | .cell => none
  | .active => some .write
  | .reserved _ _ | .frozen | .disabled => some .read

/-- Single-step permission transition `performTransition` matching
`Miri/TreeBorrows/Permissions.lean:62-112` and
`Miri/TreeBorrows/LocationState.lean:128-161`. Returns `none` on UB
(`ChildAccessForbidden` or `ProtectedDisabled`). -/
def performTransition
    (kind : AccessKind)
    (rel : AccessRelatedness)
    (isProtected : Bool)
    (st : LocationState) : Option LocationState :=
  match rel, kind with
  | .localAccess, .read =>
    match st.perm with
    | .reserved frz conf => some ⟨.reserved frz conf, true⟩
    | .active => some ⟨.active, true⟩
    | .frozen => some ⟨.frozen, true⟩
    | .cell => some ⟨.cell, true⟩
    | .disabled => none
  | .localAccess, .write =>
    match st.perm with
    | .reserved _ true =>
      if isProtected then none else some ⟨.active, true⟩
    | .reserved _ false => some ⟨.active, true⟩
    | .active => some ⟨.active, true⟩
    | .cell => some ⟨.cell, true⟩
    | .frozen | .disabled => none
  | .foreignAccess, .read =>
    match st.perm with
    | .reserved true conf =>
      some ⟨.reserved true (isProtected || conf), st.accessed⟩
    | .reserved false _ =>
      some ⟨.reserved false false, st.accessed⟩
    | .active =>
      if isProtected then none else some ⟨.frozen, st.accessed⟩
    | .frozen => some ⟨.frozen, st.accessed⟩
    | .cell => some ⟨.cell, st.accessed⟩
    | .disabled => some ⟨.disabled, st.accessed⟩
  | .foreignAccess, .write =>
    match st.perm with
    | .reserved true _ =>
      if isProtected && st.accessed then none else some ⟨.disabled, st.accessed⟩
    | .reserved false _ =>
      if isProtected then
        if st.accessed then none else some ⟨.disabled, st.accessed⟩
      else
        some ⟨.reserved false false, st.accessed⟩
    | .active | .frozen =>
      if isProtected && st.accessed then none else some ⟨.disabled, st.accessed⟩
    | .cell => some ⟨.cell, st.accessed⟩
    | .disabled =>
      if isProtected && st.accessed then none else some ⟨.disabled, st.accessed⟩

/-! ## 2. Arbitrary-Depth, Arbitrary-Branching `BorrowTree` & Tree Traversal Modes -/

/-- Visitor mode for `BorrowTree` accesses (`Miri/TreeBorrows/Traversal.lean:28-31`,
`src/borrow_tracker/tree_borrows/tree_visitor.rs:248-268`). -/
inductive ChildrenVisitMode where
  | visitChildrenOfAccessed
  | skipChildrenOfAccessed
  deriving DecidableEq, Repr

/-- Arbitrary-depth, arbitrary-branching borrow tree for an allocation. -/
structure BorrowTree where
  present : BorTag → Bool
  isAnc : BorTag → BorTag → Bool
  protector : BorTag → Option ProtectorKind
  locState : BorTag → ByteOffset → LocationState

/-- Well-formedness of the tree ancestry partial order on `BorrowTree`,
including the tree-linearity property (`anc_linear`): any two ancestors of the
same node `c` are comparable. -/
structure TreeWF (tree : BorrowTree) : Prop where
  isAnc_refl : ∀ t, tree.present t = true → tree.isAnc t t = true
  isAnc_trans : ∀ a b c, tree.isAnc a b = true → tree.isAnc b c = true → tree.isAnc a c = true
  isAnc_antisymm : ∀ a b, tree.isAnc a b = true → tree.isAnc b a = true → a = b
  isAnc_present_left : ∀ a b, tree.isAnc a b = true → tree.present a = true
  isAnc_present_right : ∀ a b, tree.isAnc a b = true → tree.present b = true
  anc_linear : ∀ a b c, tree.isAnc a c = true → tree.isAnc b c = true →
    tree.isAnc a b = true ∨ tree.isAnc b a = true

abbrev ActiveProtectors := CallId → Bool

def BorrowTree.isTagProtected (tree : BorrowTree) (t : BorTag) (active : ActiveProtectors) : Bool :=
  match tree.protector t with
  | some p => active p.callId
  | none => false

/-- Relatedness of node `n` to an access at `start` under `mode`, matching
`TraversalTree.traverse` (`Miri/TreeBorrows/Traversal.lean:70-112`). -/
def nodeAccessRelatedness
    (tree : BorrowTree)
    (start : BorTag)
    (mode : ChildrenVisitMode)
    (n : BorTag) : Option AccessRelatedness :=
  if tree.isAnc n start then
    some .localAccess
  else match mode with
    | .visitChildrenOfAccessed => some .foreignAccess
    | .skipChildrenOfAccessed =>
      if tree.isAnc start n then none else some .foreignAccess

/-- Proposition that a tree access of `kind` at `start` over `range` under
`mode` causes no UB on any present node in `tree`. -/
def TreeAccessNoUB
    (tree : BorrowTree)
    (start : BorTag)
    (kind : AccessKind)
    (range : ByteRange)
    (active : ActiveProtectors)
    (mode : ChildrenVisitMode) : Prop :=
  ∀ n b, tree.present n = true → range b = true →
    match nodeAccessRelatedness tree start mode n with
    | some rel =>
      (performTransition kind rel (tree.isTagProtected n active) (tree.locState n b)).isSome = true
    | none => True

/-- Total update of `BorrowTree` for an access of `kind` at `start` over
`range` under `mode`. -/
def applyTreeAccess
    (tree : BorrowTree)
    (start : BorTag)
    (kind : AccessKind)
    (range : ByteRange)
    (active : ActiveProtectors)
    (mode : ChildrenVisitMode) : BorrowTree where
  present := tree.present
  isAnc := tree.isAnc
  protector := tree.protector
  locState := fun n b =>
    if tree.present n && range b then
      match nodeAccessRelatedness tree start mode n with
      | some rel =>
        match performTransition kind rel (tree.isTagProtected n active) (tree.locState n b) with
        | some st' => st'
        | none => tree.locState n b
      | none => tree.locState n b
    else
      tree.locState n b

@[simp]
theorem applyTreeAccess_present
    (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode) :
    (applyTreeAccess tree start kind range active mode).present = tree.present := rfl

@[simp]
theorem applyTreeAccess_isAnc
    (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode) :
    (applyTreeAccess tree start kind range active mode).isAnc = tree.isAnc := rfl

@[simp]
theorem applyTreeAccess_protector
    (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode) :
    (applyTreeAccess tree start kind range active mode).protector = tree.protector := rfl

@[simp]
theorem applyTreeAccess_isTagProtected
    (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode)
    (n : BorTag) (act2 : ActiveProtectors) :
    (applyTreeAccess tree start kind range active mode).isTagProtected n act2 =
      tree.isTagProtected n act2 := rfl

theorem applyTreeAccess_locState_in
    (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode)
    (n : BorTag) (b : ByteOffset) (hPres : tree.present n = true) (hb : range b = true) :
    (applyTreeAccess tree start kind range active mode).locState n b =
      match nodeAccessRelatedness tree start mode n with
      | some rel =>
        match performTransition kind rel (tree.isTagProtected n active) (tree.locState n b) with
        | some st' => st'
        | none => tree.locState n b
      | none => tree.locState n b := by
  simp [applyTreeAccess, hPres, hb]

theorem applyTreeAccess_locState_out
    (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode)
    (n : BorTag) (b : ByteOffset) (hb : range b = false) :
    (applyTreeAccess tree start kind range active mode).locState n b = tree.locState n b := by
  simp [applyTreeAccess, hb]

/-- Raw child insertion into `BorrowTree` prior to the initial child read of
`retag`. -/
def insertChildNode
    (tree : BorrowTree)
    (t_parent t_child : BorTag)
    (prot : Option ProtectorKind)
    (initPerm : Permission) : BorrowTree where
  present := fun t => (t == t_child) || tree.present t
  isAnc := fun a d =>
    if d == t_child then
      (a == t_child) || tree.isAnc a t_parent
    else if a == t_child then
      false
    else
      tree.isAnc a d
  protector := fun t => if t == t_child then prot else tree.protector t
  locState := fun t b =>
    if t == t_child then ⟨initPerm, false⟩ else tree.locState t b

/-- Full `retag` operation (`Miri/TreeBorrows/TreeState.lean:943-975`,
`RetagPipeline.lean:254-309`): inserts `t_child` under `t_parent` with `prot`
and `initPerm`, then performs a `Child Read` (`visitChildrenOfAccessed`)
through `t_child` over `range`. -/
def retagChild
    (tree : BorrowTree)
    (t_parent t_child : BorTag)
    (prot : Option ProtectorKind)
    (initPerm : Permission)
    (range : ByteRange)
    (active : ActiveProtectors) : BorrowTree :=
  let tree1 := insertChildNode tree t_parent t_child prot initPerm
  applyTreeAccess tree1 t_child .read range active .visitChildrenOfAccessed

/-- Stage 1 of two-stage protector release (`BorrowTree.releaseProtector` in
`Miri/TreeBorrows/TreeState.lean:1036-1070`, `perform_protector_end_access` in
`src/borrow_tracker/tree_borrows/tree.rs:671-727`). -/
def releaseProtectorNoUB
    (tree : BorrowTree)
    (t_rel : BorTag)
    (active : ActiveProtectors) : Prop :=
  ∀ n b, tree.present n = true →
    (tree.locState t_rel b).accessed = true →
    ∀ kind, (tree.locState t_rel b).perm.associatedAccess = some kind →
      match nodeAccessRelatedness tree t_rel .skipChildrenOfAccessed n with
      | some rel =>
        (performTransition kind rel (tree.isTagProtected n active) (tree.locState n b)).isSome = true
      | none => True

def applyReleaseProtector
    (tree : BorrowTree)
    (t_rel : BorTag)
    (active : ActiveProtectors) : BorrowTree where
  present := tree.present
  isAnc := tree.isAnc
  protector := tree.protector
  locState := fun n b =>
    if tree.present n && (tree.locState t_rel b).accessed then
      match (tree.locState t_rel b).perm.associatedAccess with
      | some kind =>
        match nodeAccessRelatedness tree t_rel .skipChildrenOfAccessed n with
        | some rel =>
          match performTransition kind rel (tree.isTagProtected n active) (tree.locState n b) with
          | some st' => st'
          | none => tree.locState n b
        | none => tree.locState n b
      | none => tree.locState n b
    else
      tree.locState n b

@[simp]
theorem applyReleaseProtector_present
    (tree : BorrowTree) (t_rel : BorTag) (active : ActiveProtectors) :
    (applyReleaseProtector tree t_rel active).present = tree.present := rfl

@[simp]
theorem applyReleaseProtector_isAnc
    (tree : BorrowTree) (t_rel : BorTag) (active : ActiveProtectors) :
    (applyReleaseProtector tree t_rel active).isAnc = tree.isAnc := rfl

@[simp]
theorem applyReleaseProtector_protector
    (tree : BorrowTree) (t_rel : BorTag) (active : ActiveProtectors) :
    (applyReleaseProtector tree t_rel active).protector = tree.protector := rfl

@[simp]
theorem applyReleaseProtector_isTagProtected
    (tree : BorrowTree) (t_rel : BorTag) (active : ActiveProtectors)
    (n : BorTag) (act2 : ActiveProtectors) :
    (applyReleaseProtector tree t_rel active).isTagProtected n act2 =
      tree.isTagProtected n act2 := rfl

theorem applyReleaseProtector_locState_acc
    (tree : BorrowTree) (t_rel : BorTag) (active : ActiveProtectors)
    (n : BorTag) (b : ByteOffset)
    (hPres : tree.present n = true)
    (hAcc : (tree.locState t_rel b).accessed = true) :
    (applyReleaseProtector tree t_rel active).locState n b =
      match (tree.locState t_rel b).perm.associatedAccess with
      | some kind =>
        match nodeAccessRelatedness tree t_rel .skipChildrenOfAccessed n with
        | some rel =>
          match performTransition kind rel (tree.isTagProtected n active) (tree.locState n b) with
          | some st' => st'
          | none => tree.locState n b
        | none => tree.locState n b
      | none => tree.locState n b := by
  simp [applyReleaseProtector, hPres, hAcc]

theorem applyReleaseProtector_locState_unacc
    (tree : BorrowTree) (t_rel : BorTag) (active : ActiveProtectors)
    (n : BorTag) (b : ByteOffset)
    (hAcc : (tree.locState t_rel b).accessed = false) :
    (applyReleaseProtector tree t_rel active).locState n b = tree.locState n b := by
  simp [applyReleaseProtector, hAcc]

/-- Stage 2 of protector release (`GlobalState.endCall` in
`Miri/TreeBorrows/GlobalState.lean:146-148`, `end_call` in
`src/borrow_tracker/mod.rs:181-190`): removes `callId` from `activeProtectors`. -/
def removeActiveProtector (active : ActiveProtectors) (callId : CallId) : ActiveProtectors :=
  fun c => if c == callId then false else active c

def insertActiveProtector (active : ActiveProtectors) (callId : CallId) : ActiveProtectors :=
  fun c => (c == callId) || active c

/-! ## 3. The Compositional `HasUniqueWritePerm` Invariant -/

/-- A location state on an ancestor of `tag` supports both local reads and local
writes without protector conflict (`Active` or unconflicted `Reserved`). -/
def AncestorWritable (st : LocationState) : Prop :=
  st.perm = .active ∨ ∃ frz, st.perm = .reserved frz false

/-- A location state on a non-ancestor of `tag` will not trap under foreign
reads or writes. -/
def NonAncestorSafe (st : LocationState) (isProt : Bool) : Prop :=
  isProt = false ∨ st.perm = .cell ∨ (st.accessed = false ∧ st.perm ≠ .active)

/-- Relational unique-write permission invariant for `tag` over `range` under
`active` protectors. -/
structure HasUniqueWritePerm
    (tree : BorrowTree)
    (tag : BorTag)
    (range : ByteRange)
    (active : ActiveProtectors) : Prop where
  wf : TreeWF tree
  tag_present : tree.present tag = true
  ancestors_writable :
    ∀ anc b, tree.isAnc anc tag = true → range b = true →
      AncestorWritable (tree.locState anc b)
  non_ancestors_safe :
    ∀ other b, tree.present other = true → tree.isAnc other tag = false → range b = true →
      NonAncestorSafe (tree.locState other b) (tree.isTagProtected other active)

/-! ## 4. Fundamental Lemmas for `AncestorWritable`, `NonAncestorSafe`, and `TreeWF` -/

theorem performTransition_local_read_of_ancestorWritable
    (isProt : Bool) (st : LocationState) (h : AncestorWritable st) :
    performTransition .read .localAccess isProt st = some ⟨st.perm, true⟩ ∧
      AncestorWritable ⟨st.perm, true⟩ := by
  rcases st with ⟨perm, acc⟩
  rcases h with hAct | ⟨frz, hRes⟩
  · cases hAct
    exact ⟨rfl, Or.inl rfl⟩
  · cases hRes
    exact ⟨rfl, Or.inr ⟨frz, rfl⟩⟩

theorem performTransition_local_write_of_ancestorWritable
    (isProt : Bool) (st : LocationState) (h : AncestorWritable st) :
    performTransition .write .localAccess isProt st = some ⟨.active, true⟩ ∧
      AncestorWritable ⟨.active, true⟩ := by
  rcases st with ⟨perm, acc⟩
  rcases h with hAct | ⟨frz, hRes⟩
  · cases hAct
    exact ⟨rfl, Or.inl rfl⟩
  · cases hRes
    exact ⟨rfl, Or.inl rfl⟩

theorem associatedAccess_of_ancestorWritable
    (st : LocationState) (h : AncestorWritable st) :
    ∃ kind, st.perm.associatedAccess = some kind := by
  rcases st with ⟨perm, acc⟩
  rcases h with hAct | ⟨frz, hRes⟩
  · cases hAct
    exact ⟨.write, rfl⟩
  · cases hRes
    exact ⟨.read, rfl⟩

theorem performTransition_local_of_ancestorWritable
    (kind : AccessKind) (isProt : Bool) (st : LocationState) (h : AncestorWritable st) :
    ∃ st', performTransition kind .localAccess isProt st = some st' ∧
      AncestorWritable st' ∧ st'.accessed = true := by
  cases kind with
  | read =>
    obtain ⟨hEq, hAw⟩ := performTransition_local_read_of_ancestorWritable isProt st h
    exact ⟨⟨st.perm, true⟩, hEq, hAw, rfl⟩
  | write =>
    obtain ⟨hEq, hAw⟩ := performTransition_local_write_of_ancestorWritable isProt st h
    exact ⟨⟨.active, true⟩, hEq, hAw, rfl⟩

theorem performTransition_foreign_of_nonAncestorSafe
    (kind : AccessKind) (isProt : Bool) (st : LocationState)
    (h : NonAncestorSafe st isProt) :
    ∃ st', performTransition kind .foreignAccess isProt st = some st' ∧
      NonAncestorSafe st' isProt ∧ st'.accessed = st.accessed := by
  rcases st with ⟨perm, acc⟩
  rcases h with hUnprot | hCell | ⟨hUnacc, hNotAct⟩
  · subst hUnprot
    cases kind <;> cases perm
    · rename_i frz conf
      cases frz <;> exact ⟨_, rfl, Or.inl rfl, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl, rfl⟩
    · rename_i frz conf
      cases frz <;> exact ⟨_, rfl, Or.inl rfl, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl, rfl⟩
  · simp only at hCell
    subst hCell
    cases kind <;> exact ⟨⟨.cell, acc⟩, rfl, Or.inr (Or.inl rfl), rfl⟩
  · simp only at hUnacc hNotAct
    subst hUnacc
    cases kind with
    | read =>
      cases perm with
      | reserved frz conf =>
        cases frz <;> exact ⟨_, rfl, Or.inr (Or.inr ⟨rfl, by intro h; injection h⟩), rfl⟩
      | active => exact False.elim (hNotAct rfl)
      | frozen => exact ⟨_, rfl, Or.inr (Or.inr ⟨rfl, by intro h; injection h⟩), rfl⟩
      | cell => exact ⟨_, rfl, Or.inr (Or.inl rfl), rfl⟩
      | disabled => exact ⟨_, rfl, Or.inr (Or.inr ⟨rfl, by intro h; injection h⟩), rfl⟩
    | write =>
      cases perm with
      | reserved frz conf =>
        cases frz <;> cases isProt <;>
          exact ⟨_, rfl, Or.inr (Or.inr ⟨rfl, by intro h; injection h⟩), rfl⟩
      | active => exact False.elim (hNotAct rfl)
      | frozen =>
        cases isProt <;> exact ⟨_, rfl, Or.inr (Or.inr ⟨rfl, by intro h; injection h⟩), rfl⟩
      | cell => exact ⟨_, rfl, Or.inr (Or.inl rfl), rfl⟩
      | disabled =>
        cases isProt <;> exact ⟨_, rfl, Or.inr (Or.inr ⟨rfl, by intro h; injection h⟩), rfl⟩

theorem nonAncestorSafe_mono_unprotect
    (st : LocationState) (isProt1 isProt2 : Bool)
    (hSafe : NonAncestorSafe st isProt1)
    (hImp : isProt2 = true → isProt1 = true) :
    NonAncestorSafe st isProt2 := by
  rcases hSafe with hUnprot | hCell | hUnacc
  · left
    cases h2 : isProt2 with
    | false => rfl
    | true =>
      have h1 := hImp h2
      rw [hUnprot] at h1
      contradiction
  · exact Or.inr (Or.inl hCell)
  · exact Or.inr (Or.inr hUnacc)

theorem insertChildNode_wf
    (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (initPerm : Permission)
    (hwf : TreeWF tree)
    (hFresh : tree.present t_child = false) :
    TreeWF (insertChildNode tree t_parent t_child prot initPerm) := by
  have hNeParent : ∀ x, tree.present x = true → x ≠ t_child := by
    intro x hx hEq
    rw [hEq] at hx
    rw [hFresh] at hx
    contradiction
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp only [insertChildNode] at ht ⊢
    by_cases htc : t = t_child
    · rw [htc]; simp
    · simp [htc] at ht ⊢
      exact hwf.isAnc_refl t ht
  · intro a b c hab hbc
    simp only [insertChildNode] at hab hbc ⊢
    by_cases hct : c = t_child
    · rw [hct] at hbc ⊢
      simp at hbc ⊢
      rcases hbc with hbc_eq | hbt
      · rw [hbc_eq] at hab
        simp at hab
        exact hab
      · have hbc_ne : b ≠ t_child := hNeParent b (hwf.isAnc_present_left b t_parent hbt)
        simp [hbc_ne] at hab
        by_cases hat : a = t_child
        · rw [hat] at hab; simp at hab
        · simp [hat] at hab ⊢
          exact hwf.isAnc_trans a b t_parent hab hbt
    · simp [hct] at hbc ⊢
      by_cases hbt : b = t_child
      · rw [hbt] at hbc; simp at hbc
      · simp [hbt] at hab hbc
        by_cases hat : a = t_child
        · rw [hat] at hab; simp at hab
        · simp [hat] at hab ⊢
          exact hwf.isAnc_trans a b c hab hbc
  · intro a b hab hba
    simp only [insertChildNode] at hab hba
    by_cases hbt : b = t_child
    · rw [hbt] at hab hba ⊢
      by_cases hat : a = t_child
      · exact hat
      · simp [hat] at hab hba
    · by_cases hat : a = t_child
      · rw [hat] at hab
        simp [hbt] at hab
      · simp [hbt, hat] at hab hba
        exact hwf.isAnc_antisymm a b hab hba
  · intro a b hab
    simp only [insertChildNode] at hab ⊢
    by_cases hbt : b = t_child
    · rw [hbt] at hab
      simp at hab
      rcases hab with hab_eq | hap
      · rw [hab_eq]; simp
      · simp [hwf.isAnc_present_left a t_parent hap]
    · by_cases hat : a = t_child
      · rw [hat] at hab; simp [hbt] at hab
      · simp [hbt, hat] at hab ⊢
        exact hwf.isAnc_present_left a b hab
  · intro a b hab
    simp only [insertChildNode] at hab ⊢
    by_cases hbt : b = t_child
    · rw [hbt]; simp
    · by_cases hat : a = t_child
      · rw [hat] at hab; simp [hbt] at hab
      · simp [hbt, hat] at hab ⊢
        exact hwf.isAnc_present_right a b hab
  · intro a b c hac hbc
    simp only [insertChildNode] at hac hbc ⊢
    by_cases hct : c = t_child
    · rw [hct] at hac hbc
      simp at hac hbc
      rcases hac with hac_eq | hap
      · rw [hac_eq]
        right
        simp [hbc]
      · have ha_ne : a ≠ t_child := hNeParent a (hwf.isAnc_present_left a t_parent hap)
        rcases hbc with hbc_eq | hbp
        · rw [hbc_eq]
          left
          simp [hap]
        · have hb_ne : b ≠ t_child := hNeParent b (hwf.isAnc_present_left b t_parent hbp)
          simp [ha_ne, hb_ne]
          exact hwf.anc_linear a b t_parent hap hbp
    · simp [hct] at hac hbc
      by_cases hat : a = t_child
      · rw [hat] at hac; simp at hac
      · by_cases hbt : b = t_child
        · rw [hbt] at hbc; simp at hbc
        · simp [hat, hbt] at hac hbc ⊢
          exact hwf.anc_linear a b c hac hbc

theorem applyTreeAccess_wf
    (tree : BorrowTree) (start : BorTag) (kind : AccessKind)
    (range : ByteRange) (active : ActiveProtectors) (mode : ChildrenVisitMode)
    (hwf : TreeWF tree) :
    TreeWF (applyTreeAccess tree start kind range active mode) :=
  ⟨hwf.isAnc_refl, hwf.isAnc_trans, hwf.isAnc_antisymm,
   hwf.isAnc_present_left, hwf.isAnc_present_right, hwf.anc_linear⟩

theorem applyReleaseProtector_wf
    (tree : BorrowTree) (t_rel : BorTag) (active : ActiveProtectors)
    (hwf : TreeWF tree) :
    TreeWF (applyReleaseProtector tree t_rel active) :=
  ⟨hwf.isAnc_refl, hwf.isAnc_trans, hwf.isAnc_antisymm,
   hwf.isAnc_present_left, hwf.isAnc_present_right, hwf.anc_linear⟩

/-! ## 5. Local Read/Write Preservation & Sub-Range Narrowing of `HasUniqueWritePerm` -/

theorem hasUniqueWritePerm_narrow
    {tree : BorrowTree} {tag : BorTag} {r1 r2 : ByteRange} {active : ActiveProtectors}
    (hPerm : HasUniqueWritePerm tree tag r2 active)
    (hSub : SubRange r1 r2) :
    HasUniqueWritePerm tree tag r1 active where
  wf := hPerm.wf
  tag_present := hPerm.tag_present
  ancestors_writable := fun anc b hAnc hb =>
    hPerm.ancestors_writable anc b hAnc (hSub b hb)
  non_ancestors_safe := fun other b hPres hNotAnc hb =>
    hPerm.non_ancestors_safe other b hPres hNotAnc (hSub b hb)

/-- Any local access (`read` or `write`) through `tag` on `subRange ⊆ range` when
`HasUniqueWritePerm tree tag range active` holds is UB-free and preserves
`HasUniqueWritePerm` on the full `range`. -/
theorem local_access_preserves_hasUniqueWritePerm
    {tree : BorrowTree} {tag : BorTag} {range subRange : ByteRange}
    {active : ActiveProtectors} (kind : AccessKind)
    (hPerm : HasUniqueWritePerm tree tag range active)
    (hSub : SubRange subRange range) :
    TreeAccessNoUB tree tag kind subRange active .visitChildrenOfAccessed ∧
      HasUniqueWritePerm
        (applyTreeAccess tree tag kind subRange active .visitChildrenOfAccessed)
        tag range active := by
  constructor
  · intro n b hPres hbSub
    have hbRange := hSub b hbSub
    unfold nodeAccessRelatedness
    cases hAnc : tree.isAnc n tag with
    | true =>
      simp only [↓reduceIte]
      obtain ⟨st', hEq, _⟩ :=
        performTransition_local_of_ancestorWritable kind (tree.isTagProtected n active)
          (tree.locState n b) (hPerm.ancestors_writable n b hAnc hbRange)
      simp [hEq]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨st', hEq, _⟩ :=
        performTransition_foreign_of_nonAncestorSafe kind (tree.isTagProtected n active)
          (tree.locState n b) (hPerm.non_ancestors_safe n b hPres hAnc hbRange)
      simp [hEq]
  · refine ⟨applyTreeAccess_wf tree tag kind subRange active .visitChildrenOfAccessed hPerm.wf,
      hPerm.tag_present, ?_, ?_⟩
    · intro anc b hAnc hbRange
      have hAncOrig : tree.isAnc anc tag = true := hAnc
      have hPresAnc : tree.present anc = true := hPerm.wf.isAnc_present_left anc tag hAncOrig
      cases hbSub : subRange b with
      | true =>
        rw [applyTreeAccess_locState_in tree tag kind subRange active .visitChildrenOfAccessed
          anc b hPresAnc hbSub]
        simp only [nodeAccessRelatedness, hAncOrig, ↓reduceIte]
        obtain ⟨st', hEq, hAw, _⟩ :=
          performTransition_local_of_ancestorWritable kind (tree.isTagProtected anc active)
            (tree.locState anc b) (hPerm.ancestors_writable anc b hAncOrig hbRange)
        rw [hEq]
        exact hAw
      | false =>
        rw [applyTreeAccess_locState_out tree tag kind subRange active .visitChildrenOfAccessed
          anc b hbSub]
        exact hPerm.ancestors_writable anc b hAncOrig hbRange
    · intro other b hPres hNotAnc hbRange
      have hPresOrig : tree.present other = true := hPres
      have hNotAncOrig : tree.isAnc other tag = false := hNotAnc
      rw [applyTreeAccess_isTagProtected]
      cases hbSub : subRange b with
      | true =>
        rw [applyTreeAccess_locState_in tree tag kind subRange active .visitChildrenOfAccessed
          other b hPresOrig hbSub]
        simp only [nodeAccessRelatedness, hNotAncOrig, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨st', hEq, hSafe, _⟩ :=
          performTransition_foreign_of_nonAncestorSafe kind (tree.isTagProtected other active)
            (tree.locState other b) (hPerm.non_ancestors_safe other b hPresOrig hNotAncOrig hbRange)
        rw [hEq]
        exact hSafe
      | false =>
        rw [applyTreeAccess_locState_out tree tag kind subRange active .visitChildrenOfAccessed
          other b hbSub]
        exact hPerm.non_ancestors_safe other b hPresOrig hNotAncOrig hbRange

/-- After a local `write` through `tag` on `subRange ⊆ range`, `tag` and every
ancestor `anc` of `tag` (including any outer `FnEntry`-protected ancestor
`t_outer`) is in state `⟨.active, true⟩` on `subRange`. -/
theorem local_write_activates_ancestors
    {tree : BorrowTree} {tag anc : BorTag} {range subRange : ByteRange}
    {active : ActiveProtectors} {b : ByteOffset}
    (hPerm : HasUniqueWritePerm tree tag range active)
    (hSub : SubRange subRange range)
    (hAnc : tree.isAnc anc tag = true)
    (hb : subRange b = true) :
    (applyTreeAccess tree tag .write subRange active .visitChildrenOfAccessed).locState anc b =
      ⟨.active, true⟩ := by
  have hPresAnc : tree.present anc = true := hPerm.wf.isAnc_present_left anc tag hAnc
  have hbRange := hSub b hb
  rw [applyTreeAccess_locState_in tree tag .write subRange active .visitChildrenOfAccessed
    anc b hPresAnc hb]
  simp only [nodeAccessRelatedness, hAnc, ↓reduceIte]
  obtain ⟨hEq, _⟩ :=
    performTransition_local_write_of_ancestorWritable (tree.isTagProtected anc active)
      (tree.locState anc b) (hPerm.ancestors_writable anc b hAnc hbRange)
  rw [hEq]

/-! ## 6. Retagging Child References (`FnEntry` and `Default` Sub-Range Reborrows) -/

/-- Retagging a fresh child `t_child` under `t_parent` on
`childRange ⊆ parentRange` with initial permission `.reserved tyIsFreeze false`
succeeds without UB and establishes `HasUniqueWritePerm` for `t_child` on
`childRange`. -/
theorem retagChild_hasUniqueWritePerm
    {tree : BorrowTree} {t_parent t_child : BorTag}
    {parentRange childRange : ByteRange} {active : ActiveProtectors}
    (prot : Option ProtectorKind) (tyIsFreeze : Bool)
    (hPerm : HasUniqueWritePerm tree t_parent parentRange active)
    (hSub : SubRange childRange parentRange)
    (hFresh : tree.present t_child = false) :
    let tree1 := insertChildNode tree t_parent t_child prot (.reserved tyIsFreeze false)
    TreeAccessNoUB tree1 t_child .read childRange active .visitChildrenOfAccessed ∧
      HasUniqueWritePerm
        (retagChild tree t_parent t_child prot (.reserved tyIsFreeze false) childRange active)
        t_child childRange active := by
  intro tree1
  have hwf1 : TreeWF tree1 :=
    insertChildNode_wf tree t_parent t_child prot (.reserved tyIsFreeze false)
      hPerm.wf hFresh
  have hPrePerm : HasUniqueWritePerm tree1 t_child childRange active := by
    refine ⟨hwf1, by simp [tree1, insertChildNode], ?_, ?_⟩
    · intro anc b hAnc hbChild
      by_cases hac : anc = t_child
      · rw [hac]
        simp [tree1, insertChildNode, AncestorWritable]
      · have hAncOrig : tree.isAnc anc t_parent = true := by
          simpa [tree1, insertChildNode, hac] using hAnc
        simp [tree1, insertChildNode, hac]
        exact hPerm.ancestors_writable anc b hAncOrig (hSub b hbChild)
    · intro other b hPres hNotAnc hbChild
      have hOtherNe : other ≠ t_child := by
        intro hEq
        rw [hEq] at hNotAnc
        simp [tree1, insertChildNode] at hNotAnc
      have hPresOrig : tree.present other = true := by
        simpa [tree1, insertChildNode, hOtherNe] using hPres
      have hNotAncOrig : tree.isAnc other t_parent = false := by
        simpa [tree1, insertChildNode, hOtherNe] using hNotAnc
      have hProtEq : tree1.isTagProtected other active = tree.isTagProtected other active := by
        simp [tree1, insertChildNode, BorrowTree.isTagProtected, hOtherNe]
      rw [hProtEq]
      simp [tree1, insertChildNode, hOtherNe]
      exact hPerm.non_ancestors_safe other b hPresOrig hNotAncOrig (hSub b hbChild)
  exact local_access_preserves_hasUniqueWritePerm .read hPrePerm (fun _ h => h)

/-- When a callee retags an unprotected child `t_child` (`prot = none`) under
`t_parent` on `childRange ⊆ parentRange`, `HasUniqueWritePerm` on `t_parent`
over the full `parentRange` is also preserved. -/
theorem retagUnprotectedChild_preserves_parent_hasUniqueWritePerm
    {tree : BorrowTree} {t_parent t_child : BorTag}
    {parentRange childRange : ByteRange} {active : ActiveProtectors}
    (tyIsFreeze : Bool)
    (hPerm : HasUniqueWritePerm tree t_parent parentRange active)
    (hFresh : tree.present t_child = false) :
    HasUniqueWritePerm
      (retagChild tree t_parent t_child none (.reserved tyIsFreeze false) childRange active)
      t_parent parentRange active := by
  have hNeParent : ∀ x, tree.present x = true → x ≠ t_child := by
    intro x hx hEq; rw [hEq] at hx; rw [hFresh] at hx; contradiction
  have hParentNeChild : t_parent ≠ t_child := hNeParent t_parent hPerm.tag_present
  let tree1 := insertChildNode tree t_parent t_child none (.reserved tyIsFreeze false)
  have hwf1 : TreeWF tree1 :=
    insertChildNode_wf tree t_parent t_child none (.reserved tyIsFreeze false)
      hPerm.wf hFresh
  refine ⟨applyTreeAccess_wf tree1 t_child .read childRange active .visitChildrenOfAccessed hwf1,
    by simp [retagChild, insertChildNode, hPerm.tag_present], ?_, ?_⟩
  · intro anc b hAnc hbParent
    have hAncNeChild : anc ≠ t_child := by
      intro hEq; rw [hEq] at hAnc
      simp [retagChild, insertChildNode, hParentNeChild] at hAnc
    have hAncOrig : tree.isAnc anc t_parent = true := by
      simpa [retagChild, insertChildNode, hParentNeChild, hAncNeChild] using hAnc
    have hPresAnc : tree.present anc = true := hPerm.wf.isAnc_present_left anc t_parent hAncOrig
    have hPres1 : tree1.present anc = true := by
      simp [tree1, insertChildNode, hPresAnc]
    have hAncChild1 : tree1.isAnc anc t_child = true := by
      simp [tree1, insertChildNode, hAncOrig]
    have hLoc1 : tree1.locState anc b = tree.locState anc b := by
      simp [tree1, insertChildNode, hAncNeChild]
    have hProt1 : tree1.isTagProtected anc active = tree.isTagProtected anc active := by
      simp [tree1, insertChildNode, BorrowTree.isTagProtected, hAncNeChild]
    change AncestorWritable ((applyTreeAccess tree1 t_child .read childRange active .visitChildrenOfAccessed).locState anc b)
    cases hbChild : childRange b with
    | true =>
      rw [applyTreeAccess_locState_in tree1 t_child .read childRange active .visitChildrenOfAccessed
        anc b hPres1 hbChild]
      simp only [nodeAccessRelatedness, hAncChild1, ↓reduceIte, hLoc1, hProt1]
      obtain ⟨st', hEq, hAw, _⟩ :=
        performTransition_local_of_ancestorWritable .read (tree.isTagProtected anc active)
          (tree.locState anc b) (hPerm.ancestors_writable anc b hAncOrig hbParent)
      rw [hEq]
      exact hAw
    | false =>
      rw [applyTreeAccess_locState_out tree1 t_child .read childRange active .visitChildrenOfAccessed
        anc b hbChild, hLoc1]
      exact hPerm.ancestors_writable anc b hAncOrig hbParent
  · intro other b hPres hNotAnc hbParent
    by_cases hOtherChild : other = t_child
    · rw [hOtherChild]
      left
      simp [retagChild, insertChildNode, BorrowTree.isTagProtected]
    · have hPresOrig : tree.present other = true := by
        simpa [retagChild, insertChildNode, hOtherChild] using hPres
      have hNotAncOrig : tree.isAnc other t_parent = false := by
        simpa [retagChild, insertChildNode, hParentNeChild, hOtherChild] using hNotAnc
      have hPres1 : tree1.present other = true := by
        simp [tree1, insertChildNode, hPresOrig]
      have hNotAncChild1 : tree1.isAnc other t_child = false := by
        simp [tree1, insertChildNode, hOtherChild, hNotAncOrig]
      have hLoc1 : tree1.locState other b = tree.locState other b := by
        simp [tree1, insertChildNode, hOtherChild]
      have hProt1 : tree1.isTagProtected other active = tree.isTagProtected other active := by
        simp [tree1, insertChildNode, BorrowTree.isTagProtected, hOtherChild]
      change NonAncestorSafe
        ((applyTreeAccess tree1 t_child .read childRange active .visitChildrenOfAccessed).locState other b)
        ((applyTreeAccess tree1 t_child .read childRange active .visitChildrenOfAccessed).isTagProtected other active)
      rw [applyTreeAccess_isTagProtected, hProt1]
      cases hbChild : childRange b with
      | true =>
        rw [applyTreeAccess_locState_in tree1 t_child .read childRange active .visitChildrenOfAccessed
          other b hPres1 hbChild]
        simp only [nodeAccessRelatedness, hNotAncChild1, Bool.false_eq_true, ↓reduceIte, hLoc1, hProt1]
        obtain ⟨st', hEq, hSafe, _⟩ :=
          performTransition_foreign_of_nonAncestorSafe .read (tree.isTagProtected other active)
            (tree.locState other b) (hPerm.non_ancestors_safe other b hPresOrig hNotAncOrig hbParent)
        rw [hEq]
        exact hSafe
      | false =>
        rw [applyTreeAccess_locState_out tree1 t_child .read childRange active .visitChildrenOfAccessed
          other b hbChild, hLoc1]
        exact hPerm.non_ancestors_safe other b hPresOrig hNotAncOrig hbParent

theorem retagChild_outside_range_locState
    (tree : BorrowTree) (t_parent t_child : BorTag)
    (prot : Option ProtectorKind) (tyIsFreeze : Bool)
    (childRange : ByteRange) (active : ActiveProtectors)
    (n : BorTag) (b : ByteOffset) (hbOut : childRange b = false) :
    (retagChild tree t_parent t_child prot (.reserved tyIsFreeze false) childRange active).locState n b =
      if n == t_child then ⟨.reserved tyIsFreeze false, false⟩ else tree.locState n b := by
  simp [retagChild, applyTreeAccess, hbOut, insertChildNode]

theorem retagChild_child_accessed_iff
    {tree : BorrowTree} {t_parent t_child : BorTag}
    {prot : Option ProtectorKind} {tyIsFreeze : Bool}
    {childRange : ByteRange} {active : ActiveProtectors}
    (b : ByteOffset) :
    ((retagChild tree t_parent t_child prot (.reserved tyIsFreeze false) childRange active).locState
      t_child b).accessed = childRange b := by
  cases hb : childRange b with
  | true =>
    simp [retagChild, applyTreeAccess, insertChildNode, hb,
      nodeAccessRelatedness, performTransition]
  | false =>
    simp [retagChild, applyTreeAccess, insertChildNode, hb]

/-! ## 7. Single Returned Reborrow Under Two-Stage Protector Release (`reborrow_return_unique_write_perm`) -/

/-- State invariant during a function call with `FnEntry`-protected argument
`t_arg` on `parentRange` and callee-reborrowed descendant `t_ret` under `t_arg`
on `subRange ⊆ parentRange`. -/
structure CalleeReborrowState
    (tree : BorrowTree)
    (t_arg t_ret : BorTag)
    (parentRange subRange : ByteRange)
    (activeCaller : ActiveProtectors)
    (callId : CallId) : Prop where
  sub_range : SubRange subRange parentRange
  arg_perm : HasUniqueWritePerm tree t_arg parentRange (insertActiveProtector activeCaller callId)
  ret_present : tree.present t_ret = true
  arg_anc_ret : tree.isAnc t_arg t_ret = true
  ret_ne_arg : t_ret ≠ t_arg
  arg_accessed_in_parent : ∀ b, (tree.locState t_arg b).accessed = true → parentRange b = true
  ret_ancestors_writable :
    ∀ anc b, tree.isAnc anc t_ret = true → subRange b = true →
      AncestorWritable (tree.locState anc b)
  descendants_unprotected_in_caller :
    ∀ d, tree.isAnc t_arg d = true → d ≠ t_arg →
      tree.isTagProtected d activeCaller = false

/-- General two-stage `releaseProtector` preservation theorem
(`SkipChildrenOfAccessed` while `callId` is active, followed by removing
`callId` from `activeProtectors`). -/
theorem releaseProtector_preserves_reborrow_child
    {tree : BorrowTree} {t_arg t_ret : BorTag}
    {parentRange subRange : ByteRange} {activeCaller : ActiveProtectors} {callId : CallId}
    (hState : CalleeReborrowState tree t_arg t_ret parentRange subRange activeCaller callId) :
    let active1 := insertActiveProtector activeCaller callId
    let tree_post := applyReleaseProtector tree t_arg active1
    releaseProtectorNoUB tree t_arg active1 ∧
      (∀ b, tree_post.locState t_ret b = tree.locState t_ret b) ∧
      HasUniqueWritePerm tree_post t_ret subRange activeCaller := by
  intro active1 tree_post
  have hwf := hState.arg_perm.wf
  have hRetNotAncArg : tree.isAnc t_ret t_arg = false := by
    cases h : tree.isAnc t_ret t_arg with
    | false => rfl
    | true =>
      exact False.elim (hState.ret_ne_arg (hwf.isAnc_antisymm t_ret t_arg h hState.arg_anc_ret))
  refine ⟨?_, ?_, ?_⟩
  · -- 1. `releaseProtectorNoUB tree t_arg active1`
    intro n b hPres hAcc kind hAssoc
    have hbParent : parentRange b = true := hState.arg_accessed_in_parent b hAcc
    unfold nodeAccessRelatedness
    cases hAnc : tree.isAnc n t_arg with
    | true =>
      simp only [↓reduceIte]
      obtain ⟨st', hEq, _⟩ :=
        performTransition_local_of_ancestorWritable kind (tree.isTagProtected n active1)
          (tree.locState n b) (hState.arg_perm.ancestors_writable n b hAnc hbParent)
      simp [hEq]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hDesc : tree.isAnc t_arg n with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨st', hEq, _⟩ :=
          performTransition_foreign_of_nonAncestorSafe kind (tree.isTagProtected n active1)
            (tree.locState n b) (hState.arg_perm.non_ancestors_safe n b hPres hAnc hbParent)
        simp [hEq]
  · -- 2. `t_ret` is untouched by `applyReleaseProtector` because `SkipChildrenOfAccessed` skips it
    intro b
    cases hAcc : (tree.locState t_arg b).accessed with
    | false =>
      exact applyReleaseProtector_locState_unacc tree t_arg active1 t_ret b hAcc
    | true =>
      rw [applyReleaseProtector_locState_acc tree t_arg active1 t_ret b hState.ret_present hAcc]
      simp only [nodeAccessRelatedness, hRetNotAncArg, hState.arg_anc_ret, Bool.false_eq_true, ↓reduceIte]
      cases (tree.locState t_arg b).perm.associatedAccess <;> rfl
  · -- 3. `HasUniqueWritePerm tree_post t_ret subRange activeCaller`
    refine ⟨applyReleaseProtector_wf tree t_arg active1 hwf, hState.ret_present, ?_, ?_⟩
    · intro anc b hAncRet hbSub
      have hPresAnc : tree.present anc = true := hwf.isAnc_present_left anc t_ret hAncRet
      have hbParent : parentRange b = true := hState.sub_range b hbSub
      cases hAcc : (tree.locState t_arg b).accessed with
      | true =>
        rw [applyReleaseProtector_locState_acc tree t_arg active1 anc b hPresAnc hAcc]
        obtain ⟨kind, hKind⟩ :=
          associatedAccess_of_ancestorWritable (tree.locState t_arg b)
            (hState.arg_perm.ancestors_writable t_arg b
              (hwf.isAnc_refl t_arg hState.arg_perm.tag_present) hbParent)
        simp only [hKind, nodeAccessRelatedness]
        cases hAncArg : tree.isAnc anc t_arg with
        | true =>
          simp only [↓reduceIte]
          obtain ⟨st', hEq, hAw, _⟩ :=
            performTransition_local_of_ancestorWritable kind (tree.isTagProtected anc active1)
              (tree.locState anc b) (hState.arg_perm.ancestors_writable anc b hAncArg hbParent)
          rw [hEq]
          exact hAw
        | false =>
          have hDescArg : tree.isAnc t_arg anc = true := by
            rcases hwf.anc_linear anc t_arg t_ret hAncRet hState.arg_anc_ret with h1 | h2
            · rw [hAncArg] at h1; contradiction
            · exact h2
          simp only [Bool.false_eq_true, ↓reduceIte, hDescArg]
          exact hState.ret_ancestors_writable anc b hAncRet hbSub
      | false =>
        rw [applyReleaseProtector_locState_unacc tree t_arg active1 anc b hAcc]
        exact hState.ret_ancestors_writable anc b hAncRet hbSub
    · intro other b hPres hNotAncRet hbSub
      have hPresOrig : tree.present other = true := hPres
      have hNotAncRetOrig : tree.isAnc other t_ret = false := hNotAncRet
      have hbParent : parentRange b = true := hState.sub_range b hbSub
      rw [applyReleaseProtector_isTagProtected]
      cases hDescArg : tree.isAnc t_arg other with
      | true =>
        have hOtherNeArg : other ≠ t_arg := by
          intro hEq
          rw [hEq] at hNotAncRetOrig
          rw [hState.arg_anc_ret] at hNotAncRetOrig
          contradiction
        left
        exact hState.descendants_unprotected_in_caller other hDescArg hOtherNeArg
      | false =>
        have hNotAncArg : tree.isAnc other t_arg = false := by
          cases h : tree.isAnc other t_arg with
          | false => rfl
          | true =>
            have hAncRet := hwf.isAnc_trans other t_arg t_ret h hState.arg_anc_ret
            rw [hNotAncRetOrig] at hAncRet; contradiction
        have hSafePre := hState.arg_perm.non_ancestors_safe other b hPresOrig hNotAncArg hbParent
        have hImp : tree.isTagProtected other activeCaller = true →
            tree.isTagProtected other active1 = true := by
          intro hProtCaller
          simp only [BorrowTree.isTagProtected] at hProtCaller ⊢
          cases hProt : tree.protector other with
          | none => simp [hProt] at hProtCaller
          | some p =>
            simp [hProt] at hProtCaller ⊢
            simp [active1, insertActiveProtector, hProtCaller]
        cases hAcc : (tree.locState t_arg b).accessed with
        | true =>
          rw [applyReleaseProtector_locState_acc tree t_arg active1 other b hPresOrig hAcc]
          obtain ⟨kind, hKind⟩ :=
            associatedAccess_of_ancestorWritable (tree.locState t_arg b)
              (hState.arg_perm.ancestors_writable t_arg b
                (hwf.isAnc_refl t_arg hState.arg_perm.tag_present) hbParent)
          simp only [hKind, nodeAccessRelatedness, hNotAncArg, hDescArg, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨st', hEq, hSafePost, _⟩ :=
            performTransition_foreign_of_nonAncestorSafe kind (tree.isTagProtected other active1)
              (tree.locState other b) hSafePre
          rw [hEq]
          exact nonAncestorSafe_mono_unprotect st'
            (tree.isTagProtected other active1)
            (tree.isTagProtected other activeCaller) hSafePost hImp
        | false =>
          rw [applyReleaseProtector_locState_unacc tree t_arg active1 other b hAcc]
          exact nonAncestorSafe_mono_unprotect (tree.locState other b)
            (tree.isTagProtected other active1)
            (tree.isTagProtected other activeCaller) hSafePre hImp

/-- **End-to-End Theorem `reborrow_return_unique_write_perm`**:
Suppose `HasUniqueWritePerm tree0 t_parent parentRange activeCaller` holds
before calling `get_mut(x: &mut Pair) -> &mut u32` (even when `t_parent` or an
outer ancestor `t_outer` is `Strong`-protected in `activeCaller`).
1. `enterCallBoundary` creates `FnEntry`-protected child `t_arg` under
   `t_parent` on `parentRange` with fresh protector `callId`.
2. The callee creates unprotected child `t_ret` under `t_arg` on
   `subRange ⊆ parentRange` without writing during the call, so `t_arg` stays
   `Reserved` and emits implicit `Read` on protector release.
3. `releaseProtector` releases `t_arg`'s protector (`SkipChildrenOfAccessed` +
   removing `callId`).
Then:
- Every step is UB-free,
- `HasUniqueWritePerm tree_post t_ret subRange activeCaller` holds in the
  caller, and
- When the caller subsequently writes through `t_ret` on `subRange`, the write
  is UB-free and activates `t_ret`, `t_arg`, `t_parent`, and any outer
  protected ancestor `t_outer` to `⟨.active, true⟩` on `subRange`. -/
theorem reborrow_return_unique_write_perm
    {tree0 : BorrowTree} {t_parent t_arg t_ret : BorTag}
    {parentRange subRange : ByteRange} {activeCaller : ActiveProtectors} {callId : CallId}
    (tyIsFreeze : Bool)
    (hPerm0 : HasUniqueWritePerm tree0 t_parent parentRange activeCaller)
    (hSub : SubRange subRange parentRange)
    (hFreshArg : tree0.present t_arg = false)
    (hFreshRet : tree0.present t_ret = false)
    (hRetNeArg : t_ret ≠ t_arg)
    (hFreshCallId : ∀ n, tree0.present n = true →
      ∀ p, tree0.protector n = some p → p.callId ≠ callId) :
    let active1 := insertActiveProtector activeCaller callId
    let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reserved tyIsFreeze false) parentRange active1
    let tree2 := retagChild tree1 t_arg t_ret none (.reserved tyIsFreeze false) subRange active1
    let tree_post := applyReleaseProtector tree2 t_arg active1
    releaseProtectorNoUB tree2 t_arg active1 ∧
      HasUniqueWritePerm tree_post t_ret subRange activeCaller ∧
      TreeAccessNoUB tree_post t_ret .write subRange activeCaller .visitChildrenOfAccessed ∧
      HasUniqueWritePerm
        (applyTreeAccess tree_post t_ret .write subRange activeCaller .visitChildrenOfAccessed)
        t_ret subRange activeCaller := by
  intro active1 tree1 tree2 tree_post
  have hPerm0_active1 : HasUniqueWritePerm tree0 t_parent parentRange active1 := by
    refine ⟨hPerm0.wf, hPerm0.tag_present, hPerm0.ancestors_writable, ?_⟩
    intro other b hPres hNotAnc hb
    have hProtEq : tree0.isTagProtected other active1 = tree0.isTagProtected other activeCaller := by
      simp only [BorrowTree.isTagProtected]
      cases hP : tree0.protector other with
      | none => rfl
      | some p =>
        have hNe := hFreshCallId other hPres p hP
        simp [active1, insertActiveProtector, hNe]
    rw [hProtEq]
    exact hPerm0.non_ancestors_safe other b hPres hNotAnc hb
  have hTree1Perm : HasUniqueWritePerm tree1 t_arg parentRange active1 :=
    (retagChild_hasUniqueWritePerm (some (.strong callId)) tyIsFreeze hPerm0_active1 (fun _ h => h) hFreshArg).2
  have hFreshRet1 : tree1.present t_ret = false := by
    simp [tree1, retagChild, insertChildNode, hRetNeArg, hFreshRet]
  have hTree2ArgPerm : HasUniqueWritePerm tree2 t_arg parentRange active1 :=
    retagUnprotectedChild_preserves_parent_hasUniqueWritePerm tyIsFreeze hTree1Perm hFreshRet1
  have hTree2RetPerm : HasUniqueWritePerm tree2 t_ret subRange active1 :=
    (retagChild_hasUniqueWritePerm none tyIsFreeze hTree1Perm hSub hFreshRet1).2
  have hCalleeState : CalleeReborrowState tree2 t_arg t_ret parentRange subRange activeCaller callId := by
    refine ⟨hSub, hTree2ArgPerm, hTree2RetPerm.tag_present, ?_, hRetNeArg, ?_, hTree2RetPerm.ancestors_writable, ?_⟩
    · simp [tree2, retagChild, insertChildNode, hTree1Perm.wf.isAnc_refl t_arg hTree1Perm.tag_present]
    · intro b hAcc
      cases hbParent : parentRange b with
      | true => rfl
      | false =>
        have hbSubOut : subRange b = false := by
          cases hbSub : subRange b with
          | false => rfl
          | true =>
            have hT := hSub b hbSub
            rw [hbParent] at hT; contradiction
        have hLoc2 : (tree2.locState t_arg b).accessed = (tree1.locState t_arg b).accessed := by
          simp [tree2, retagChild_outside_range_locState, hbSubOut, Ne.symm hRetNeArg]
        have hLoc1 : (tree1.locState t_arg b).accessed = parentRange b :=
          retagChild_child_accessed_iff b
        rw [hLoc2, hLoc1, hbParent] at hAcc
        contradiction
    · intro d hDesc hdNeArg
      by_cases hdRet : d = t_ret
      · rw [hdRet]
        simp [tree2, retagChild, insertChildNode, BorrowTree.isTagProtected]
      · have hDesc1 : tree1.isAnc t_arg d = true := by
          simpa [tree2, retagChild, insertChildNode, hdRet, Ne.symm hRetNeArg] using hDesc
        have hFalse : tree1.isAnc t_arg d = false := by
          simp [tree1, retagChild, insertChildNode, hdNeArg]
        rw [hFalse] at hDesc1
        contradiction
  obtain ⟨hRelNoUB, _, hPostPerm⟩ := releaseProtector_preserves_reborrow_child hCalleeState
  obtain ⟨hWriteNoUB, hAfterWritePerm⟩ :=
    local_access_preserves_hasUniqueWritePerm .write hPostPerm (fun _ h => h)
  exact ⟨hRelNoUB, hPostPerm, hWriteNoUB, hAfterWritePerm⟩

/-- **Activated Variant (`reborrow_return_after_callee_write_unique_write_perm`)**:
If the callee also writes through `t_ret` on `subRange` during the call—so
`t_arg` is `.active` (`Unique`) on `subRange` and `.reserved` on
`parentRange \ subRange`, emitting an implicit `Write` on `subRange` and
implicit `Read` on `parentRange \ subRange` during `releaseProtector`—
`releaseProtector` still succeeds without UB and establishes
`HasUniqueWritePerm tree_post t_ret subRange activeCaller`. -/
theorem reborrow_return_after_callee_write_unique_write_perm
    {tree0 : BorrowTree} {t_parent t_arg t_ret : BorTag}
    {parentRange subRange : ByteRange} {activeCaller : ActiveProtectors} {callId : CallId}
    (tyIsFreeze : Bool)
    (hPerm0 : HasUniqueWritePerm tree0 t_parent parentRange activeCaller)
    (hSub : SubRange subRange parentRange)
    (hFreshArg : tree0.present t_arg = false)
    (hFreshRet : tree0.present t_ret = false)
    (hRetNeArg : t_ret ≠ t_arg)
    (hFreshCallId : ∀ n, tree0.present n = true →
      ∀ p, tree0.protector n = some p → p.callId ≠ callId) :
    let active1 := insertActiveProtector activeCaller callId
    let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reserved tyIsFreeze false) parentRange active1
    let tree2 := retagChild tree1 t_arg t_ret none (.reserved tyIsFreeze false) subRange active1
    let tree3 := applyTreeAccess tree2 t_ret .write subRange active1 .visitChildrenOfAccessed
    let tree_post := applyReleaseProtector tree3 t_arg active1
    releaseProtectorNoUB tree3 t_arg active1 ∧
      HasUniqueWritePerm tree_post t_ret subRange activeCaller := by
  intro active1 tree1 tree2 tree3 tree_post
  have hPerm0_active1 : HasUniqueWritePerm tree0 t_parent parentRange active1 := by
    refine ⟨hPerm0.wf, hPerm0.tag_present, hPerm0.ancestors_writable, ?_⟩
    intro other b hPres hNotAnc hb
    have hProtEq : tree0.isTagProtected other active1 = tree0.isTagProtected other activeCaller := by
      simp only [BorrowTree.isTagProtected]
      cases hP : tree0.protector other with
      | none => rfl
      | some p =>
        have hNe := hFreshCallId other hPres p hP
        simp [active1, insertActiveProtector, hNe]
    rw [hProtEq]
    exact hPerm0.non_ancestors_safe other b hPres hNotAnc hb
  have hTree1Perm : HasUniqueWritePerm tree1 t_arg parentRange active1 :=
    (retagChild_hasUniqueWritePerm (some (.strong callId)) tyIsFreeze hPerm0_active1 (fun _ h => h) hFreshArg).2
  have hFreshRet1 : tree1.present t_ret = false := by
    simp [tree1, retagChild, insertChildNode, hRetNeArg, hFreshRet]
  have hTree2ArgPerm : HasUniqueWritePerm tree2 t_arg parentRange active1 :=
    retagUnprotectedChild_preserves_parent_hasUniqueWritePerm tyIsFreeze hTree1Perm hFreshRet1
  have hTree2RetPerm : HasUniqueWritePerm tree2 t_ret subRange active1 :=
    (retagChild_hasUniqueWritePerm none tyIsFreeze hTree1Perm hSub hFreshRet1).2
  have hTree3RetPerm : HasUniqueWritePerm tree3 t_ret subRange active1 :=
    (local_access_preserves_hasUniqueWritePerm .write hTree2RetPerm (fun _ h => h)).2
  have hTree3ArgPerm : HasUniqueWritePerm tree3 t_arg parentRange active1 := by
    refine ⟨applyTreeAccess_wf tree2 t_ret .write subRange active1 .visitChildrenOfAccessed hTree2ArgPerm.wf,
      hTree2ArgPerm.tag_present, ?_, ?_⟩
    · intro anc b hAncArg hbParent
      have hAncArg2 : tree2.isAnc anc t_arg = true := hAncArg
      have hAncRet : tree2.isAnc anc t_ret = true := by
        have hArgAncRet : tree2.isAnc t_arg t_ret = true := by
          simp [tree2, retagChild, insertChildNode,
            hTree1Perm.wf.isAnc_refl t_arg hTree1Perm.tag_present]
        exact hTree2ArgPerm.wf.isAnc_trans anc t_arg t_ret hAncArg2 hArgAncRet
      cases hbSub : subRange b with
      | true => exact hTree3RetPerm.ancestors_writable anc b hAncRet hbSub
      | false =>
        rw [applyTreeAccess_locState_out tree2 t_ret .write subRange active1 .visitChildrenOfAccessed
          anc b hbSub]
        exact hTree2ArgPerm.ancestors_writable anc b hAncArg2 hbParent
    · intro other b hPres hNotAncArg hbParent
      have hPres2 : tree2.present other = true := hPres
      have hNotAncArg2 : tree2.isAnc other t_arg = false := hNotAncArg
      by_cases hOtherRet : other = t_ret
      · rw [hOtherRet]
        left
        simp [tree3, tree2, retagChild, insertChildNode, BorrowTree.isTagProtected]
      · have hNotAncRet : tree2.isAnc other t_ret = false := by
          simpa [tree2, retagChild, insertChildNode, hOtherRet] using hNotAncArg2
        cases hbSub : subRange b with
        | true => exact hTree3RetPerm.non_ancestors_safe other b hPres2 hNotAncRet hbSub
        | false =>
          rw [applyTreeAccess_locState_out tree2 t_ret .write subRange active1 .visitChildrenOfAccessed
            other b hbSub, applyTreeAccess_isTagProtected]
          exact hTree2ArgPerm.non_ancestors_safe other b hPres2 hNotAncArg2 hbParent
  have hCalleeState : CalleeReborrowState tree3 t_arg t_ret parentRange subRange activeCaller callId := by
    refine ⟨hSub, hTree3ArgPerm, hTree3RetPerm.tag_present, ?_, hRetNeArg, ?_, hTree3RetPerm.ancestors_writable, ?_⟩
    · simp [tree3, tree2, retagChild, insertChildNode,
        hTree1Perm.wf.isAnc_refl t_arg hTree1Perm.tag_present]
    · intro b hAcc
      cases hbParent : parentRange b with
      | true => rfl
      | false =>
        have hbSubOut : subRange b = false := by
          cases hbSub : subRange b with
          | false => rfl
          | true =>
            have hT := hSub b hbSub
            rw [hbParent] at hT; contradiction
        have hLoc3 : (tree3.locState t_arg b).accessed = (tree2.locState t_arg b).accessed := by
          rw [applyTreeAccess_locState_out tree2 t_ret .write subRange active1 .visitChildrenOfAccessed
            t_arg b hbSubOut]
        have hLoc2 : (tree2.locState t_arg b).accessed = (tree1.locState t_arg b).accessed := by
          simp [tree2, retagChild_outside_range_locState, hbSubOut, Ne.symm hRetNeArg]
        have hLoc1 : (tree1.locState t_arg b).accessed = parentRange b :=
          retagChild_child_accessed_iff b
        rw [hLoc3, hLoc2, hLoc1, hbParent] at hAcc
        contradiction
    · intro d hDesc hdNeArg
      by_cases hdRet : d = t_ret
      · rw [hdRet]
        simp [tree3, tree2, retagChild, insertChildNode, BorrowTree.isTagProtected]
      · have hDesc1 : tree1.isAnc t_arg d = true := by
          simpa [tree3, tree2, retagChild, insertChildNode, hdRet, Ne.symm hRetNeArg] using hDesc
        have hFalse : tree1.isAnc t_arg d = false := by
          simp [tree1, retagChild, insertChildNode, hdNeArg]
        rw [hFalse] at hDesc1
        contradiction
  obtain ⟨hRelNoUB, _, hPostPerm⟩ := releaseProtector_preserves_reborrow_child hCalleeState
  exact ⟨hRelNoUB, hPostPerm⟩

/-! ## 8. Disjoint Sibling Reborrows (`split_at_mut_unique_write_perm`) & Frame Preservation -/

/-- Framing lemma: any memory access (`read` or `write`) at `t_left` over
`leftRange` preserves `HasUniqueWritePerm` for any tag `t_right` over a
disjoint `rightRange`. -/
theorem disjoint_access_preserves_hasUniqueWritePerm
    {tree : BorrowTree} {t_right : BorTag}
    {leftRange rightRange : ByteRange} {active : ActiveProtectors}
    (t_left : BorTag) (kind : AccessKind) (mode : ChildrenVisitMode)
    (hRightPerm : HasUniqueWritePerm tree t_right rightRange active)
    (hDisj : DisjointRange leftRange rightRange) :
    HasUniqueWritePerm
      (applyTreeAccess tree t_left kind leftRange active mode)
      t_right rightRange active := by
  have hDisjRL := disjointRange_symm hDisj
  refine ⟨applyTreeAccess_wf tree t_left kind leftRange active mode hRightPerm.wf,
    hRightPerm.tag_present, ?_, ?_⟩
  · intro anc b hAnc hbRight
    have hbLeftF : leftRange b = false := hDisjRL b hbRight
    rw [applyTreeAccess_locState_out tree t_left kind leftRange active mode anc b hbLeftF]
    exact hRightPerm.ancestors_writable anc b hAnc hbRight
  · intro other b hPres hNotAnc hbRight
    have hbLeftF : leftRange b = false := hDisjRL b hbRight
    rw [applyTreeAccess_locState_out tree t_left kind leftRange active mode other b hbLeftF,
      applyTreeAccess_isTagProtected]
    exact hRightPerm.non_ancestors_safe other b hPres hNotAnc hbRight

/-- Retagging a new `Strong`-protected child `t_left_child` under `t_left` on
`leftRange` (for example, when passing `left` into a callee `foo(left, right)`
that attaches `FnEntry` protectors to both arguments) preserves
`HasUniqueWritePerm` for `t_right` on `rightRange` because on every byte
`b ∈ rightRange`, `t_left_child` has
`accessed = false ∧ perm = .reserved tyIsFreeze false ≠ .active`. -/
theorem disjoint_retagChild_preserves_hasUniqueWritePerm
    {tree : BorrowTree} {t_left t_left_child t_right : BorTag}
    {leftRange rightRange : ByteRange} {active : ActiveProtectors}
    (prot : Option ProtectorKind) (tyIsFreeze : Bool)
    (hRightPerm : HasUniqueWritePerm tree t_right rightRange active)
    (hDisj : DisjointRange leftRange rightRange)
    (hFresh : tree.present t_left_child = false) :
    HasUniqueWritePerm
      (retagChild tree t_left t_left_child prot (.reserved tyIsFreeze false) leftRange active)
      t_right rightRange active := by
  have hRightNeNew : t_right ≠ t_left_child := by
    intro hEq; rw [hEq] at hRightPerm
    have hP := hRightPerm.tag_present
    rw [hFresh] at hP; contradiction
  let tree1 := insertChildNode tree t_left t_left_child prot (.reserved tyIsFreeze false)
  have hwf1 : TreeWF tree1 :=
    insertChildNode_wf tree t_left t_left_child prot (.reserved tyIsFreeze false)
      hRightPerm.wf hFresh
  have hRightPerm1 : HasUniqueWritePerm tree1 t_right rightRange active := by
    refine ⟨hwf1, by simp [tree1, insertChildNode, hRightPerm.tag_present], ?_, ?_⟩
    · intro anc b hAnc hbRight
      have hAncNeNew : anc ≠ t_left_child := by
        intro hEq; rw [hEq] at hAnc
        simp [tree1, insertChildNode, hRightNeNew] at hAnc
      have hAncOrig : tree.isAnc anc t_right = true := by
        simpa [tree1, insertChildNode, hRightNeNew, hAncNeNew] using hAnc
      simp [tree1, insertChildNode, hAncNeNew]
      exact hRightPerm.ancestors_writable anc b hAncOrig hbRight
    · intro other b hPres hNotAnc hbRight
      by_cases hOtherNew : other = t_left_child
      · rw [hOtherNew]
        right; right
        simp [tree1, insertChildNode]
      · have hPresOrig : tree.present other = true := by
          simpa [tree1, insertChildNode, hOtherNew] using hPres
        have hNotAncOrig : tree.isAnc other t_right = false := by
          simpa [tree1, insertChildNode, hRightNeNew, hOtherNew] using hNotAnc
        have hProtEq : tree1.isTagProtected other active = tree.isTagProtected other active := by
          simp [tree1, insertChildNode, BorrowTree.isTagProtected, hOtherNew]
        rw [hProtEq]
        simp [tree1, insertChildNode, hOtherNew]
        exact hRightPerm.non_ancestors_safe other b hPresOrig hNotAncOrig hbRight
  exact disjoint_access_preserves_hasUniqueWritePerm t_left_child .read .visitChildrenOfAccessed hRightPerm1 hDisj

/-- **End-to-End Theorem `split_at_mut_unique_write_perm`**:
Suppose `HasUniqueWritePerm tree0 t_parent parentRange activeCaller` holds
before calling `slice::split_at_mut(x: &mut [T], mid) -> (&mut [T], &mut [T])`.
1. `enterCallBoundary` creates `FnEntry`-protected child `t_arg` under
   `t_parent` on `parentRange`.
2. The callee (or `TrustedFnSpec` reborrow contract) creates two distinct
   unprotected child tags `t_left` on `leftRange` and `t_right` on `rightRange`
   under `t_arg`, where `DisjointRange leftRange rightRange`,
   `SubRange leftRange parentRange`, and `SubRange rightRange parentRange`.
3. `releaseProtector` releases `t_arg`'s protector (`SkipChildrenOfAccessed` +
   removing `callId`).
Then:
- `releaseProtector` succeeds without UB,
- **Both** `HasUniqueWritePerm tree_post t_left leftRange activeCaller` and
  `HasUniqueWritePerm tree_post t_right rightRange activeCaller` hold
  simultaneously, and
- Writing through `t_left` on `leftRange` preserves `HasUniqueWritePerm` for
  `t_right` on `rightRange` (and vice versa). -/
theorem split_at_mut_unique_write_perm
    {tree0 : BorrowTree} {t_parent t_arg t_left t_right : BorTag}
    {parentRange leftRange rightRange : ByteRange}
    {activeCaller : ActiveProtectors} {callId : CallId}
    (tyIsFreeze : Bool)
    (hPerm0 : HasUniqueWritePerm tree0 t_parent parentRange activeCaller)
    (hSubLeft : SubRange leftRange parentRange)
    (hSubRight : SubRange rightRange parentRange)
    (hDisj : DisjointRange leftRange rightRange)
    (hFreshArg : tree0.present t_arg = false)
    (hFreshLeft : tree0.present t_left = false)
    (hFreshRight : tree0.present t_right = false)
    (hLeftNeArg : t_left ≠ t_arg)
    (hRightNeArg : t_right ≠ t_arg)
    (hRightNeLeft : t_right ≠ t_left)
    (hFreshCallId : ∀ n, tree0.present n = true →
      ∀ p, tree0.protector n = some p → p.callId ≠ callId) :
    let active1 := insertActiveProtector activeCaller callId
    let tree1 := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reserved tyIsFreeze false) parentRange active1
    let tree2 := retagChild tree1 t_arg t_left none (.reserved tyIsFreeze false) leftRange active1
    let tree3 := retagChild tree2 t_arg t_right none (.reserved tyIsFreeze false) rightRange active1
    let tree_post := applyReleaseProtector tree3 t_arg active1
    releaseProtectorNoUB tree3 t_arg active1 ∧
      HasUniqueWritePerm tree_post t_left leftRange activeCaller ∧
      HasUniqueWritePerm tree_post t_right rightRange activeCaller ∧
      HasUniqueWritePerm
        (applyTreeAccess tree_post t_left .write leftRange activeCaller .visitChildrenOfAccessed)
        t_right rightRange activeCaller ∧
      HasUniqueWritePerm
        (applyTreeAccess tree_post t_right .write rightRange activeCaller .visitChildrenOfAccessed)
        t_left leftRange activeCaller := by
  intro active1 tree1 tree2 tree3 tree_post
  have hDisjSymm : DisjointRange rightRange leftRange := disjointRange_symm hDisj
  have hPerm0_active1 : HasUniqueWritePerm tree0 t_parent parentRange active1 := by
    refine ⟨hPerm0.wf, hPerm0.tag_present, hPerm0.ancestors_writable, ?_⟩
    intro other b hPres hNotAnc hb
    have hProtEq : tree0.isTagProtected other active1 = tree0.isTagProtected other activeCaller := by
      simp only [BorrowTree.isTagProtected]
      cases hP : tree0.protector other with
      | none => rfl
      | some p =>
        have hNe := hFreshCallId other hPres p hP
        simp [active1, insertActiveProtector, hNe]
    rw [hProtEq]
    exact hPerm0.non_ancestors_safe other b hPres hNotAnc hb
  have hTree1Perm : HasUniqueWritePerm tree1 t_arg parentRange active1 :=
    (retagChild_hasUniqueWritePerm (some (.strong callId)) tyIsFreeze hPerm0_active1 (fun _ h => h) hFreshArg).2
  have hFreshLeft1 : tree1.present t_left = false := by
    simp [tree1, retagChild, insertChildNode, hLeftNeArg, hFreshLeft]
  have hTree2ArgPerm : HasUniqueWritePerm tree2 t_arg parentRange active1 :=
    retagUnprotectedChild_preserves_parent_hasUniqueWritePerm tyIsFreeze hTree1Perm hFreshLeft1
  have hTree2LeftPerm : HasUniqueWritePerm tree2 t_left leftRange active1 :=
    (retagChild_hasUniqueWritePerm none tyIsFreeze hTree1Perm hSubLeft hFreshLeft1).2
  have hFreshRight2 : tree2.present t_right = false := by
    simp [tree2, tree1, retagChild, insertChildNode, hRightNeLeft, hRightNeArg, hFreshRight]
  have hTree3ArgPerm : HasUniqueWritePerm tree3 t_arg parentRange active1 :=
    retagUnprotectedChild_preserves_parent_hasUniqueWritePerm tyIsFreeze hTree2ArgPerm hFreshRight2
  have hTree3RightPerm : HasUniqueWritePerm tree3 t_right rightRange active1 :=
    (retagChild_hasUniqueWritePerm none tyIsFreeze hTree2ArgPerm hSubRight hFreshRight2).2
  have hTree3LeftPerm : HasUniqueWritePerm tree3 t_left leftRange active1 :=
    disjoint_retagChild_preserves_hasUniqueWritePerm none tyIsFreeze
      hTree2LeftPerm hDisjSymm hFreshRight2
  have hArgAccInParent : ∀ b, (tree3.locState t_arg b).accessed = true → parentRange b = true := by
    intro b hAcc
    cases hbParent : parentRange b with
    | true => rfl
    | false =>
      have hbLeftOut : leftRange b = false := by
        cases hbL : leftRange b with
        | false => rfl
        | true => have hT := hSubLeft b hbL; rw [hbParent] at hT; contradiction
      have hbRightOut : rightRange b = false := by
        cases hbR : rightRange b with
        | false => rfl
        | true => have hT := hSubRight b hbR; rw [hbParent] at hT; contradiction
      have hLoc3 : (tree3.locState t_arg b).accessed = (tree2.locState t_arg b).accessed := by
        simp [tree3, retagChild_outside_range_locState, hbRightOut, Ne.symm hRightNeArg]
      have hLoc2 : (tree2.locState t_arg b).accessed = (tree1.locState t_arg b).accessed := by
        simp [tree2, retagChild_outside_range_locState, hbLeftOut, Ne.symm hLeftNeArg]
      have hLoc1 : (tree1.locState t_arg b).accessed = parentRange b :=
        retagChild_child_accessed_iff b
      rw [hLoc3, hLoc2, hLoc1, hbParent] at hAcc
      contradiction
  have hDescUnprot : ∀ d, tree3.isAnc t_arg d = true → d ≠ t_arg →
      tree3.isTagProtected d activeCaller = false := by
    intro d hDesc hdNeArg
    by_cases hdRight : d = t_right
    · rw [hdRight]
      simp [tree3, retagChild, insertChildNode, BorrowTree.isTagProtected]
    · by_cases hdLeft : d = t_left
      · rw [hdLeft]
        simp [tree3, tree2, retagChild, insertChildNode,
          BorrowTree.isTagProtected, Ne.symm hRightNeLeft]
      · have hDesc1 : tree1.isAnc t_arg d = true := by
          simpa [tree3, tree2, retagChild, insertChildNode,
            hdRight, hdLeft, Ne.symm hRightNeArg, Ne.symm hLeftNeArg] using hDesc
        have hFalse : tree1.isAnc t_arg d = false := by
          simp [tree1, retagChild, insertChildNode, hdNeArg]
        rw [hFalse] at hDesc1
        contradiction
  have hStateLeft : CalleeReborrowState tree3 t_arg t_left parentRange leftRange activeCaller callId := by
    refine ⟨hSubLeft, hTree3ArgPerm, hTree3LeftPerm.tag_present, ?_, hLeftNeArg,
      hArgAccInParent, hTree3LeftPerm.ancestors_writable, hDescUnprot⟩
    simp [tree3, tree2, retagChild, insertChildNode,
      Ne.symm hRightNeLeft, Ne.symm hRightNeArg,
      hTree1Perm.wf.isAnc_refl t_arg hTree1Perm.tag_present]
  have hStateRight : CalleeReborrowState tree3 t_arg t_right parentRange rightRange activeCaller callId := by
    refine ⟨hSubRight, hTree3ArgPerm, hTree3RightPerm.tag_present, ?_, hRightNeArg,
      hArgAccInParent, hTree3RightPerm.ancestors_writable, hDescUnprot⟩
    simp [tree3, retagChild, insertChildNode,
      hTree2ArgPerm.wf.isAnc_refl t_arg hTree2ArgPerm.tag_present]
  obtain ⟨hRelNoUB, _, hPostLeft⟩ := releaseProtector_preserves_reborrow_child hStateLeft
  obtain ⟨_, _, hPostRight⟩ := releaseProtector_preserves_reborrow_child hStateRight
  have hFrameLeftToRight :=
    disjoint_access_preserves_hasUniqueWritePerm t_left .write .visitChildrenOfAccessed hPostRight hDisj
  have hFrameRightToLeft :=
    disjoint_access_preserves_hasUniqueWritePerm t_right .write .visitChildrenOfAccessed hPostLeft hDisjSymm
  exact ⟨hRelNoUB, hPostLeft, hPostRight, hFrameLeftToRight, hFrameRightToLeft⟩

/-! ## 9. Negative Control: Why `TrustedFnSpec` Must Mint Distinct Child Reborrow Tags -/

/-- **Negative-Control Theorem `same_tag_split_unsound_control`**:
Suppose `slice::split_at_mut` is modeled via a naive `TrustedFnSpec` that does
not insert fresh child tags `t_left ≠ t_right` under `t_arg` in `BorrowTree`,
and instead returns two pointers `(ptr_left, ptr_right)` that share the same
`BorTag` (`t_arg`).
Then if the caller activates `ptr_right` on `rightRange` and then performs an
out-of-bounds raw-pointer write through `ptr_left` into a byte `b ∈ rightRange`:
1. In the **true Tree Borrows semantics** (with distinct sibling tags
   `t_left ≠ t_right`), the write through `t_left` at `b ∈ rightRange` is a
   `foreignAccess .write` on `t_right`, which transitions `t_right` at `b` to
   **`.disabled`** so any subsequent read through `t_right` at `b` is **UB**
   (`performTransition .read .localAccess false (tree_distinct4.locState t_right b) = none`).
2. In the **naive same-tag `TrustedFnSpec`** (`t_left = t_right = t_arg`), the
   write through `t_arg` at `b ∈ rightRange` is a `localAccess .write` on
   `t_arg`, which leaves `t_arg` in **`.active`** so a subsequent read through
   `ptr_right` at `b` **succeeds (`some ⟨.active, true⟩`)**, missing real Tree
   Borrows UB. -/
theorem same_tag_split_unsound_control
    {tree : BorrowTree} {t_arg t_left t_right : BorTag}
    {leftRange rightRange : ByteRange} {active : ActiveProtectors} {b : ByteOffset}
    (hPresArg : tree.present t_arg = true)
    (hAncRefl : tree.isAnc t_arg t_arg = true)
    (hArgWritable : (tree.locState t_arg b).perm = .reserved true false)
    (hNeLR : t_right ≠ t_left)
    (hbRight : rightRange b = true) :
    let tree_distinct1 := retagChild tree t_arg t_left none (.reserved true false) leftRange active
    let tree_distinct2 := retagChild tree_distinct1 t_arg t_right none (.reserved true false) rightRange active
    let tree_distinct3 := applyTreeAccess tree_distinct2 t_right .write rightRange active .visitChildrenOfAccessed
    let tree_distinct4 := applyTreeAccess tree_distinct3 t_left .write rightRange active .visitChildrenOfAccessed
    let tree_shared1 := applyTreeAccess tree t_arg .write rightRange active .visitChildrenOfAccessed
    let tree_shared2 := applyTreeAccess tree_shared1 t_arg .write rightRange active .visitChildrenOfAccessed
    (tree_distinct4.locState t_right b).perm = .disabled ∧
      performTransition .read .localAccess false (tree_distinct4.locState t_right b) = none ∧
      (tree_shared2.locState t_arg b).perm = .active ∧
      performTransition .read .localAccess false (tree_shared2.locState t_arg b) = some ⟨.active, true⟩ := by
  intro tree_distinct1 tree_distinct2 tree_distinct3 tree_distinct4 tree_shared1 tree_shared2
  have hRightNotAncLeft2 : tree_distinct2.isAnc t_right t_left = false := by
    simp [tree_distinct2, tree_distinct1, retagChild, insertChildNode, Ne.symm hNeLR]
  have hRightPres2 : tree_distinct2.present t_right = true := by
    simp [tree_distinct2, retagChild, insertChildNode]
  have hRightRefl2 : tree_distinct2.isAnc t_right t_right = true := by
    simp [tree_distinct2, retagChild, insertChildNode]
  have hRightUnprot2 : tree_distinct2.isTagProtected t_right active = false := by
    simp [tree_distinct2, retagChild, insertChildNode, BorrowTree.isTagProtected]
  have hRightLoc2 : tree_distinct2.locState t_right b = ⟨.reserved true false, true⟩ := by
    simp [tree_distinct2, retagChild, applyTreeAccess_locState_in, insertChildNode, hbRight,
      nodeAccessRelatedness, performTransition]
  have hRightLoc3 : tree_distinct3.locState t_right b = ⟨.active, true⟩ := by
    rw [applyTreeAccess_locState_in tree_distinct2 t_right .write rightRange active .visitChildrenOfAccessed
      t_right b hRightPres2 hbRight]
    simp [nodeAccessRelatedness, hRightRefl2, hRightLoc2, performTransition]
  have hRightLoc4 : tree_distinct4.locState t_right b = ⟨.disabled, true⟩ := by
    rw [applyTreeAccess_locState_in tree_distinct3 t_left .write rightRange active .visitChildrenOfAccessed
      t_right b hRightPres2 hbRight]
    simp [tree_distinct3, nodeAccessRelatedness, hRightNotAncLeft2, hRightLoc3, hRightUnprot2, performTransition]
  have hSharedLoc1 : tree_shared1.locState t_arg b = ⟨.active, true⟩ := by
    rw [applyTreeAccess_locState_in tree t_arg .write rightRange active .visitChildrenOfAccessed
      t_arg b hPresArg hbRight]
    simp [nodeAccessRelatedness, hAncRefl, hArgWritable, performTransition]
  have hSharedLoc2 : tree_shared2.locState t_arg b = ⟨.active, true⟩ := by
    rw [applyTreeAccess_locState_in tree_shared1 t_arg .write rightRange active .visitChildrenOfAccessed
      t_arg b hPresArg hbRight]
    simp [tree_shared1, nodeAccessRelatedness, hAncRefl, hSharedLoc1, performTransition]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hRightLoc4]
  · rw [hRightLoc4]; rfl
  · rw [hSharedLoc2]
  · rw [hSharedLoc2]; rfl

/-! ## 10. `TrustedFnSpec` Reborrow Descriptor (`ReborrowEdge`) & Inline Equivalence -/

/-- A declarative reborrow edge in a `TrustedFnSpec` contract: specifies that a
returned reference with freshly minted tag `childTag` is reborrowed from
`parentTag` (which may be a `FnEntry`-retagged argument `t_arg` or an inner
pointer tag `t_slice` stored inside an argument struct such as `IterMut<'a, T>`)
over `subRange` with initial permission `initPerm` (`.reserved tyIsFreeze false`
for `&mut T`, `.frozen` / `.cell` for `&T`). -/
structure ReborrowEdge where
  parentTag : BorTag
  childTag : BorTag
  subRange : ByteRange
  initPerm : Permission

def applyReborrowEdge (tree : BorrowTree) (edge : ReborrowEdge) (active : ActiveProtectors) : BorrowTree :=
  retagChild tree edge.parentTag edge.childTag none edge.initPerm edge.subRange active

def applyReborrowEdges (tree : BorrowTree) (edges : List ReborrowEdge) (active : ActiveProtectors) : BorrowTree :=
  edges.foldl (fun acc edge => applyReborrowEdge acc edge active) tree

/-- Executing a `TrustedFnSpec` call that applies `reborrowEdges` before
`applyReleaseProtector` is definitionally identical to inline callee execution
of the corresponding `RetagMode.Default` reborrows, and therefore satisfies the
exact same `HasUniqueWritePerm` postconditions for both single-reference returns
(`get_mut`) and multi-reference returns (`split_at_mut`). -/
theorem trustedSpec_reborrow_equivalence
    {tree0 : BorrowTree} {t_parent t_arg t_left t_right : BorTag}
    {parentRange leftRange rightRange : ByteRange}
    {activeCaller : ActiveProtectors} {callId : CallId}
    (tyIsFreeze : Bool)
    (hPerm0 : HasUniqueWritePerm tree0 t_parent parentRange activeCaller)
    (hSubLeft : SubRange leftRange parentRange)
    (hSubRight : SubRange rightRange parentRange)
    (hDisj : DisjointRange leftRange rightRange)
    (hFreshArg : tree0.present t_arg = false)
    (hFreshLeft : tree0.present t_left = false)
    (hFreshRight : tree0.present t_right = false)
    (hLeftNeArg : t_left ≠ t_arg)
    (hRightNeArg : t_right ≠ t_arg)
    (hRightNeLeft : t_right ≠ t_left)
    (hFreshCallId : ∀ n, tree0.present n = true →
      ∀ p, tree0.protector n = some p → p.callId ≠ callId) :
    let active1 := insertActiveProtector activeCaller callId
    let tree_entry := retagChild tree0 t_parent t_arg (some (.strong callId)) (.reserved tyIsFreeze false) parentRange active1
    let edges : List ReborrowEdge :=
      [ ⟨t_arg, t_left, leftRange, .reserved tyIsFreeze false⟩,
        ⟨t_arg, t_right, rightRange, .reserved tyIsFreeze false⟩ ]
    let tree_before_release := applyReborrowEdges tree_entry edges active1
    let tree_post := applyReleaseProtector tree_before_release t_arg active1
    releaseProtectorNoUB tree_before_release t_arg active1 ∧
      HasUniqueWritePerm tree_post t_left leftRange activeCaller ∧
      HasUniqueWritePerm tree_post t_right rightRange activeCaller := by
  intro active1 tree_entry edges tree_before_release tree_post
  obtain ⟨hNoUB, hLeft, hRight, _, _⟩ :=
    split_at_mut_unique_write_perm tyIsFreeze hPerm0 hSubLeft hSubRight hDisj
      hFreshArg hFreshLeft hFreshRight hLeftNeArg hRightNeArg hRightNeLeft hFreshCallId
  exact ⟨hNoUB, hLeft, hRight⟩

#print axioms reborrow_return_unique_write_perm
#print axioms reborrow_return_after_callee_write_unique_write_perm
#print axioms split_at_mut_unique_write_perm
#print axioms disjoint_retagChild_preserves_hasUniqueWritePerm
#print axioms same_tag_split_unsound_control
#print axioms trustedSpec_reborrow_equivalence

end CompositionalReborrowProtectorProbe
