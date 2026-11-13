# Tree Borrows Two-Stage Protector Release, Sub-Range Reborrow Preservation, and Modular Reborrow Contracts

## Summary

When a Rust function receives a `FnEntry`-protected mutable reference `t_arg`
(`&mut Pair` or `&mut [T]`) and returns a reborrowed sub-reference `t_ret`
(`&mut u32`, `(&mut [T], &mut [T])`, or `Option<&mut T>`), Tree Borrows releases
`t_arg`'s protector at frame exit (`BorrowTree.releaseProtector` in
`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` and
`Tree::release_protector` in
`rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`) before the caller uses
the returned reference. This report characterizes how two-stage protector
release interacts with sub-range reborrows, outer caller protectors, and
modular function contracts (`TrustedFnSpec`):

1. **Exact Two-Stage Protector-Release Mechanics (`SkipChildrenOfAccessed` +
   `endCall`):**
   - On every initialized (`accessed = true`) byte offset of `t_arg`,
     `Permission.associatedAccess` (`Miri/TreeBorrows/Permissions.lean:268-271`,
     `src/borrow_tracker/tree_borrows/perms.rs:311-319`) maps `.Cell => none`,
     `.Unique => some .Write`, and
     `.ReservedFrz _ | .ReservedIM | .Frozen | .Disabled => some .Read`.
   - `TraversalTree.traverse` under `ChildrenVisitMode.SkipChildrenOfAccessed`
     (`Miri/TreeBorrows/Traversal.lean:28-31,70-112`,
     `src/borrow_tracker/tree_borrows/tree_visitor.rs:89-140,248-268`) applies
     that implicit access as `LocalAccess` to `t_arg` and its ancestors,
     **skips all proper descendants of `t_arg`** (`shouldVisitChildren = false`
     at `isStart = true`), and applies `ForeignAccess` in postorder to all
     non-ancestor non-descendant nodes **while the exiting frame's protected
     tags are still active in `global.protectedTags`**. Only after all protected
     tags of the exiting frame have run `releaseProtector` does
     `GlobalState.endCall` (`Miri/TreeBorrows/GlobalState.lean:146-148`,
     `GlobalStateInner::end_call` in `src/borrow_tracker/mod.rs:181-190`)
     retire the exiting frame's protectors from `global.protectedTags`.
2. **Compositional `HasUniqueWritePerm` Preservation Across Single and Sibling
   Reborrows:**
   - Whether `t_arg` remains in unconflicted `Reserved` (`.ReservedFrz false`,
     emitting an implicit `Read` on `[0, pairSize)`) or is activated to `Unique`
     on `[off, off + sz)` during the call (emitting an implicit `Write` on
     `[off, off + sz)` and an implicit `Read` on `[0, pairSize) \ [off, off +
     sz)`), `SkipChildrenOfAccessed` leaves `t_ret` untouched: `⟨perm, true⟩` on
     `[off, off + sz)` and `⟨.ReservedFrz false, false⟩` on
     `[0, pairSize) \ [off, off + sz)`.
   - A four-conjunct relational invariant `HasUniqueWritePerm tree tag range
     activeProtectors`—requiring (i) tree well-formedness (`TreeWF`), (ii) tag
     presence, (iii) `AncestorWritable` (`.active` or unconflicted `.reserved`)
     for every ancestor on `range`, and (iv) `NonAncestorSafe` (unprotected,
     `.cell`, or unaccessed and non-`.active`) for every non-ancestor on
     `range`—is preserved across function entry retagging, sub-range reborrows,
     two-stage `releaseProtector`, subsequent caller writes (even under outer
     `FnEntry` protectors `t_outer`), and disjoint sibling splits
     (`reborrow_return_unique_write_perm`,
     `reborrow_return_after_callee_write_unique_write_perm`,
     `split_at_mut_unique_write_perm`, and
     `disjoint_retagChild_preserves_hasUniqueWritePerm` in
     [`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean)).
3. **Why Modular Function Contracts (`TrustedFnSpec`) Require a Deterministic
   `ReborrowSpec` Step:**
   - Return-value copy and validation (`validateValue` / `copyReturn`) at a
     MIR call terminator do not retag returned pointers in `BorrowTree`; in
     Rust's MIR operational semantics, child tags for returned references are
     created by `RetagMode.Default` (`RetagKind::Default`) statements inside
     the callee body before frame exit.
   - Consequently, a modular specification contract (`TrustedFnSpec`) that only
     applies an `accessFootprint` to existing allocations without inserting
     fresh child tags into `BorrowTree` before `releaseProtectorsForCall` fails
     in three ways: (a) multi-reference returns (`slice::split_at_mut`) or
     successive iterator yields (`IterMut::next`) are forced to share an
     existing `BorTag`, turning cross-slice `ForeignAccess` writes into
     `LocalAccess` writes and missing real Tree Borrows UB
     (`same_tag_split_unsound_control` in
     [`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean#L1556-L1606)
     and `neg_split_at_mut_cross_half_raw_write_disables_sibling` in
     [`support/miri_reborrow_probe/src/lib.rs`](support/miri_reborrow_probe/src/lib.rs#L168-L184));
     (b) single sub-range returns (`get_mut`) inherit `t_arg`'s over-wide
     `accessed = true` footprint across `parentRange` instead of `subRange`;
     and (c) functions like `IterMut::next(iter: &mut IterMut<'a, T>) ->
     Option<&'a mut T>` reborrow from an **inner pointer tag `t_slice`** stored
     inside `*iter` (`NonNull<T>`, which `walkValue` / `RetagVisitor` at call
     entry does not retag), not from `t_arg`.
   - Adding a deterministic `reborrowFootprint : MachineState → List Value →
     List ReborrowSpec` (executed after `accessFootprint` and before
     `releaseProtectorsForCall`, binding the minted `freshTags : List BorTag` in
     the postcondition `ens`) makes modular specification execution
     definitionally equivalent to inline callee verification
     (`trustedSpec_reborrow_equivalence` in
     [`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean#L1633-L1664)).

## Applicability

These findings apply to:

- **`proofs-rs/lean-miri`** at commit `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`:
  - `Miri/TreeBorrows/Permissions.lean` (`Permission`,
    `Permission.performAccess`, `Permission.associatedAccess`),
  - `Miri/TreeBorrows/LocationState.lean` (`LocationState`,
    `LocationState.performTransition`),
  - `Miri/TreeBorrows/Traversal.lean` (`ChildrenVisitMode`,
    `ContinueTraversal`, `TraversalTree.traverse`),
  - `Miri/TreeBorrows/TreeState.lean` (`BorrowTree.newChild`,
    `BorrowTree.performAccess`, `BorrowTree.releaseProtector`,
    `BorrowTree.deallocateBorrowRange`),
  - `Miri/TreeBorrows/GlobalState.lean` (`ProtectorKind`, `ProtectedTags`,
    `FrameState`, `GlobalState.endCall`),
  - `Miri/Interpreter/TypedRetag.lean` (`RetagMode`, `RetagPerm.fromType`,
    `TypedRetag.retagPtrValue`, `retagPlaceWith`),
  - `Miri/Interpreter/ValidityVisitor.lean` (`checkSafePointer`, `walkValue`),
    and
  - `Miri/Interpreter/MachineHooks.lean` (`beforeStackPopWithEnsure`).
- **`rust-lang/miri`** at commit `7fa591d7d4dd9af8154becbc8332f8096f8323b1`:
  - `src/borrow_tracker/tree_borrows/perms.rs` (`Permission`, `PermTransition`,
    `LocationState`, `associated_access`, `perform_access`),
  - `src/borrow_tracker/tree_borrows/tree_visitor.rs` (`ChildrenVisitMode`,
    `ContinueTraversal`, `TreeVisitor::traverse_this_parents_children_other`),
  - `src/borrow_tracker/tree_borrows/tree.rs` (`Tree::new_child`,
    `Tree::perform_access`, `Tree::release_protector`,
    `Tree::dealloc_protector`),
  - `src/borrow_tracker/mod.rs` (`ProtectorKind`, `GlobalStateInner::end_call`,
    `RetagVisitor`, `FrameExtra::on_stack_pop`), and
  - `src/machine.rs` (`MiriMachine::after_stack_push`,
    `MiriMachine::before_stack_pop`).
- **`rust-lang/rust`** at commit `8144389c895da997dbdecaa635e41d6a50be6ffd`
  (`library/core/src/slice/mod.rs:1975-2027` and
  `library/core/src/slice/iter.rs:163-250` for `slice::split_at_mut`,
  `slice::split_at_mut_unchecked`, and `slice::IterMut::next`), and **`rustc
  1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`)**
  with **`miri 0.1.0 (3ef0c22cdb 2026-11-11)`** under
  `MIRIFLAGS="-Zmiri-tree-borrows"`.
- **Lean 4** toolchains **`v4.28.0-rc1`**
  (`3b0f2862196c6a8af9eb0025ee650252694013dd`) and **`v4.34.1`**
  (`5045d0056413266e57c625dcd7c365b10e377c52`), on which all mechanized proofs
  in [`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean)
  elaborate and kernel-check with zero errors, zero warnings, and only standard
  axioms (`[propext, Classical.choice, Quot.sound]`).

Relationship to existing corpus reports:
[`reports/minirust-tree-borrows-protectors-and-program-logic-correspondence/REPORT.md`](../minirust-tree-borrows-protectors-and-program-logic-correspondence/REPORT.md)
characterizes MiniRust's `specr`-based `TreeBorrowsMemory::release_protector`
and bounded state-machine equivalence. This report complements that work by
analyzing the `lean-miri` and `rust-lang/miri` `SkipChildrenOfAccessed`
traversal, proving compositional relational postconditions (`HasUniqueWritePerm`)
for functions returning reborrowed sub-references under nested protectors, and
deriving the exact `ReborrowSpec` contract required for modular function
specifications.

## Findings

### 1. Exact Two-Stage Protector Release in `lean-miri` and `rust-lang/miri`

Basis: `source`.

#### 1.1 Per-Permission Implicit Access (`Permission.associatedAccess`)

In `Miri/TreeBorrows/Permissions.lean:258-271`
(`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`) and
`src/borrow_tracker/tree_borrows/perms.rs:301-320`
(`rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`), the implicit
access emitted for each byte location when a protector is released is:

```lean
def Permission.associatedAccess : Permission → Option AccessKind
  | .Cell => none
  | .Unique => some .Write
  | .ReservedFrz _ | .ReservedIM | .Frozen | .Disabled => some .Read
```

For each byte offset `offset` tracked in `tree.locations`,
`BorrowTree.releaseProtector` (`Miri/TreeBorrows/TreeState.lean:1036-1070`,
mirroring `Tree::release_protector` in
`src/borrow_tracker/tree_borrows/tree.rs:671-727`) inspects the released node's
location state `loc := node.perms.get? offset |>.getD node.defaultInitialPerm`:

- **Guard (`!loc.isInitialized`):** If `loc.initialized = false` (unaccessed on
  that byte), `releaseProtector` does **nothing** (`pure tree`) at `offset`.
- **Guard (`loc.isInitialized = true`):** If `loc.initialized = true`, it looks
  up `loc.permission.associatedAccess`. If `some accessKind` is returned, it
  runs `TraversalTree.traverse` starting at `idx` (`t_arg`) with
  `ChildrenVisitMode.SkipChildrenOfAccessed`.

#### 1.2 `ChildrenVisitMode.SkipChildrenOfAccessed` Traversal Partition

In `Miri/TreeBorrows/Traversal.lean:28-31,70-112` and
`src/borrow_tracker/tree_borrows/tree_visitor.rs:89-140,248-268`,
`TraversalTree.traverse` partitions all nodes `n` in `BorrowTree` into three
disjoint sets relative to the starting tag `t_arg`:

1. **Ancestors of `t_arg` (`isAnc n t_arg = true`, including `t_arg` itself):**
   Visited during the upward climb from `t_arg` to the root (`fNode` with
   `AccessRelatedness.LocalAccess` / `This` and `Ancestor`).
2. **Proper descendants of `t_arg` (`isAnc t_arg n = true ∧ n ≠ t_arg`):**
   At `t_arg` (`isStart = true`), `shouldVisitChildren` evaluates
   `match childrenMode with | .VisitChildrenOfAccessed => true |
   .SkipChildrenOfAccessed => !isStart`, which is **`false`**. The postorder
   propagation loop pushes `t_arg`'s children only when `shouldVisitChildren` is
   `true` (`Traversal.lean:94-101`, `tree_visitor.rs:124-130`), and whenever the
   upward walk later visits an ancestor of `t_arg`, it sets `excludeBranch :=
   some prevIdx` so the child subtree containing `t_arg` is skipped (`childIdx !=
   excludeIdx`). Therefore, **every proper descendant of `t_arg` is completely
   skipped** during `releaseProtector`.
3. **Non-ancestors outside `t_arg`'s subtree (`isAnc n t_arg = false ∧
   isAnc t_arg n = false`):**
   Visited in postorder (`fPropagate` with `AccessRelatedness.ForeignAccess` /
   `Distant`).

#### 1.3 Ordering Between `releaseProtector` and `endCall` at Frame Exit

In `Miri/Interpreter/MachineHooks.lean:392-429` (`beforeStackPopWithEnsure`) and
`src/borrow_tracker/mod.rs:359-397` (`FrameExtra::on_stack_pop`, called from
`MiriMachine::before_stack_pop` in `src/machine.rs:1971-1996`), stack frame exit
executes in two ordered stages:

1. **Stage 1 (`releaseProtector` loop while the exiting frame's protectors are
   still active):** For every `(allocId, tag)` recorded in the exiting frame's
   `borrowFrame.protectedTags`, the interpreter invokes
   `tree.releaseProtector tag tracker.global.protectedTags`. During this stage,
   `tracker.global.protectedTags` **still contains the exiting frame's
   protected tags** (so `t_arg` and any co-protected sibling parameters of the
   same frame still have `protected = true` in `performTransition`).
2. **Stage 2 (`GlobalState.endCall` / `GlobalStateInner::end_call`):** Only
   after all `(allocId, tag)` pairs in `borrowFrame.protectedTags` have
   completed `releaseProtector` does `GlobalState.endCall`
   (`Miri/TreeBorrows/GlobalState.lean:146-148`, matching
   `GlobalStateInner::end_call` in `src/borrow_tracker/mod.rs:181-190`) remove
   each `(allocId, tag)` of the exiting `FrameState` from `global.protectedTags`
   (modeled in [`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean#L437-L445)
   by retiring the frame's `callId` from `activeProtectors`).

Because `t_arg` is visited as `LocalAccess` during its own `releaseProtector`:

- If `t_arg` is in `.ReservedFrz false` (`accessed = true`), `associatedAccess`
  is `some .Read`, and `performAccess .Read .LocalAccess (protected := true)` on
  `.ReservedFrz false` returns `some (.ReservedFrz false)`.
- If `t_arg` is in `.Unique` (`accessed = true`), `associatedAccess` is
  `some .Write`, and `performAccess .Write .LocalAccess (protected := true)` on
  `.Unique` returns `some .Unique`.

Thus `t_arg` remaining `protected = true` during Stage 1 never causes `t_arg`'s
own implicit access to fail, while Stage 1 enforces strong-protector conflicts
against any **other** protected tag in the tree (including a co-protected
aliasing parameter in the same frame) before Stage 2 retires the exiting
frame's protectors.

### 2. Trace of Sub-Range Reborrow Return (`get_mut(x: &mut Pair) -> &mut u32`)

Basis: `source` + `execution` + `derived`.

Consider `fn get_mut(x: &mut Pair) -> &mut u32` where `Pair` (`Freeze`) has byte
range `[0, pairSize)` and the returned reference covers sub-range
`[off, off + sz) ⊆ [0, pairSize)`. In `lean-miri` syntax
(`Miri/TreeBorrows/Permissions.lean:19-28`), an unconflicted `Freeze`
reservation is `.ReservedFrz false` (conflicted is `.ReservedFrz true`); in
[`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean#L95-L101),
the combined reservation constructor `.reserved (tyIsFreeze : Bool)
(conflicted : Bool)` writes `.reserved true false` for `.ReservedFrz false` and
`.reserved false false` for `.ReservedIM`:

1. **Function Entry (`enterCallBoundary`):** `x` is retagged with
   `RetagMode.FnEntry`, inserting child tag `t_arg` under caller tag `t_parent`
   with `ProtectorKind.StrongProtector` and default initial state
   `⟨.ReservedFrz false, false⟩` (`⟨.reserved true false, false⟩`), followed by
   a `LocalAccess .Read` on `[0, pairSize)`. On `[0, pairSize)`, `t_arg` now
   has state `⟨.ReservedFrz false, true⟩`.
2. **Callee Reborrow (`&mut (*x).field`):** In MIR, reborrowing a field produces
   a `Retag` statement with `RetagMode.Default` (`prot = none`), inserting fresh
   child tag `t_ret` under `t_arg` with default initial state
   `⟨.ReservedFrz false, false⟩` everywhere and performing a `LocalAccess .Read`
   through `t_ret` on `[off, off + sz)`.
   - On `[off, off + sz)`: `t_ret` becomes `⟨.ReservedFrz false, true⟩`; `t_arg`
     (an ancestor of `t_ret`) receives `LocalAccess .Read` and stays
     `⟨.ReservedFrz false, true⟩`.
   - On `[0, pairSize) \ [off, off + sz)`: no access occurs during `t_ret`'s
     retag, so `t_ret` remains in its unaccessed default state
     `⟨.ReservedFrz false, false⟩` (`accessed = false`).

#### 2.1 Case 1: Callee Returns `t_ret` Without Writing vs. Callee Writes Before Returning

| Aspect at `releaseProtector(t_arg)` | Case 1a: Callee does **not** write (`t_arg` stays `ReservedFrz false`) | Case 1b: Callee **writes** to `[off, off + sz)` (`t_arg` is `Unique` on `[off, off + sz)`) |
| :--- | :--- | :--- |
| **`t_arg` state before `releaseProtector`** | `⟨.ReservedFrz false, true⟩` on all of `[0, pairSize)` | `⟨.Unique, true⟩` on `[off, off + sz)`; `⟨.ReservedFrz false, true⟩` on `[0, pairSize) \ [off, off + sz)` |
| **Implicit access emitted by `t_arg`** | `some .Read` on all of `[0, pairSize)` | `some .Write` on `[off, off + sz)`; `some .Read` on `[0, pairSize) \ [off, off + sz)` |
| **Effect on `t_ret` (`SkipChildrenOfAccessed`)** | **Skipped on all bytes:** `t_ret` stays `⟨.ReservedFrz false, true⟩` on `[off, off + sz)` and `⟨.ReservedFrz false, false⟩` outside `[off, off + sz)` | **Skipped on all bytes:** `t_ret` stays `⟨.Unique, true⟩` on `[off, off + sz)` and `⟨.ReservedFrz false, false⟩` outside `[off, off + sz)` |
| **Effect on ancestors of `t_arg` (`t_parent`, `t_outer`)** | Receive `LocalAccess .Read` on `[0, pairSize)`: `.Unique` stays `.Unique`, `.ReservedFrz false` stays `.ReservedFrz false` | Receive `LocalAccess .Write` on `[off, off + sz)` (becoming `⟨.Unique, true⟩`) and `LocalAccess .Read` on `[0, pairSize) \ [off, off + sz)` |
| **Effect on cousins/siblings outside `t_arg`'s subtree** | Receive `ForeignAccess .Read` on `[0, pairSize)`: `.Unique` (unprotected) becomes `.Frozen`; protected `.ReservedFrz false` becomes `.ReservedFrz true` (`conflicted = true`) on accessed bytes | Receive `ForeignAccess .Write` on `[off, off + sz)` (unprotected nodes become `.Disabled`; unaccessed protected `.Reserved`/`.Frozen` stay `.Reserved`/`.Frozen` with `accessed = false`) and `ForeignAccess .Read` on `[0, pairSize) \ [off, off + sz)` |

Why `SkipChildrenOfAccessed` is essential here: if `releaseProtector` visited
`t_arg`'s children as `ForeignAccess`, then in Case 1a (`t_arg` in
`.ReservedFrz false` emitting `Read`), if the callee had written through `t_ret`
only on part of `t_ret` or if `t_arg` emitted `ForeignAccess .Write` in Case 1b,
`t_ret` (which is **unprotected**) would receive `ForeignAccess .Write` on
`[off, off + sz)` and transition from `.Unique` or `.ReservedFrz false` to
**`.Disabled`**, making the returned reference `&mut u32` immediately unusable
in the caller. Skipping `t_arg`'s subtree preserves `t_ret` intact in both Case
1a and Case 1b.

Furthermore, because `t_ret` has `accessed = false` on
`[0, pairSize) \ [off, off + sz)`, any subsequent caller read or write through
`t_parent` (or a sibling field reborrow) on `[0, pairSize) \ [off, off + sz)`
hits `t_ret` as an **unprotected, unaccessed** node (`⟨.ReservedFrz false,
false⟩`) on those disjoint bytes and has zero effect on `t_ret`'s permissions on
`[off, off + sz)` (`test_disjoint_field_via_parent_tag_while_reborrow_live` in
[`support/miri_reborrow_probe/src/lib.rs`](support/miri_reborrow_probe/src/lib.rs#L60-L75)).

#### 2.2 Case 2: Caller Writes Through `t_ret` Under Outer Protected Ancestors (`t_outer`)

Suppose an outer caller frame holds a `FnEntry`-protected reference `t_outer`
(covering `[0, outerSize) ⊇ [0, pairSize)`), passes a reborrow `t_parent` into
`get_mut`, receives `t_ret` covering `[off, off + sz)`, and then executes a
write through `t_ret` on `[off, off + sz)`:

- By transitivity of the tree parent relation (`isAnc`),
  `isAnc t_outer t_parent = true`, `isAnc t_parent t_arg = true`, and
  `isAnc t_arg t_ret = true` imply `isAnc t_outer t_ret = true` and
  `isAnc t_parent t_ret = true`.
- Therefore, when the caller writes through `t_ret` on `[off, off + sz)`,
  `t_ret`, `t_arg` (now unprotected in the tree), `t_parent`, and `t_outer`
  (still `Strong`-protected by the outer frame) all satisfy `isAnc anc t_ret =
  true` and receive **`LocalAccess .Write`** (`Child Write`), **not**
  `ForeignAccess .Write`.
- Under `Permission.performAccess .Write .LocalAccess`, `.ReservedFrz false`
  (`conflicted = false`) and `.Unique` both transition to `some .Unique`
  regardless of whether `protected` is `true` or `false`
  (`Miri/TreeBorrows/Permissions.lean:62-112`,
  `src/borrow_tracker/tree_borrows/perms.rs:193-208`). Crucially, while `t_arg`
  was alive inside `get_mut`, `t_outer` was an **ancestor** of `t_arg` (not a
  cousin), so every read or retag on `t_arg` or `t_ret` was a `LocalAccess .Read`
  on `t_outer`, which never sets `conflicted = true` on `.ReservedFrz`!
- Consequently, the caller's write through `t_ret` transitions `t_ret`, `t_arg`,
  `t_parent`, and `t_outer` to `⟨.Unique, true⟩` on `[off, off + sz)` with zero
  protector UB (`local_write_activates_ancestors` and
  `reborrow_return_unique_write_perm` in
  [`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean#L780-L797)).

### 3. Compositional Relational Invariant (`HasUniqueWritePerm`)

Basis: `execution` + `derived`.

To reason compositionally about arbitrary chains of reborrows, nested calls,
`releaseProtector`, and disjoint slice splits (`slice::split_at_mut`), a
point-wise statement about `tag`'s own permission is insufficient: a local
write through `tag` succeeds if and only if **every ancestor** of `tag` permits
a `LocalAccess .Write` and **every non-ancestor** of `tag` in `BorrowTree`
permits a `ForeignAccess .Write`.

[`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean#L450-L473)
mechanizes the exact relational invariant required:

```lean
/-- A location state on an ancestor of `tag` can accept both `LocalAccess .read`
(staying `AncestorWritable`) and `LocalAccess .write` (becoming `.active`),
whether protected or unprotected. -/
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
```

Why each of the three disjuncts of `NonAncestorSafe` is both necessary and
closed under transitions:

1. `isProt = false`: An unprotected node **never** traps under
   `ForeignAccess .Read` or `ForeignAccess .Write` in Tree Borrows
   (`performTransition_foreign_of_nonAncestorSafe` in
   [`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean#L520-L566)).
   Once `releaseProtector` retires `t_arg`'s protector, `t_arg` and any other
   unprotected descendants of `t_arg` (such as a sibling `t_left` when reasoning
   about `t_right` in `split_at_mut`) satisfy `isProt = false`.
2. `st.perm = .cell`: Shared interior-mutable `Cell` nodes ignore protector
   conflicts under both `ForeignAccess .Read` and `ForeignAccess .Write`.
3. `st.accessed = false ∧ st.perm ≠ .active`: What if a non-ancestor `other`
   **is** currently `Strong`-protected in an active frame—for example, when a
   caller calls `both_halves_protected(left, right)` where both `left` and
   `right` receive `FnEntry` protectors in the same call frame on disjoint
   ranges `leftRange` and `rightRange`? When `left` is retagged on `leftRange`,
   its location state on `b ∈ rightRange` remains `⟨.ReservedFrz false, false⟩`
   (`⟨.reserved true false, false⟩`, satisfying `accessed = false ∧ perm ≠
   .active`). Under `ForeignAccess .Read` and `ForeignAccess .Write`, a
   protected `.ReservedFrz`, `.ReservedIM`, `.Frozen`, or `.Disabled` node with
   `accessed = false` transitions without trapping (to `.ReservedFrz true`,
   `.ReservedIM`, `.Disabled`, or `.Disabled` with `accessed = false`),
   preserving `st.accessed = false ∧ st.perm ≠ .active`!

All six core preservation and negative-control theorems are kernel-checked in
[`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean):

| Theorem | Lines in `CompositionalReborrowProtectorProbe.lean` | Statement |
| :--- | :--- | :--- |
| `reborrow_return_unique_write_perm` | [`L1132-L1206`](support/CompositionalReborrowProtectorProbe.lean#L1132-L1206) | Given `HasUniqueWritePerm tree0 t_parent parentRange activeCaller`, retagging `FnEntry` child `t_arg` on `parentRange`, retagging unprotected child `t_ret` under `t_arg` on `subRange ⊆ parentRange` without writing, and releasing `t_arg`'s protector via `applyReleaseProtector` (`SkipChildrenOfAccessed`) is UB-free, establishes `HasUniqueWritePerm tree_post t_ret subRange activeCaller`, and guarantees that a subsequent caller write through `t_ret` on `subRange` is UB-free and preserves `HasUniqueWritePerm`. |
| `reborrow_return_after_callee_write_unique_write_perm` | [`L1215-L1321`](support/CompositionalReborrowProtectorProbe.lean#L1215-L1321) | Same as `reborrow_return_unique_write_perm`, except the callee also writes through `t_ret` on `subRange` before returning (so `t_arg` is `.active` on `subRange` and `.reserved` on `parentRange \ subRange`, emitting implicit `Write` on `subRange` and implicit `Read` on `parentRange \ subRange` during `releaseProtector`). |
| `split_at_mut_unique_write_perm` | [`L1418-L1535`](support/CompositionalReborrowProtectorProbe.lean#L1418-L1535) | Given `HasUniqueWritePerm tree0 t_parent parentRange activeCaller` and disjoint sub-ranges `leftRange, rightRange ⊆ parentRange`, retagging `FnEntry` child `t_arg` on `parentRange`, retagging distinct unprotected children `t_left` and `t_right` under `t_arg`, and releasing `t_arg`'s protector establishes **both** `HasUniqueWritePerm tree_post t_left leftRange activeCaller` and `HasUniqueWritePerm tree_post t_right rightRange activeCaller` simultaneously, and writing through `t_left` on `leftRange` frames `HasUniqueWritePerm` on `t_right` over `rightRange` (and vice versa). |
| `disjoint_retagChild_preserves_hasUniqueWritePerm` | [`L1356-L1398`](support/CompositionalReborrowProtectorProbe.lean#L1356-L1398) | Retagging a `Strong`-protected child `t_left_child` under `t_left` on `leftRange` (e.g., `FnEntry` retag when passing `(left, right)` into a callee) preserves `HasUniqueWritePerm` for `t_right` on a disjoint `rightRange`. |
| `same_tag_split_unsound_control` | [`L1556-L1606`](support/CompositionalReborrowProtectorProbe.lean#L1556-L1606) | Negative control proving that if `split_at_mut` returns two pointers sharing the same `BorTag` (`t_arg`) instead of distinct child tags `t_left ≠ t_right`, an out-of-bounds write through `ptr_left` into `b ∈ rightRange` after activating `ptr_right` leaves `t_arg` in `.active` (so reading `ptr_right` at `b` returns `some ⟨.active, true⟩`), whereas true Tree Borrows transitions `t_right` at `b` to `.disabled` (so reading `ptr_right` at `b` returns `none`, i.e., UB). |
| `trustedSpec_reborrow_equivalence` | [`L1633-L1664`](support/CompositionalReborrowProtectorProbe.lean#L1633-L1664) | Applying declarative `ReborrowEdge` descriptors after `accessFootprint` and before `applyReleaseProtector` produces the exact same `BorrowTree` state and `HasUniqueWritePerm` postconditions as inline callee reborrowing. |

### 4. Why Modular Function Contracts (`TrustedFnSpec`) Require a `ReborrowSpec` Step

Basis: `source` + `execution` + `derived`.

In an operational MIR verifier that supports both inline callee verification and
modular specification contracts (`TrustedFnSpec`) for external or standard
library functions (such as `core::slice::split_at_mut`, `IterMut::next`, or a
specified `get_mut`), consider what happens at the call boundary:

1. **Before the call (`enterCallBoundary`):** The recursive retag visitor
   (`TypedRetag.retagPtrValue` in `Miri/Interpreter/TypedRetag.lean:173-190` and
   `checkSafePointer` / `walkValue` in
   `Miri/Interpreter/ValidityVisitor.lean:196-241`, corresponding to
   `RetagVisitor` in `src/borrow_tracker/mod.rs:212-357`) traverses the argument
   values by type, retagging `&mut T` / `&T` arguments (and references nested
   inside algebraic data types like `Option<&mut T>` or tuples) with
   `RetagMode.FnEntry`, which mints protected argument tags `t_arg` in
   `BorrowTree`. Crucially, the visitor **stops at raw pointers (`*const T`,
   `*mut T`, `NonNull<T>`)** and only recurses through `Box` when `fromBox =
   true`.
2. **At the call return (`validateValue retLayout retVal` + `copyReturn`):**
   A MIR `Call` terminator does **not** run `retag` on the returned value; in
   `rustc`'s MIR lowering, any `Retag` (`RetagKind::Default`) for a returned
   reference is emitted as a statement **inside the callee body** when the
   reborrow expression is evaluated, prior to `Return`.

Therefore, if a modular contract `TrustedFnSpec` only applies an
`accessFootprint : MachineState → List Value → Option (List AccessSpec)` to
existing allocations and then runs `releaseProtectorsForCall` without inserting
child reborrow tags into `BorrowTree`, three soundness and precision failures
arise:

1. **Multi-Reference Returns (`slice::split_at_mut`) and Successive Yields
   (`IterMut::next`) Cannot Share an Existing Tag:**
   In `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`
   (`library/core/src/slice/mod.rs:1975-2027`), `split_at_mut` calls
   `split_at_mut_unchecked`, which executes
   `(&mut *slice_from_raw_parts_mut(ptr, mid), &mut *slice_from_raw_parts_mut(ptr.add(mid), len - mid))`.
   In MIR, the two `&mut *...` expressions execute two separate
   `RetagMode.Default` reborrows from `ptr` (which carries `t_arg`), minting two
   distinct sibling tags `t_left ≠ t_right` under `t_arg` with initial accessed
   footprints `[0, mid * sizeof::<T>())` and `[mid * sizeof::<T>(), len *
   sizeof::<T>())`. If a `TrustedFnSpec` for `split_at_mut` does not mint fresh
   child tags in `BorrowTree`, both returned slices must carry the only
   available tag (`t_arg`). As proven in `same_tag_split_unsound_control`
   ([`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean#L1556-L1606))
   and demonstrated by Miri in
   `neg_split_at_mut_cross_half_raw_write_disables_sibling`
   ([`support/miri_reborrow_probe/src/lib.rs`](support/miri_reborrow_probe/src/lib.rs#L168-L184)),
   sharing `t_arg` between `left` and `right` causes an out-of-bounds write
   through a raw pointer derived from `left` into `right`'s range to be treated
   as a `LocalAccess .Write` on `t_arg` (keeping `right` `.active`) instead of a
   `ForeignAccess .Write` on `t_right` (which disables `t_right` and triggers
   UB).
2. **Single Sub-Range Returns (`get_mut`) Have the Wrong `accessed` Footprint if
   They Reuse `t_arg`:**
   On `t_arg`, `enterCallBoundary` sets `accessed = true` across all of
   `parentRange` (`[0, pairSize)`). On a genuine child reborrow `t_ret` covering
   `subRange = [off, off + sz)`, `t_ret` has `accessed = true` **only** on
   `subRange` and `accessed = false` on `parentRange \ subRange`. If a modular
   contract returns `t_arg` directly instead of a child `t_ret`, `t_arg` has
   `accessed = true` on `parentRange \ subRange`, so a foreign write on
   `parentRange \ subRange` would disable `t_arg` on `parentRange \ subRange`
   instead of seeing an unaccessed node.
3. **Indirect Reborrows (`IterMut::next`) Originate From an Un-Retagged Inner
   Pointer Tag (`t_slice`), Not From `t_arg`:**
   In `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`
   (`library/core/src/slice/iter.rs:163-250`), `IterMut<'a, T>` stores
   `ptr: NonNull<T>` and `end_or_len: *mut T` (raw pointers carrying the
   original slice tag `t_slice`), plus `_marker: PhantomData<&'a mut T>`. When
   `IterMut::next(self: &mut IterMut<'a, T>) -> Option<&'a mut T>` is called:
   - `enterCallBoundary` retags `self: &mut IterMut<'a, T>` with `FnEntry` tag
     `t_self` on the `IterMut` struct allocation `alloc_iter`, but **does not**
     retag `self.ptr: NonNull<T>` because `walkValue` / `RetagVisitor` stops at
     raw pointers!
   - Inside `IterMut::next`, advancing `self.ptr` and constructing
     `Some(&mut *ptr)` performs a `LocalAccess .Write` on `alloc_iter` through
     `t_self` and a `RetagMode.Default` reborrow on the backing array allocation
     `alloc_slice` with **parent tag `t_slice`** (the tag stored inside
     `self.ptr` in pre-state memory) over the single element's `subRange`.

#### 4.1 Exact `ReborrowSpec` Extension for `TrustedFnSpec`

To make `TrustedFnSpec` both sound and compositional across `get_mut`,
`slice::split_at_mut`, and `IterMut::next`, `TrustedFnSpec` must include a
deterministic `reborrowFootprint` step between `accessFootprint` and
`releaseProtectorsForCall`:

```lean
/-- Declarative description of a single `RetagMode.Default` child reborrow
performed by a specified function before returning. -/
structure ReborrowSpec where
  allocId : AllocId
  /-- Parent tag in `allocId`'s `BorrowTree` from which the returned reference is
  derived. This may be an `FnEntry`-retagged argument tag `t_arg` (as in
  `get_mut` or `split_at_mut`) or a pointer tag `t_slice` read from pre-state
  memory (as in `IterMut::next`). -/
  parentTag : BorTag
  /-- Sub-range `[offset, offset + size)` over which the child tag receives its
  initial `LocalAccess .Read` during retagging. -/
  offset : Nat
  size : Nat
  /-- Initial permission at retag time: `.ReservedFrz false` for `&mut T` when
  `T: Freeze` or `.ReservedIM` when `!T: Freeze` (written
  `.reserved tyIsFreeze false` in the probe), `.Unique` for 2-phase-disabled /
  `Box`, `.Frozen` for `&T` when `T: Freeze`, or `.Cell` when `!T: Freeze`. -/
  initPerm : Permission

structure TrustedFnSpec where
  req : MachineState → List Value → Prop
  accessFootprint : MachineState → List Value → Option (List AccessSpec)
  /-- Deterministic list of child reborrows created before frame exit. Each
  entry mints a fresh `BorTag` from `st.nextBorTag` in order. -/
  reborrowFootprint : MachineState → List Value → List ReborrowSpec := fun _ _ => []
  /-- Postcondition relates pre-state `st`, post-entry `FnEntry`-retagged
  argument values `args'`, the freshly minted reborrow tags
  `freshTags : List BorTag` (in 1-to-1 correspondence with `reborrowFootprint`),
  post-state `st'`, and return value `retVal`. -/
  ens : MachineState → List Value → List BorTag → MachineState → Value → Prop
```

And the call-boundary execution transition for a specified function is:

1. `enterCallBoundary st args argLayouts` (mints `FnEntry` protectors for
   reference arguments, producing `(st_entry, args', frameProtectors)`).
2. Assert `spec.req st_entry args'` and compute `some accesses :=
   spec.accessFootprint st_entry args'`.
3. Apply `accesses` to `st_entry` via `applyAccessFootprint`, yielding `st_acc`
   (must not trap).
4. For each `r ∈ spec.reborrowFootprint st_entry args'` in order:
   - Allocate `t_fresh := st_cur.nextBorTag` and increment `nextBorTag`.
   - Insert `t_fresh` as an unprotected (`prot := none`) child of `r.parentTag`
     in `alloc.borrowTree` (for `r.allocId`) with default initial permission
     `⟨r.initPerm, false⟩`.
   - Perform `BorrowTree.performAccess t_fresh .Read ⟨r.offset, r.size⟩
     st_cur.activeProtectors` (which must not trap).
   - Record `t_fresh` in `freshTags : List BorTag`.
5. Run `releaseProtectorsForCall st_reborrowed frameProtectors` (which executes
   `BorrowTree.releaseProtector` with `SkipChildrenOfAccessed` for every tag in
   `frameProtectors` while the exiting frame's protectors are still active, and
   then retires them via `GlobalState.endCall`), yielding `st_rel`.
6. Quantify over `(st', retVal)` satisfying `spec.ens st_entry args' freshTags
   st' retVal`, `validateValue retLayout retVal`, and frame preservation of all
   `BorrowTree`s from `st_rel`.

By `trustedSpec_reborrow_equivalence`
([`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean#L1633-L1664)),
this 6-step sequence produces the exact same post-call `BorrowTree` as inline
execution of the callee body.

## Boundaries

1. **Unprotected Child Retags (`RetagMode.Default`) Only:**
   The preservation theorems `reborrow_return_unique_write_perm` and
   `split_at_mut_unique_write_perm` rely on the fact that references created
   inside a callee and returned to the caller are retagged with
   `RetagMode.Default` (`prot = none`), not `RetagMode.FnEntry`. A tag with
   `RetagMode.FnEntry` cannot outlive its defining call frame because its
   protector is released at frame exit.
2. **Interior Mutability (`UnsafeCell` / `!Freeze`) Outside the Reborrowed
   Sub-Range:**
   `HasUniqueWritePerm` covers unique mutable borrows (`&mut T` where `T:
   Freeze` has initial permission `.ReservedFrz false` or `T: !Freeze` has
   initial permission `.ReservedIM`, modeled by `tyIsFreeze : Bool` in
   `Permission.reserved (tyIsFreeze : Bool) (conflicted : Bool)`). For shared
   references `&Cell<T>` (`Permission.cell`), `NonAncestorSafe` already includes
   the disjunct `st.perm = .cell`, which is invariant under arbitrary foreign
   reads and writes, but shared-read-only references `&T` (`Permission.frozen`)
   require a dual `HasSharedReadPerm` invariant (`ancestors_readable` +
   `non_ancestors_read_safe`) rather than `HasUniqueWritePerm`.
3. **Allocation Liveness During `releaseProtector`:**
   In both `lean-miri` (`Miri/Interpreter/MachineHooks.lean:399-415` and
   `BorrowTree.deallocateBorrowRange` in `Miri/TreeBorrows/TreeState.lean:1076-1156`)
   and `rust-lang/miri` (`src/borrow_tracker/mod.rs:368-383` and
   `Tree::dealloc_protector`), if an allocation was deallocated during the call,
   strong protectors were already checked at deallocation time;
   `HasUniqueWritePerm` assumes the allocation remains live across the call.

## Evidence

- **`source` (`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):**
  - `Miri/TreeBorrows/Permissions.lean:19-112,258-271`
    (`Permission`, `Permission.performAccess`, `Permission.associatedAccess`),
  - `Miri/TreeBorrows/LocationState.lean:36-40,128-161`
    (`LocationState`, `LocationState.performTransition`),
  - `Miri/TreeBorrows/Traversal.lean:28-31,70-112`
    (`ChildrenVisitMode.SkipChildrenOfAccessed`, `TraversalTree.traverse`),
  - `Miri/TreeBorrows/TreeState.lean:943-1156`
    (`BorrowTree.newChild`, `BorrowTree.performAccess`,
    `BorrowTree.releaseProtector`, `BorrowTree.deallocateBorrowRange`),
  - `Miri/TreeBorrows/GlobalState.lean:17-31,61-63,146-148`
    (`ProtectorKind`, `ProtectedTags`, `FrameState`, `GlobalState.endCall`),
  - `Miri/Interpreter/TypedRetag.lean:173-190` (`TypedRetag.retagPtrValue`) and
    `Miri/Interpreter/ValidityVisitor.lean:196-241` (`checkSafePointer`,
    `walkValue`), and
  - `Miri/Interpreter/MachineHooks.lean:392-429`
    (`beforeStackPopWithEnsure`).
- **`source` (`rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`):**
  - `src/borrow_tracker/tree_borrows/perms.rs:190-320`
    (`Permission::perform_access`, `Permission::associated_access`),
  - `src/borrow_tracker/tree_borrows/tree_visitor.rs:89-140,248-268`
    (`ChildrenVisitMode::SkipChildrenOfAccessed`,
    `TreeVisitor::traverse_this_parents_children_other`),
  - `src/borrow_tracker/tree_borrows/tree.rs:671-727`
    (`Tree::release_protector`), and
  - `src/borrow_tracker/mod.rs:181-190,212-397` (`GlobalStateInner::end_call`,
    `RetagVisitor`, `FrameExtra::on_stack_pop`).
- **`source` (`rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`):**
  - `library/core/src/slice/mod.rs:1975-2027` (`slice::split_at_mut`,
    `slice::split_at_mut_unchecked`), and
  - `library/core/src/slice/iter.rs:163-250` (`slice::IterMut` definition and
    `Iterator::next` implementation).
- **`execution` and `derived` (Lean 4 Mechanization in
  [`support/CompositionalReborrowProtectorProbe.lean`](support/CompositionalReborrowProtectorProbe.lean)):**
  - 1,673-line standalone Lean 4 module checked on both `leanprover/lean4:v4.28.0-rc1`
    (`3b0f2862196c6a8af9eb0025ee650252694013dd`) and `leanprover/lean4:v4.34.1`
    (`5045d0056413266e57c625dcd7c365b10e377c52`) on `2026-11-12` with zero
    `sorryAx` and `#print axioms` confirming only
    `[propext, Classical.choice, Quot.sound]` for
    `reborrow_return_unique_write_perm`,
    `reborrow_return_after_callee_write_unique_write_perm`,
    `split_at_mut_unique_write_perm`,
    `disjoint_retagChild_preserves_hasUniqueWritePerm`,
    `same_tag_split_unsound_control`, and `trustedSpec_reborrow_equivalence`.
- **`execution` (Miri Tree Borrows Probe in
  [`support/miri_reborrow_probe/src/lib.rs`](support/miri_reborrow_probe/src/lib.rs)):**
  - Executed on `2026-11-12` with `rustc 1.102.0-nightly (3ef0c22cdb
    2026-11-11)` and `miri 0.1.0 (3ef0c22cdb 2026-11-11)` under
    `MIRIFLAGS="-Zmiri-tree-borrows"`:
    - All 4 positive tests
      (`test_case1_and_case2_get_mut_unwritten_and_written`,
      `test_disjoint_field_via_parent_tag_while_reborrow_live`,
      `test_split_at_mut_and_dual_protected_callee`, and
      `test_iter_mut_successive_reborrows`) pass with zero Tree Borrows errors.
    - Both negative-control tests
      (`neg_parent_write_on_subrange_disables_returned_reborrow` and
      `neg_split_at_mut_cross_half_raw_write_disables_sibling`) fail with the
      exact predicted Tree Borrows diagnostic:
      `Undefined Behavior: trying to reborrow <...> for Unique permission at alloc...[<offset>], but that tag does not exist in the borrow stack for this location` /
      `this error occurs as part of reborrow at alloc...[<range>]:read access through <tag> is forbidden`
      because the child tag was transitioned from `Unique` to `Disabled` by a
      foreign write on the overlapping byte range.

## Revalidation

To re-verify the mechanized Lean 4 proofs on Lean `v4.28.0-rc1` or `v4.34.1`
from the package directory:

```bash
lean support/CompositionalReborrowProtectorProbe.lean
```

Expected output on both toolchains (exit code `0`, zero warnings/errors):

```text
'CompositionalReborrowProtectorProbe.reborrow_return_unique_write_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CompositionalReborrowProtectorProbe.reborrow_return_after_callee_write_unique_write_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CompositionalReborrowProtectorProbe.split_at_mut_unique_write_perm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CompositionalReborrowProtectorProbe.disjoint_retagChild_preserves_hasUniqueWritePerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CompositionalReborrowProtectorProbe.same_tag_split_unsound_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CompositionalReborrowProtectorProbe.trustedSpec_reborrow_equivalence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

To re-run the Miri Tree Borrows execution probe without leaving `target/` or
`Cargo.lock` artifacts in the corpus working tree, copy
`support/miri_reborrow_probe` to a temporary directory first:

```bash
tmpdir="$(mktemp -d)"
cp -R support/miri_reborrow_probe "$tmpdir/"
MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test \
  --manifest-path "$tmpdir/miri_reborrow_probe/Cargo.toml"
MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test \
  --manifest-path "$tmpdir/miri_reborrow_probe/Cargo.toml" -- --ignored
rm -rf "$tmpdir"
```
