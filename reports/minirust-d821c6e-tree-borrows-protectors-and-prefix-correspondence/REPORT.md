# MiniRust Tree Borrows Protectors, Coupled vs. Factored Prefix Correspondence, and `libspecr` Copy-on-Write Semantics (`d821c6e` / `15200eb`)

## Summary

MiniRust (`minirust/minirust` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`) specifies its Tree Borrows aliasing model across `spec/mem/tree_borrows/{memory.md,tree.md,state_machine_unprotected.md,state_machine_protected.md}` as a wrapper (`TreeBorrowsMemory<M>`) around `BasicMemory`, executing inside `specr` (`minirust/specr` at commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348`, published as `libspecr 0.1.41`). In the specification, each allocation carries a recursive permission tree (`Node` with `permissions: List<Permission>`, `protected: Protected`, and `children: List<Node>`), mutated functionally through `libspecr`'s garbage-collected copy-on-write containers (`List<T>`, `Map<K, V>`, `Set<T>` backed by `GcCow<T>`) and fallible `?` error propagation.

This report consolidates a 10-stage source and mechanized Lean 4 (`v4.34.1`) investigation of MiniRust's Tree Borrows specification and its `libspecr` runtime substrate. Across 88 `Tree*.lean` modules, 3 `Helper*.lean` modules, and 2 shared `BasicMemory` modules (93 modules and 1,026 kernel-checked `#print axioms` theorem audits in total, re-verified on `2026-10-24`), the investigation establishes:

1. **Executable vs. prose discrepancies and two-stage protector release in `tree.md` and `memory.md`**:
   - In `Node::access` and `Node::release_protector` (`spec/mem/tree_borrows/tree.md`), `path: Option<Path>` encodes `Some(path)` as `NodeRelation::Local` (visited along ancestors up to and including the accessed node `Some([])`, after which `subpath` yields `None` for all descendants) and `None` as `NodeRelation::Foreign` (all non-ancestors, including descendants of the accessed node), whereas the nearby prose comment reverses `Some` and `None`.
   - `TreeBorrowsMemory::release_protector` (`spec/mem/tree_borrows/memory.md:201-235`) executes in **two stages**: (a) a targeted `access_node(p.path, ...)` pass that converts `p.path`'s permission array via `unprotect()` and collects per-byte implicit accesses `List<Option<AccessKind>>`, followed by a liveness check on the allocation; and (b) if the allocation is still live, a tree-wide `Node::release_protector(Some(p.path), accesses)` traversal that at `Some([])` clears `self.protected = Protected::No` and **returns immediately without traversing `p.path`'s subtree**, while applying the implicit accesses at all ancestor (`Local`) and non-ancestor/outside-subtree (`Foreign`) nodes.
2. **Transactional `?` rollback boundaries vs. nested `GcCow` copy-on-write**:
   - In `BasicMemory::store` and `BasicMemory::load` (`spec/mem/basic.md:227-274`), `let mut alloc = self.allocations[id];` copies the value-type `Allocation` into a local variable; if `T::access` returns `Err(Ub)` via `?`, `self.allocations.set(id, alloc)` is never reached, rolling back the allocation update.
   - By contrast, inside `List::mutate_at` (`libspecr/src/list/mod.rs`) and `GcCow::mutate` (`libspecr/src/gc/gccow.rs`), `GcCow::mutate` clones the inner `Vec`, runs the closure `&mut T -> O` (returning `O` opaquely without inspecting whether `O` is `Result::Err`), allocates a new GC cell for the mutated `Vec`, and overwrites `*self` **before** the caller's `?` operator inspects `O` (`HelperValueHeap`, `HelperNestedMutation`, `HelperValueControls`).
3. **End-to-end coupled vs. factored `TreeBorrowsMemory` state and all-prefix correspondence**:
   - Separating recursive `Node` trees (`TreeReference`, `TreeMemory`) into an ordered tree topology plus a flat path-indexed store (`TreeFactored`, `TreeFactoredMemory`) preserves exact operational status, diagnostics, returned pointers/bytes, and reified residual states across `allocate` root birth, demonic allocator base-address choice, `load`/`store` with recursive reference provenance, live `reborrow` child insertion, `dereferenceable`, `deallocate` strong-protector UB checks, `exit` leak checks, and ordered `end_call` protector release lists (`TreeCorrespondence` through `TreeEndCallFailureControls`).
4. **Upstream `libspecr 0.1.41` crate vs. git `15200eb` packaging drift**:
   - Although `libspecr-0.1.41.crate`'s embedded `.cargo_vcs_info.json` records `"sha1": "15200eb5e676e2ee91f43bd79e674f8fc32e5348"`, its source files differ from git commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348` in `minirust/specr`: the git tree adds `#[derive(Clone, Copy)]` (instead of `#[derive(Clone)]`) to `List`, `Set`, `Map`, `GcCow`, and `Obj`, and adds `#[repr(transparent)]` to `Obj<T>`.

## Applicability

- **Upstream specification subjects**:
  - `minirust/minirust` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (retained archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`):
    - `spec/mem/tree_borrows/memory.md` (9,666 bytes; SHA-256 `6dd36c2f4b18e8fa3775c79e0c1a158cf129224fb2cb606a8a3e134b04765e53`)
    - `spec/mem/tree_borrows/tree.md` (5,532 bytes; SHA-256 `9f2de7f400f31f0a130da77f51936be45b3e7f7fc8743934bc816aaebbb0e56c`)
    - `spec/mem/tree_borrows/state_machine_unprotected.md` (4,507 bytes; SHA-256 `d21fa9d19e5c828416aa67fffe86137f54d1ffbe26dc42d282f704ff97a65668`)
    - `spec/mem/tree_borrows/state_machine_protected.md` (8,415 bytes; SHA-256 `770e0ebff4699c14284e699b6a48eb5a80147f6965056ca9000f74a353baaf98`)
    - `spec/mem/basic.md` (10,275 bytes; SHA-256 `8bb62a21b6cd0050e8ac2b0c690be89ef1e7de4b779b18666a98b683b63a3763`)
    - `spec/lang/machine.md` (14,940 bytes; SHA-256 `121c624125adf8d8d988b6d088d8e85687e8a275ee703a80e486dcb05dfbd91c`)
    - `spec/lang/step/reborrow.md` (8,450 bytes; SHA-256 `56dd4774650317972e4bb1dbbf170fd3899038c4e18bc0d4fd33dbcd1f4f6a00`)
    - `spec/lang/step/terminators.md` (9,938 bytes; SHA-256 `c24989ef7bc92298a11268bc7766cfab93b751bc4ca6f7f676c0115fd4bc768c`)
  - `minirust/specr` at commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348` (archive SHA-256 `7e39738319f77a43fd0ce8e185888306b3a777f7b3f9d3234ec1802b9da5e220`) and crates.io `libspecr 0.1.41` (archive SHA-256 `a3c0c46f39513f6c4b533ec6bea7d623f6761fd0a610b1152db7f2e4dd385a61`).
- **Mechanized verification subject**: Lean `v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`), using only `{propext, Quot.sound, Classical.choice}`.

## Findings

### 1. Tree Borrows Permission Lattice, Subpath Relation, and Two-Stage Protector Release (`tree.md`, `memory.md`, `state_machine_*.md`)

**Basis**: `source` and `execution`

#### 1.1 Unprotected vs. Protected Permission Lattices (`TreePermissions.lean`)

In `spec/mem/tree_borrows/state_machine_unprotected.md` and `state_machine_protected.md`, each node in an allocation's borrow tree stores a `Protected` flag (`No`, `Weak`, `Strong`) and a byte-indexed permission vector `permissions: List<Permission>`, where `Permission` is a tagged sum `Unprotected(UnprotectedPermission)` or `Protected(ProtectedPermission)`:

- `UnprotectedPermission` has 6 states: `Cell`, `Reserved`, `ReservedIm`, `Unique`, `Frozen`, `Disabled`.
- `ProtectedPermission` has 5 constructors (8 concrete states): `Cell`, `Reserved { had_local_read: bool, had_foreign_read: bool }`, `Unique`, `Frozen { had_local_read: bool }`, and `Disabled`. Under a foreign write, a protected `Reserved { had_local_read: false, .. }` becomes `Reserved { had_local_read: false, had_foreign_read: true }` rather than `Disabled`, whereas a foreign write against protected `Unique`, `Frozen`, or `Reserved { had_local_read: true, .. }` immediately throws UB (`foreignWriteProtected` in [`support/TreePermissions.lean:45-177`](support/TreePermissions.lean#L45-L177)).
- Calling `unprotect()` (`state_machine_protected.md:94-112`; [`TreePermissions.lean:179-203`](support/TreePermissions.lean#L179-L203)) maps each `ProtectedPermission` to `(UnprotectedPermission, Option<AccessKind>)`:
  - `ProtectedPermission::Unique` $\mapsto$ `(UnprotectedPermission::Unique, Some(AccessKind::Write))`
  - `ProtectedPermission::Reserved { had_local_read: true, .. }` $\mapsto$ `(UnprotectedPermission::Reserved, Some(AccessKind::Read))`
  - `ProtectedPermission::Frozen { had_local_read: true }` $\mapsto$ `(UnprotectedPermission::Frozen, Some(AccessKind::Read))`
  - All other states emit `None` for the implicit access.

#### 1.2 Executable `Some(path)` vs. `None` Node Relation and Comment Reversal in `tree.md`

In `spec/mem/tree_borrows/tree.md` (`Node::access` and `Node::release_protector`), the parameter `path: Option<Path>` determines `NodeRelation`:

- Executable equations (`tree.md:71-106`, mechanized in [`TreeReference.lean:100-110`](support/TreeReference.lean#L100-L110)):
  - `let rel = if path.is_some() { NodeRelation::Local } else { NodeRelation::Foreign };`
  - For each child index `idx`, `let subpath = path.and_then(|path| if path.get(0) == Some(idx) { Some(path[1..]) } else { None });`
  - Consequently, every ancestor of the target node has `path = Some(idx :: rest)` (`Local`), the target node itself receives `path = Some([])` (`Local`), and **every descendant of the target node** receives `subpath = None` (`Foreign`), just like sibling subtrees.
- Prose comment discrepancy (`tree.md:62-66`): The comment above `Node::access` states the opposite convention (*"`path` is `None` if the accessed node is an ancestor of `self`, or `Some` of a path from `self` to the accessed node"*). Following the prose comment instead of the executable equations would invert `Local` and `Foreign` transitions on every ancestor and descendant (`TreeMemoryControls.lean`).

#### 1.3 Two-Stage `release_protector` and Subtree Skipping (`memory.md:201-235`, `tree.md:108-145`)

In `spec/mem/tree_borrows/memory.md:201-235`, `TreeBorrowsMemory::release_protector(p: Provenance)` executes in two distinct stages:

1. **Stage 1 — Targeted conversion and implicit-access extraction (`unprotectAt`, [`TreeReference.lean:273-305`](support/TreeReference.lean#L273-L305))**:
   Descends via `alloc.extra.root.access_node(p.path, ...)` to the single node at `p.path`, asserts `node.protected != Protected::No`, converts each byte's `Permission::Protected(perm)` via `perm.unprotect()`, writes the resulting `Permission::Unprotected` array back into `node.permissions`, and returns the per-byte implicit access vector `accesses: List<Option<AccessKind>>`.
2. **Liveness gate (`memory.md:223-227`)**:
   Checks `if !self.mem.allocations[p.alloc_id.0].live { return ret(()); }`. If the allocation was already deallocated, Stage 1's conversion is committed (or retained in `alloc.extra`), and Stage 2 is skipped.
3. **Stage 2 — Complement traversal (`releaseCore` / `releaseTraverse`, [`TreeReference.lean:184-212,307-311`](support/TreeReference.lean#L184-L212))**:
   Calls `alloc.extra.root.release_protector(Some(p.path), accesses)` (`tree.md:108-145`). At `path == Some(Path::new())` (`Some([])`, i.e., the released node `p.path` itself), `Node::release_protector` sets `self.protected = Protected::No` and **immediately returns `ret(())` without applying `accesses` to `self` or recursing into `self.children`**. For all other visited nodes (`Some(idx :: rest)` ancestors with `NodeRelation::Local`, and `None` sibling subtrees with `NodeRelation::Foreign`), it applies `accesses` byte-by-byte and recurses into their children.
   - Because `Node::release_protector` returns early at `Some([])`, **descendants of the released node `p.path` are never visited by the implicit access pass**, whereas ancestors receive `Local` implicit accesses and non-descendant cousins/siblings receive `Foreign` implicit accesses (`TreeTraversal.lean`, `TreeReleaseAgreement.lean`, `TreeMemoryControls.lean`).

### 2. Transactional `?` Rollback in `BasicMemory` vs. `GcCow` Copy-on-Write Persistence in `libspecr`

**Basis**: `source`, `execution`, and `derived`

A subtle semantic boundary arises from how MiniRust combines value-typed records (`List<T>`, `Map<K, V>`) with fallible `?` returns (`Result<T, TerminationInfo>`):

1. **Outer `BasicMemory` allocation updates roll back on `T::access` UB (`spec/mem/basic.md:227-274`)**:
   In `BasicMemory::store` and `BasicMemory::load`, the method copies `let mut alloc = self.allocations[id];`, mutates `alloc.extra` via `T::access(...) ?`, and only reaches `self.allocations.set(id, alloc)` if `T::access` returns `Ok(())`. If `T::access` throws UB mid-traversal, the local copy `alloc` is dropped and `self.allocations[id]` in `BasicMemory` remains unchanged (`TreeMemory.lean`, `TreeExceptions.lean`).
2. **Inner `List::mutate_at` and `GcCow::mutate` commit before `?` inspects `Result` (`libspecr/src/list/mod.rs:140-149`, `libspecr/src/gc/gccow.rs:42-48`)**:
   In `minirust/specr` (`15200eb5e676e2ee91f43bd79e674f8fc32e5348`), `List::mutate_at` is implemented as:
   ```rust
   pub fn mutate_at<O>(&mut self, i: Int, f: impl FnOnce(&mut T) -> O) -> O {
       let i = i.try_into_usize().unwrap();
       self.0.mutate(|v| f(&mut v[i]))
   }
   ```
   where `GcCow::mutate` (`libspecr/src/gc/gccow.rs:42-48`) is:
   ```rust
   pub fn mutate<O>(&mut self, f: impl FnOnce(&mut T) -> O) -> O {
       let mut v = self.extract();
       let ret = f(&mut v);
       *self = GcCow::new(v);
       ret
   }
   ```
   Because `O` is completely unconstrained (`O = Result<(), TerminationInfo>` when called as `self.children.mutate_at(idx, |child| ...)?`), `GcCow::mutate` unconditionally allocates a new GC cell containing the mutated `v` and assigns `*self = GcCow::new(v)` **before** returning `ret` to the `?` operator.
3. **Mechanized verification of nested `GcCow` mutation (`HelperValueHeap.lean`, `HelperNestedMutation.lean`, `HelperValueControls.lean`)**:
   - [`support/HelperValueHeap.lean`](support/HelperValueHeap.lean) and [`support/HelperNestedMutation.lean`](support/HelperNestedMutation.lean) model a two-level copy-on-write heap (`parent` -> `leaf`) where `mutateParent` and `mutateLeaf` allocate fresh handles and return an opaque callback output `α` (instantiated to `Except ε β`).
   - Theorems `nested_exact`, `nested_observations`, `nested_error_exact`, and `nested_error_retains` ([`HelperNestedMutation.lean:145-209`](support/HelperNestedMutation.lean#L145-L209)) prove that:
     1. Old handles (`root` and all prior `RootImage` / `LeafImage` aliases) retain their original pure values (`readParent actual.heap root = some value`), so any outer caller that discards the mutated receiver handle on `Err` observes pure value rollback.
     2. The mutated receiver handle (`actual.receiver = heap.next + 1`) and the two newly allocated heap cells (`heap.next` and `heap.next + 1`) are **installed even when the callback returns `.error error`** (`rollback_discriminator` and `overwrite_discriminator` in [`HelperValueControls.lean:107-140`](support/HelperValueControls.lean#L107-L140)).
4. **Packaging drift between crates.io `libspecr 0.1.41` and git `15200eb` (`helper-value-sources.json`)**:
   Comparing `libspecr-0.1.41.crate` (SHA-256 `a3c0c46f39513f6c4b533ec6bea7d623f6761fd0a610b1152db7f2e4dd385a61`) against `minirust/specr` git commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348` (which `.cargo_vcs_info.json` claims to package) shows that six source files differ (`gc/gccow.rs`, `gc/obj.rs`, `list/mod.rs`, `map/mod.rs`, `set/mod.rs`, `Cargo.toml`): the git commit derives `Copy` (in addition to `Clone`) on `GcCow<T>`, `Obj<T>`, `List<T>`, `Map<K, V>`, and `Set<T>` and marks `Obj<T>` as `#[repr(transparent)]`, whereas the published `0.1.41` crate only derives `Clone`. Because MiniRust specs rely on implicit `Copy` semantics for `List` and `Map` values (e.g., `let mut alloc = self.allocations[id];`), MiniRust requires the git revision `15200eb5e676e2ee91f43bd79e674f8fc32e5348` rather than the crates.io `0.1.41` tarball.

### 3. Coupled vs. Factored `TreeBorrowsMemory` Correspondence Across All Operations and Prefixes

**Basis**: `execution` and `derived`

Across the 88 `Tree*.lean` modules in [`support/`](support/), the coupled reference model (`TreeReference.Node` inside `TreeMemory.State`) and the factored model (`TreeFactored.State` separating `Topology` from path-indexed `Store : Path → Entry` inside `TreeFactoredMemory.State`) are proven equivalent across 9 progressive operational layers:

1. **Node & tree-level correspondence (`TreePermissions` .. `TreeUnprotectWidths`, 22 modules)**:
   - `TreeCorrespondence.reify` ([`TreeCorrespondence.lean:37-39`](support/TreeCorrespondence.lean#L37-L39)) reconstructs a recursive `TreeReference.Node` from `(topology, store)` while ignoring unrepresented store paths (`overwrite_absent_preserves_reify`, [`TreeCorrespondence.lean:103-113`](support/TreeCorrespondence.lean#L103-L113)).
   - `TreeAgreement.access_agrees` and `TreeReleaseAgreement.releaseTraverse_agrees` prove that recursive node access and Stage-2 protector traversal commute with `reify`, and `TreeUnprotectAgreement.unprotectAt_agrees` proves that Stage-1 targeted `unprotect` conversion commutes with `reify` on all valid and invalid paths.
2. **Memory-level composition and invariant preservation (`TreeFactoredMemory` .. `TreeGeometryControls`, 13 modules)**:
   - `TreeMemoryAgreement`, `TreeMemoryOperations`, and `TreeMemoryReleaseAgreement` lift node agreement to `TreeMemory.State` and `TreeFactoredMemory.State` across `load`, `store`, `dereferenceable`, `free` (including the `contains_active_strong_protector` UB check before `BasicMemory::deallocate`), `exit`, and `release`.
   - `TreeMemoryDomain.WellSized` and `TreeMemoryPreservation` prove that per-allocation permission-array widths (`arraysSized node alloc.size`) and tree domains are preserved across all memory operations.
3. **Client prefix correspondence and canonical encoding (`TreeMemoryClient` .. `TreeEncodedPrefixes`, 9 modules)**:
   - `TreeMemoryPrefixes` and `TreeMemoryPrefixAgreement` prove all-prefix reachability and `NoUB` equivalence (`prefix_iff`, `noUB_iff`) for reactive client plans over `TreeMemory` and `TreeFactoredMemory`.
   - `TreeEncoding`, `TreeMemoryEncoding`, `TreeEncodingNormalization`, and `TreeEncodedPrefixes` define `encode : TreeReference.Node → TreeFactored.State`, prove `reify (encode node) = node`, and establish canonical normal forms for factored stores.
4. **Live reborrowing and child-node insertion (`TreeGraft` .. `TreeReborrowHistory`, 29 modules)**:
   - `TreeGraft` and `TreeFactoredReborrow` model `TreeBorrowsMemory::reborrow` (`spec/mem/tree_borrows/memory.md:133-199`): validating dereferenceability over the reborrowed span, reading parent path `p.path`, performing the initial child access over the reborrowed offset range, constructing the new child node (with `Protected::Strong` or `Protected::Weak` when `is_protected` is set, `Protected::No` otherwise, `DefaultPermission` inside the reborrowed range and `Unprotected(Disabled)` outside), appending the child at index `children.len()`, and registering the new provenance in `current_frame.protectors` when protected.
   - `TreeReborrowAgreement`, `TreeReborrowClient`, `TreeReborrowPrefixes`, and `TreeReborrowClientCoverage` prove exact single-step and all-prefix correspondence for dynamic client programs that chain arbitrary `reborrow` replies into subsequent `load`, `store`, `release`, and nested `reborrow` commands.
5. **Allocation root birth and demonic base-address choice (`TreeAllocation` .. `TreeChoiceCoverage`, 13 modules)**:
   - `TreeAllocation` and `TreeAllocationFreshness` model `TreeBorrowsMemory::allocate` (`spec/mem/tree_borrows/memory.md:62-84`), which delegates to `BasicMemory::allocate` and initializes the fresh allocation's borrow tree to a single unprotected root node (`Path::new()`) with `[Permission::Unprotected(UnprotectedPermission::Unique); size]`.
   - `TreeAllocationChoices`, `TreeChoiceClient`, `TreeChoicePrefixes`, and `TreeChoiceCoverage` lift demonic allocator base-address non-determinism (`candidate : Nat`) and pointer-reply continuation passing to the full coupled and factored `TreeBorrowsMemory` machines, proving exact all-prefix and `NoUB` correspondence (`TreeChoicePrefixes`).
6. **Ordered `end_call` multi-protector release (`TreeEndCall` .. `TreeEndCallFailureControls`, 4 modules)**:
   - `TreeEndCall` ([`TreeEndCall.lean:35-153`](support/TreeEndCall.lean#L35-L153)) models `TreeBorrowsMemory::end_call` (`spec/mem/tree_borrows/memory.md:92-99`), which iterates in order over `extra.protectors : List<Provenance>` and invokes `self.release_protector(p)?`.
   - Theorem `endCall_agrees` ([`TreeEndCall.lean:148-152`](support/TreeEndCall.lean#L148-L152)) proves that under the sole structural precondition `WellSized memory`, coupled `rEndCall` and factored `fEndCall` agree on status, UB/unsupported diagnostics, and complete reified memory state across arbitrary protector lists (including duplicate registrations, dead allocations, and mid-list UB aborts where earlier releases in the list remain committed while later registrations are skipped, verified in `TreeEndCallProperties`, `TreeEndCallConstructed`, and `TreeEndCallFailureControls`).

## Boundaries

- **Known not to apply**:
  - Single-pass protector release (combining `unprotect()` and implicit access emission in a single top-down walk, or visiting the released node's own subtree during implicit access emission) disagrees with `spec/mem/tree_borrows/{memory.md,tree.md}` on protected descendant nodes (`TreeMemoryControls.lean`).
  - Treating `Some(path)` as `Foreign` and `None` as `Local` (as written in the prose comment at `tree.md:62-66`) disagrees with the executable equations at `tree.md:71-106`.
  - Assuming `GcCow::mutate` rolls back physical heap allocations when its closure returns `Err(Error)` is false (`HelperValueControls.rollback_discriminator`); rollback holds only at the level of pure value observations through unmutated caller handles (`HelperNestedMutation.nested_error_retains`).
- **Not examined in this package**:
  - Integer-to-pointer cast exposure and prediction (`expose` / `predict` in `spec/mem/intptrcast.md`), which `TreeBorrowsMemory` leaves as `unimplemented!()` in `spec/mem/tree_borrows/memory.md:122-130`.
  - Concurrent atomic memory operations and data-race detection (`spec/mem/concurrent.md`).
- **Unsupported / out-of-contract representations**:
  - Out-of-bounds child path indices (`invalidPath`), mismatched permission array lengths (`arrayLength`), releasing an unprotected node (`unprotectUnprotected`), or negative `specr::Int` indices are classified as `.unsupported` structural faults distinct from language-level `.ub` (`TreeReference.Structural`, [`TreeReference.lean:41-54`](support/TreeReference.lean#L41-L54)) and are proven unreachable on `WellSized` states with minted provenances (`TreeMemoryDomain`, `TreeAllocationFreshness`, `TreeReborrowDomain`).
- **Unknown**:
  - Whether upstream MiniRust will update the prose comment at `spec/mem/tree_borrows/tree.md:62-66` to match the executable `Some`/`None` convention, or publish a newer `libspecr` crate version on crates.io syncing commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348`.

## Evidence

All 93 Lean modules (88 `Tree*.lean` modules, 3 `Helper*.lean` modules, and 2 shared `BasicMemory` modules `MiniRustReference.lean` and `ReferenceInvariants.lean`) and the fresh execution ledger are archived in [`support/`](support/):

- Execution ledger: [`support/lean-verification-results.json`](support/lean-verification-results.json) (93 modules, 1,026 audited theorems, recorded `2026-10-24` on `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`).

| Module | Support File | Source SHA-256 | Flags (`x86_64-linux`) | Wall (s) | Audited Theorems |
| :--- | :--- | :--- | :--- | ---: | ---: |
| `AnnealResearch.TreePermissions` | [`support/TreePermissions.lean`](support/TreePermissions.lean) | `fd0ca0946219fabc2f3116d602e2d275e4418050cb228a38d4680700dc041836` | `-j1 -M1024` | 0.9418 | 12 |
| `AnnealResearch.TreeReference` | [`support/TreeReference.lean`](support/TreeReference.lean) | `3b42ee60259f68a7c08775dd320ff6e3827d5e7e568653e11b4dbed79efd7636` | `-j1 -M1024` | 1.6234 | 20 |
| `AnnealResearch.TreeFactored` | [`support/TreeFactored.lean`](support/TreeFactored.lean) | `0f531e1b010ef7be08fa3173159e59ea7d7a139e33e055d0169ba22731bae975` | `-j1 -M1024` | 0.9255 | 14 |
| `AnnealResearch.TreeCorrespondence` | [`support/TreeCorrespondence.lean`](support/TreeCorrespondence.lean) | `27a5cc0aa1dfa8aaddabe53c8e4784d6d2e07c6a3dee9eabd763f4fda145b0d8` | `-j1 -M1024` | 0.7241 | 13 |
| `AnnealResearch.TreeQueries` | [`support/TreeQueries.lean`](support/TreeQueries.lean) | `ecb860083337ac2d17a59c9933ebe61c57205b047c1187b14be216e091775b45` | `-j1 -M768` | 0.5987 | 17 |
| `AnnealResearch.TreeOperations` | [`support/TreeOperations.lean`](support/TreeOperations.lean) | `13087d6f9a43eb462a7ebcee2b5dce9bff883d2f05e99ccbc4a0fb846b882029` | `-j1 -M1024` | 0.9517 | 13 |
| `AnnealResearch.TreeTraversal` | [`support/TreeTraversal.lean`](support/TreeTraversal.lean) | `c433d399e98625d370ea875a1b76240575fbe4861676c3aa962b9518af7f12c0` | `-j1 -M1024` | 0.7301 | 19 |
| `AnnealResearch.TreeAgreement` | [`support/TreeAgreement.lean`](support/TreeAgreement.lean) | `7fbd6a228bd085772bdbc34fe558bdeded68ac2bca00522a2ef3739e7caaca7a` | `-j1 -M1024` | 0.6204 | 8 |
| `AnnealResearch.TreeReleaseAgreement` | [`support/TreeReleaseAgreement.lean`](support/TreeReleaseAgreement.lean) | `9f7eddf0f48113b9c44ef665184b2bf0413f80741ad52a6e0f91a79144c3a3e5` | `-j1 -M1024` | 0.5541 | 5 |
| `AnnealResearch.MiniRustReference` | [`support/MiniRustReference.lean`](support/MiniRustReference.lean) | `f2974b04a15b378f930719a0ad8943e3313abccbabf108b6ad0d24a0478fc778` | `-j1 -M1024` | 0.8883 | 6 |
| `AnnealResearch.TreeMemory` | [`support/TreeMemory.lean`](support/TreeMemory.lean) | `605c2afead08cfce80995e75277b49e39a1fd566a86269cc53fed6e24fb61b14` | `-j1 -M1024` | 0.8538 | 2 |
| `AnnealResearch.TreeMemoryControls` | [`support/TreeMemoryControls.lean`](support/TreeMemoryControls.lean) | `1854d636ad5370d6b3ac1fe329b4a8fc8e0868e45baf74115b96196ca0113d2a` | `-j1 -M1024` | 2.3038 | 21 |
| `AnnealResearch.TreeExceptions` | [`support/TreeExceptions.lean`](support/TreeExceptions.lean) | `cc15661f33adf1216eb9def69111d93cf963a1a8dc477c8907aa4b07f55da8ca` | `-j1 -M1024` | 1.0754 | 22 |
| `AnnealResearch.TreeExit` | [`support/TreeExit.lean`](support/TreeExit.lean) | `21ead38eb2b2777470cd947bf11d9ff2672a0806c59911034787118231d6eef6` | `-j1 -M1024` | 0.7100 | 12 |
| `AnnealResearch.TreePairing` | [`support/TreePairing.lean`](support/TreePairing.lean) | `da5ef936ce9068fe9a1d349bdd37656c2da2ce4f3256f0c50484fdb70e1a59aa` | `-j1 -M1024` | 0.6423 | 22 |
| `AnnealResearch.TreeLookup` | [`support/TreeLookup.lean`](support/TreeLookup.lean) | `0c16439b234ab9039e12e6b4dda991d6b40c28197e20d8780f64551a922daf9e` | `-j1 -M1024` | 0.5914 | 10 |
| `AnnealResearch.TreeNodeUpdate` | [`support/TreeNodeUpdate.lean`](support/TreeNodeUpdate.lean) | `92e5ed1c71c81aaa8d34c322d80e724e897bb3150eefb778b14644e28edaaf30` | `-j1 -M768` | 0.5054 | 7 |
| `AnnealResearch.TreeUnprotect` | [`support/TreeUnprotect.lean`](support/TreeUnprotect.lean) | `340dc80852111f7d0416d31328ba03fa55da47609a459b0b0ba3efd1ec3fb709` | `-j1 -M768` | 0.5396 | 5 |
| `AnnealResearch.TreeValidated` | [`support/TreeValidated.lean`](support/TreeValidated.lean) | `18cd6fa7e1c1d8898578c2a58917a62ed2a6daeeceb7899d328e72a8184b8e17` | `-j1 -M768` | 0.5087 | 9 |
| `AnnealResearch.TreeNodePathUpdate` | [`support/TreeNodePathUpdate.lean`](support/TreeNodePathUpdate.lean) | `85794c70ac3f8cb2bb4904907eb9a23e9cb8b9641e439069fc8aa221a6de646e` | `-j1 -M1024` | 0.6120 | 7 |
| `AnnealResearch.TreeUnprotectAgreement` | [`support/TreeUnprotectAgreement.lean`](support/TreeUnprotectAgreement.lean) | `a6789a76e5b9ec674dec2c68210ed07b84715373d7f7dfc927d2eeb1e44c0fd7` | `-j1 -M768` | 0.5059 | 7 |
| `AnnealResearch.TreeUnprotectTotal` | [`support/TreeUnprotectTotal.lean`](support/TreeUnprotectTotal.lean) | `faff83d50fe6d4c2c4775eff524b41ba756f8d924ce5af510b7413d3936367fd` | `-j1 -M768` | 0.5035 | 6 |
| `AnnealResearch.TreeUnprotectWidths` | [`support/TreeUnprotectWidths.lean`](support/TreeUnprotectWidths.lean) | `61836bf19d6fa8b33f345605d8dad7b58c7381fc31dfb94cecdc35c88ab9a17c` | `-j1 -M1024` | 0.5618 | 9 |
| `AnnealResearch.TreeFactoredMemory` | [`support/TreeFactoredMemory.lean`](support/TreeFactoredMemory.lean) | `f8d14056c02f03473f9f64b9e2245cb405ad474f432481d558c86ccc49f6da65` | `-j1 -M1024` | 0.5829 | 4 |
| `AnnealResearch.TreeMemoryAgreement` | [`support/TreeMemoryAgreement.lean`](support/TreeMemoryAgreement.lean) | `8fb0588fff0dcf7ccb4ac2fcdfab1fcd9781466359922e82210bdd5f5d9a6f2f` | `-j1 -M1024` | 0.4787 | 7 |
| `AnnealResearch.TreeMemoryOperations` | [`support/TreeMemoryOperations.lean`](support/TreeMemoryOperations.lean) | `13cb805d6ae2e1c01534c582a7c18a528dc75d29a1027de2e7c5a01a6033b952` | `-j1 -M1024` | 0.7793 | 5 |
| `AnnealResearch.TreeMemoryReleaseAgreement` | [`support/TreeMemoryReleaseAgreement.lean`](support/TreeMemoryReleaseAgreement.lean) | `842e8cc70187094e49d72e238b5a2375ec0cb989438d8e3d3942778b1dd198d6` | `-j1 -M1024` | 0.5001 | 2 |
| `AnnealResearch.TreeMemoryPairing` | [`support/TreeMemoryPairing.lean`](support/TreeMemoryPairing.lean) | `43c71004578f8dbe8126e849ff57cd95a2fa1ab50e664a070f66ad1cf1078952` | `-j1 -M1024` | 0.6114 | 11 |
| `AnnealResearch.TreeMemoryCompositionControls` | [`support/TreeMemoryCompositionControls.lean`](support/TreeMemoryCompositionControls.lean) | `6b5c36283c1ba725fc12dfadeb71760ecd7d616dc7d1879014fbf248f096601d` | `-j1 -M1024` | 0.5778 | 18 |
| `AnnealResearch.TreeRawGeometry` | [`support/TreeRawGeometry.lean`](support/TreeRawGeometry.lean) | `395c520c39b98c04c58226023e174d6c4d59a31a7d375ec8d0827a443add90d8` | `-j1 -M768` | 0.7979 | 11 |
| `AnnealResearch.TreeTraversalGeometry` | [`support/TreeTraversalGeometry.lean`](support/TreeTraversalGeometry.lean) | `e6e252ae87ce410c5053913482682c8047e31251938304d2455f6803b2bece69` | `-j1 -M768` | 0.4874 | 14 |
| `AnnealResearch.TreeTraversalGeometryPublic` | [`support/TreeTraversalGeometryPublic.lean`](support/TreeTraversalGeometryPublic.lean) | `39759dc186bdc3d8c0ad04359acddc72597b54618f6142bf7d4de7c9e529bb33` | `-j1 -M1024` | 0.4914 | 10 |
| `AnnealResearch.TreeMemoryDomain` | [`support/TreeMemoryDomain.lean`](support/TreeMemoryDomain.lean) | `5677c68f5ea5ca8052a5fa4c5a71eeafe6c6d9e15a4070e496b65ddd20645d11` | `-j1 -M1024` | 0.4380 | 7 |
| `AnnealResearch.TreeMemoryPreservation` | [`support/TreeMemoryPreservation.lean`](support/TreeMemoryPreservation.lean) | `7657410407635941ccfb6c4445f83e0cad274ebf0ace3b002d3d266a38b54893` | `-j1 -M1024` | 0.6216 | 5 |
| `AnnealResearch.TreeGeometryControls` | [`support/TreeGeometryControls.lean`](support/TreeGeometryControls.lean) | `ce81fdc87df696032e57a6e103069dcbeea112c8e9383398363bc17978552577` | `-j1 -M1024` | 0.5591 | 13 |
| `AnnealResearch.TreeMemoryClient` | [`support/TreeMemoryClient.lean`](support/TreeMemoryClient.lean) | `5ae67ba193ab01277944865ab61dc96e17d26a90837499e2479a3c1c6ebce71c` | `-j1 -M1024` | 0.7468 | 15 |
| `AnnealResearch.TreeMemoryPrefixes` | [`support/TreeMemoryPrefixes.lean`](support/TreeMemoryPrefixes.lean) | `636399dab96980acc383cb5a602fcdda0d041177827ee3efcad8dad70f26e840` | `-j1 -M1024` | 0.5230 | 6 |
| `AnnealResearch.TreeMemoryPrefixAgreement` | [`support/TreeMemoryPrefixAgreement.lean`](support/TreeMemoryPrefixAgreement.lean) | `c60007d252443ce509630d37cf9b33c6ee650a749866a0bd1da0fe6a54e429b8` | `-j1 -M1024` | 0.4600 | 7 |
| `AnnealResearch.TreeMemoryPrefixControls` | [`support/TreeMemoryPrefixControls.lean`](support/TreeMemoryPrefixControls.lean) | `41614f3bc53c4f5a5f591a29092642f2557bec06cd716dd003cf958392788cba` | `-j1 -M1024` | 0.5153 | 12 |
| `AnnealResearch.TreeEncoding` | [`support/TreeEncoding.lean`](support/TreeEncoding.lean) | `8cb251c74c439fa792b672b071735dac4ba6fdbaef3fdaba7394bb28ba21b826` | `-j1 -M1024` | 0.5571 | 8 |
| `AnnealResearch.TreeMemoryEncoding` | [`support/TreeMemoryEncoding.lean`](support/TreeMemoryEncoding.lean) | `ba7c0a542855702f6a63ab5727aad68e8689e57c4c85e5b8e3e48ed44afe3168` | `-j1 -M768` | 0.4369 | 7 |
| `AnnealResearch.TreeEncodingNormalization` | [`support/TreeEncodingNormalization.lean`](support/TreeEncodingNormalization.lean) | `b0e21992e27a0c9a3519b015571caeede2806b3785a5fab880f3b353d9144a52` | `-j1 -M768` | 0.4270 | 9 |
| `AnnealResearch.TreeEncodingControls` | [`support/TreeEncodingControls.lean`](support/TreeEncodingControls.lean) | `52bec9c84c4da2d66f7a165c00a8fa00a7d6543e855843d088caf8495fd9e941` | `-j1 -M1024` | 0.5008 | 14 |
| `AnnealResearch.TreeEncodedPrefixes` | [`support/TreeEncodedPrefixes.lean`](support/TreeEncodedPrefixes.lean) | `7c69ecb02c7b361390dff56581c2ac32ac8efb74a692ccfd58a6ee0236415288` | `-j1 -M1024` | 0.4420 | 6 |
| `AnnealResearch.TreeGraft` | [`support/TreeGraft.lean`](support/TreeGraft.lean) | `e9b6fe34e6621ef5e98f182022e093c918075ef82de57ce097e0e82d681190a2` | `-j1 -M1024` | 0.6615 | 13 |
| `AnnealResearch.TreeKindPreservation` | [`support/TreeKindPreservation.lean`](support/TreeKindPreservation.lean) | `16b5f73fea91b9666e2f7c95ca9d8f15e6f8b3573eb00ae2a3c3d56cf67a5b62` | `-j1 -M768` | 0.5103 | 5 |
| `AnnealResearch.TreeGraftPaths` | [`support/TreeGraftPaths.lean`](support/TreeGraftPaths.lean) | `f39b04ca201445e84b87a865a6b7dc5ce1ffb7956ff5baa3fa09514a219dd3df` | `-j1 -M1024` | 0.6349 | 5 |
| `AnnealResearch.TreeKindAccess` | [`support/TreeKindAccess.lean`](support/TreeKindAccess.lean) | `87170478878caf8e4512b7980edca29c1e6f074dfad7956ad1e6fa435d5427ef` | `-j1 -M768` | 0.5599 | 5 |
| `AnnealResearch.TreeReleaseKinds` | [`support/TreeReleaseKinds.lean`](support/TreeReleaseKinds.lean) | `3e90947b7f48875b2e1c949930b3c3743cb2b01144683c7f8a49c620564f642c` | `-j1 -M1024` | 0.8807 | 7 |
| `AnnealResearch.TreeInsertionAgreement` | [`support/TreeInsertionAgreement.lean`](support/TreeInsertionAgreement.lean) | `7737778067b362f805397bc761873cbb07aeae07be3189b6506583f1f9dc0931` | `-j1 -M1024` | 0.5858 | 8 |
| `AnnealResearch.TreeLiveKinds` | [`support/TreeLiveKinds.lean`](support/TreeLiveKinds.lean) | `2363fcf97ebea329fb6bbbd1085e56f9e9207245af233ab6a9d05502e637be73` | `-j1 -M768` | 0.5004 | 12 |
| `AnnealResearch.TreeUnprotectKinds` | [`support/TreeUnprotectKinds.lean`](support/TreeUnprotectKinds.lean) | `fb9670f7576ffa787a44d4f6d5c0ab0245a98ba786c7da424501ad16cd583da3` | `-j1 -M1024` | 0.6852 | 9 |
| `AnnealResearch.TreeInsertionWidths` | [`support/TreeInsertionWidths.lean`](support/TreeInsertionWidths.lean) | `255bf5f3be064c5e9b5757e41484363a79d4efd5eaa2e798962655c85cb650c4` | `-j1 -M1024` | 0.5111 | 10 |
| `AnnealResearch.TreeLiveKindControls` | [`support/TreeLiveKindControls.lean`](support/TreeLiveKindControls.lean) | `3cdec98eabd72c66eb52d6ec3b94f9dbf45c6a2d82bf1708b5bc45bff0864f7e` | `-j1 -M1024` | 0.5733 | 11 |
| `AnnealResearch.TreeLiveMemory` | [`support/TreeLiveMemory.lean`](support/TreeLiveMemory.lean) | `9df5f625d6fe24de77c7f8f3b5402967424ed77f2c0e84b4893fb8350d7ecb37` | `-j1 -M1024` | 0.5743 | 6 |
| `AnnealResearch.TreeInitialAgreement` | [`support/TreeInitialAgreement.lean`](support/TreeInitialAgreement.lean) | `ae58d350410297257f76c75e266f9a7a8b9289cf851980eb01048cef1dee5f15` | `-j1 -M1024` | 0.5502 | 8 |
| `AnnealResearch.TreeLiveRelease` | [`support/TreeLiveRelease.lean`](support/TreeLiveRelease.lean) | `97ac7641bf2a1d8f787a2ac28518583a7a318a92a69a007dcfedb28ac3c9a9c7` | `-j1 -M768` | 0.4293 | 6 |
| `AnnealResearch.TreeReleaseKindControls` | [`support/TreeReleaseKindControls.lean`](support/TreeReleaseKindControls.lean) | `edcf792f35dff8d1f6203934a7783304b1124e4ef91397334643e36cf4bd2686` | `-j1 -M1024` | 0.5317 | 6 |
| `AnnealResearch.TreeFactoredReborrow` | [`support/TreeFactoredReborrow.lean`](support/TreeFactoredReborrow.lean) | `7d5019f4d05e8467fefd8ce281537f13bf0d23a25aa58754743d6d69de666469` | `-j1 -M1024` | 0.5196 | 8 |
| `AnnealResearch.TreeInsertionControls` | [`support/TreeInsertionControls.lean`](support/TreeInsertionControls.lean) | `3f4be4ca02566f21842c7aabf2714bf919efedfefc3d8fd7d654e29f83d8d089` | `-j1 -M1024` | 0.5780 | 8 |
| `AnnealResearch.TreeLivePrefixes` | [`support/TreeLivePrefixes.lean`](support/TreeLivePrefixes.lean) | `11dca9ab3f75edc4e98de21de3a2fb4dc5d6517ca9083ab2179d7a8d56242cae` | `-j1 -M1024` | 0.4855 | 6 |
| `AnnealResearch.TreeReborrowKinds` | [`support/TreeReborrowKinds.lean`](support/TreeReborrowKinds.lean) | `4d27462d3b6501867e1908db683f8d647409c5eb41fd1e7fdd192b19ef44426e` | `-j1 -M1024` | 0.8667 | 8 |
| `AnnealResearch.TreeReborrowAgreement` | [`support/TreeReborrowAgreement.lean`](support/TreeReborrowAgreement.lean) | `7f428e845b1d194264b0212995b734cfd2c0e1b17b693ad2e08064133b8f63cf` | `-j1 -M1024` | 0.7325 | 3 |
| `AnnealResearch.TreeReborrowDomain` | [`support/TreeReborrowDomain.lean`](support/TreeReborrowDomain.lean) | `a041def444a2ee924abae66933f41ad53d55aac1a1f79f5d3b7292bc12d67796` | `-j1 -M1024` | 0.6334 | 6 |
| `AnnealResearch.TreeReborrowStateControls` | [`support/TreeReborrowStateControls.lean`](support/TreeReborrowStateControls.lean) | `8125b11f92635ede08473b9c1e64e7aa72dc8232f1b6a4eaacabff7340e74fd3` | `-j1 -M1024` | 0.5889 | 5 |
| `AnnealResearch.TreeLiveTransfer` | [`support/TreeLiveTransfer.lean`](support/TreeLiveTransfer.lean) | `e65d594829f0bce748fad0cd93d473fae99f19c260ba39ffb6eb19c8aed322b3` | `-j1 -M1024` | 0.4566 | 9 |
| `AnnealResearch.TreeReborrowPairedControls` | [`support/TreeReborrowPairedControls.lean`](support/TreeReborrowPairedControls.lean) | `73e1a2d3231dbb04d9cb0892617b344ef1f9b708332ceacb3ecece34ecd5db59` | `-j1 -M1024` | 0.4475 | 6 |
| `AnnealResearch.TreeReborrowClient` | [`support/TreeReborrowClient.lean`](support/TreeReborrowClient.lean) | `8ca2ad3eaba824803e4a03bd82bff0b08fda22124d5bc0fb3c229c8db85a57a5` | `-j1 -M1024` | 0.5991 | 14 |
| `AnnealResearch.TreeReborrowLive` | [`support/TreeReborrowLive.lean`](support/TreeReborrowLive.lean) | `1b76d8bc7334bad867b9d7499afae8f03af8260e3ae529b1bdd7979bbbc065b1` | `-j1 -M1024` | 0.4823 | 4 |
| `AnnealResearch.TreeReborrowPrefixes` | [`support/TreeReborrowPrefixes.lean`](support/TreeReborrowPrefixes.lean) | `a8b874e21e661136d12b34f648df768f90ca521b73760a7888a5c3028cc9ca18` | `-j1 -M1024` | 0.5372 | 10 |
| `AnnealResearch.TreeReborrowClientControls` | [`support/TreeReborrowClientControls.lean`](support/TreeReborrowClientControls.lean) | `bae0cf0525664556050b3d170666abed3484d4f744fe2cdd32ff9fbf590cbbb1` | `-j1 -M1024` | 0.6356 | 20 |
| `AnnealResearch.TreeReborrowClientCoverage` | [`support/TreeReborrowClientCoverage.lean`](support/TreeReborrowClientCoverage.lean) | `07c1e1fa1229631b19c57908e5f391e6a4059398b0c7e13c133acd6917910a83` | `-j1 -M1024` | 0.3959 | 6 |
| `AnnealResearch.TreeReborrowHistory` | [`support/TreeReborrowHistory.lean`](support/TreeReborrowHistory.lean) | `a676d67adbba067449c7e0d143896174b6c1549b074090f6ff885aed0f066f11` | `-j1 -M1024` | 0.7909 | 17 |
| `AnnealResearch.TreeAllocation` | [`support/TreeAllocation.lean`](support/TreeAllocation.lean) | `123cbeadd6c5d328f0072f7acdeffb155235f908885d33cc2d76488f310c41e3` | `-j1 -M1024` | 0.5437 | 12 |
| `AnnealResearch.ReferenceInvariants` | [`support/ReferenceInvariants.lean`](support/ReferenceInvariants.lean) | `18e7d810df82fe6620fc32bd6a69ad2b9b71b768c1d1baaeeba78086169741ec` | `-j1 -M1024` | 1.2438 | 9 |
| `AnnealResearch.TreeAllocationAdmissionControls` | [`support/TreeAllocationAdmissionControls.lean`](support/TreeAllocationAdmissionControls.lean) | `4eb67ea41c29287d1ab4ba906973a84d0c138a486208ed0585dec424a62be568` | `-j1 -M1024` | 0.5850 | 25 |
| `AnnealResearch.TreeAllocationDomain` | [`support/TreeAllocationDomain.lean`](support/TreeAllocationDomain.lean) | `f986279d531259805c651986cb59bf301e21c858a20ed4513e3f62ba58ff30c3` | `-j1 -M1024` | 0.4884 | 8 |
| `AnnealResearch.TreeAllocationFreshness` | [`support/TreeAllocationFreshness.lean`](support/TreeAllocationFreshness.lean) | `7574b34bcf550929108efab4226b3976920a1d17be29281f2b4006fb34c81b04` | `-j1 -M1024` | 0.5807 | 17 |
| `AnnealResearch.TreeAllocationMutationControls` | [`support/TreeAllocationMutationControls.lean`](support/TreeAllocationMutationControls.lean) | `22e79bf418cc691356b96b80d2b377bf2f77086f332d130df02db1244314eb85` | `-j1 -M1024` | 0.6512 | 11 |
| `AnnealResearch.TreeAllocationChoices` | [`support/TreeAllocationChoices.lean`](support/TreeAllocationChoices.lean) | `4c0d495c0356fb7348086590b051975eb5d05abcb7f1e9538bc2c270a5568848` | `-j1 -M1024` | 0.4745 | 12 |
| `AnnealResearch.TreeAllocationControls` | [`support/TreeAllocationControls.lean`](support/TreeAllocationControls.lean) | `30994efb9b161e8a0d0116c76a899703a4b23cc0a7efdd30a1fee08e0973d8d2` | `-j1 -M1024` | 0.8037 | 35 |
| `AnnealResearch.TreeChoiceClient` | [`support/TreeChoiceClient.lean`](support/TreeChoiceClient.lean) | `76eb1df42146559dd41eb4df702e8d3a3119f3c5805968bddedb12a072ebfbb8` | `-j1 -M1024` | 0.6845 | 22 |
| `AnnealResearch.TreeChoicePrefixes` | [`support/TreeChoicePrefixes.lean`](support/TreeChoicePrefixes.lean) | `39082bc4d00aab18f50291a777f08808e54401948d02eca902f6220c23de6d66` | `-j1 -M1024` | 0.4669 | 9 |
| `AnnealResearch.TreeChoiceLive` | [`support/TreeChoiceLive.lean`](support/TreeChoiceLive.lean) | `33e8f55cafa8e6853f411558c474199bdca39abe61aca45c8dc895e6132f2996` | `-j1 -M1024` | 0.4470 | 5 |
| `AnnealResearch.TreeChoiceControls` | [`support/TreeChoiceControls.lean`](support/TreeChoiceControls.lean) | `fb6225d37abc5f0afdc6c7afafa615a052465d8b833efdb7ab888f5c4557a437` | `-j1 -M1024` | 0.7893 | 32 |
| `AnnealResearch.TreeChoiceCoverage` | [`support/TreeChoiceCoverage.lean`](support/TreeChoiceCoverage.lean) | `c9f5754ee9d835dd6dcf89f3351ea3a3e10a5f5c30ac484759899e9715a9bc5a` | `-j1 -M1024` | 0.4188 | 6 |
| `AnnealResearch.TreeEndCall` | [`support/TreeEndCall.lean`](support/TreeEndCall.lean) | `5f4def8b8ad70572fd6ac3503606fdb6b3a18a2069903b6a8bcca6470d38854c` | `-j1 -M1024` | 0.7278 | 16 |
| `AnnealResearch.TreeEndCallProperties` | [`support/TreeEndCallProperties.lean`](support/TreeEndCallProperties.lean) | `4d855f5fc0afe224d28a701457d4d0a95313fd48428da2c73406a43bb5b94f46` | `-j1 -M1024` | 0.5272 | 16 |
| `AnnealResearch.TreeEndCallConstructed` | [`support/TreeEndCallConstructed.lean`](support/TreeEndCallConstructed.lean) | `6c1e7f06e86e3b26cda98751564c01fc9a289bceebeda304877d9b1e10d9f3e6` | `-j1 -M1024` | 1.0662 | 27 |
| `AnnealResearch.TreeEndCallFailureControls` | [`support/TreeEndCallFailureControls.lean`](support/TreeEndCallFailureControls.lean) | `b04d3eed1d3cbcc6f8ebb8de60edaf9bc9e74a335549502cdad6f0dbedcc5980` | `-j1 -M1024` | 0.9226 | 23 |
| `AnnealResearch.HelperValueHeap` | [`support/HelperValueHeap.lean`](support/HelperValueHeap.lean) | `674c33a9b362f0c8bb1fbfc5c99de3ff3ab96452249f006164056a373291521d` | `-j1 -M768` | 0.5890 | 14 |
| `AnnealResearch.HelperNestedMutation` | [`support/HelperNestedMutation.lean`](support/HelperNestedMutation.lean) | `4f7b070deca233320346fa37015129f52de1c82420b3305d68f849a54839b102` | `-j1 -M768` | 0.5805 | 16 |
| `AnnealResearch.HelperValueControls` | [`support/HelperValueControls.lean`](support/HelperValueControls.lean) | `67bd81860edd448da6d706003d53ff52e3dcd0346e846c659ac341ce6c78aa8b` | `-j1 -M768` | 0.6729 | 13 |

## Revalidation

To re-check all 93 Lean modules in topological order from the self-contained [`support/`](support/) directory using Lean `v4.34.1`:

```bash
python3 - <<'EOF'
import json, os, subprocess, tempfile

pkg_dir = "reports/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence"
support_dir = os.path.join(pkg_dir, "support")
with open(os.path.join(support_dir, "lean-verification-results.json")) as f:
    ledger = json.load(f)

with tempfile.TemporaryDirectory() as tmp:
    mod_dir = os.path.join(tmp, "AnnealResearch")
    os.makedirs(mod_dir, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = tmp
    for mod in ledger["topological_order"]:
        src = os.path.join(support_dir, f"{mod}.lean")
        olean = os.path.join(mod_dir, f"{mod}.olean")
        subprocess.run(["lean", "-j1", "-M1024", "-o", olean, src], env=env, check=True)
        print(f"OK: AnnealResearch.{mod}")
EOF
```

Revalidate this report when:
- Updating the pinned `minirust/minirust` commit beyond `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (especially `spec/mem/tree_borrows/*` or `spec/mem/basic.md`),
- Updating `minirust/specr` beyond commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348` or `libspecr` beyond `0.1.41`, or
- Upgrading the Lean 4 toolchain beyond `v4.34.1`.
