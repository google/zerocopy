# MiniRust Tree Borrows Protectors, Coupled vs. Factored Prefix Correspondence, `libspecr` Copy-on-Write Semantics, and Program-Logic Boundaries

## Summary

MiniRust (`minirust/minirust` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`) specifies its Tree Borrows aliasing model across `spec/mem/tree_borrows/{memory.md,tree.md,reborrow_settings.md,state_machine_unprotected.md,state_machine_protected.md}` as a wrapper (`TreeBorrowsMemory<M>`) around `BasicMemory`, executing over `specr` (`minirust/specr` at commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348`, published on crates.io as `libspecr 0.1.41`). Each allocation carries a recursive permission tree (`Node` with `permissions: List<Permission>`, `protected: Protected`, and `children: List<Node>`), mutated functionally through `libspecr`'s garbage-collected copy-on-write containers (`List<T>`, `Map<K, V>`, `Set<T>` backed by `GcCow<T>`) and fallible `?` error propagation.

This report unifies a 93-module mechanized Lean 4 (`4.34.1`) investigation (1,026 kernel-checked `#print axioms` theorem audits, re-verified on `2026-10-24`) with an 81,915-trace differential comparison against Miri (`rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`) and a source/documentation audit of the PLDI 2025 Tree Borrows calculus and Rudy Peterson's 2025 $\lambda_{\text{TB}}$ Iris program logic:

1. **Executable vs. Prose Discrepancies and Two-Stage Protector Release in `tree.md` and `memory.md`:**
   - In `Node::access` and `Node::release_protector` (`spec/mem/tree_borrows/tree.md:71-145`), `path: Option<Path>` encodes `Some(path)` as `NodeRelation::Local` (visited along ancestors up to and including the accessed node `Some([])`, after which `subpath` yields `None` for all descendants) and `None` as `NodeRelation::Foreign` (all non-ancestors, including descendants of the accessed node), whereas the prose comment at `tree.md:62-66` reverses `Some` and `None`.
   - `TreeBorrowsMemory::release_protector` (`spec/mem/tree_borrows/memory.md:201-235`) executes in **two stages**: (a) a targeted `access_node(p.path, ...)` pass that converts `p.path`'s permission array via `unprotect()` and extracts per-byte implicit accesses `List<Option<AccessKind>>`, followed by an allocation liveness check; and (b) if the allocation is still live, a tree-wide `Node::release_protector(Some(p.path), accesses)` traversal that at `Some([])` sets `self.protected = Protected::No` and **returns immediately without traversing `p.path`'s subtree**, while applying implicit accesses to all ancestor (`Local`) and non-ancestor/outside-subtree (`Foreign`) nodes.
2. **Transactional `?` Rollback in `BasicMemory` vs. `GcCow` Copy-on-Write Persistence and `libspecr` Packaging Drift:**
   - In `BasicMemory::store` and `BasicMemory::load` (`spec/mem/basic.md:227-274`), `let mut alloc = self.allocations[id];` copies the value-type `Allocation` into a local variable; if `T::access` returns `Err(Ub)` via `?`, `self.allocations.set(id, alloc)` is never reached, rolling back the allocation update.
   - Inside `List::mutate_at` (`libspecr/src/list/mod.rs:140-149`) and `GcCow::mutate` (`libspecr/src/gc/gccow.rs:42-48`), however, `GcCow::mutate` clones the inner `Vec`, invokes the closure `&mut T -> O` opaquely without inspecting whether `O` is `Result::Err`, allocates a new GC cell for the mutated `Vec`, and overwrites `*self` **before** the caller's `?` operator inspects `O` (`HelperValueHeap`, `HelperNestedMutation`, `HelperValueControls`).
   - Although crates.io `libspecr-0.1.41.crate` records `"sha1": "15200eb5e676e2ee91f43bd79e674f8fc32e5348"` in `.cargo_vcs_info.json`, its source files differ from git commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348`: the git tree adds `#[derive(Clone, Copy)]` (instead of `#[derive(Clone)]`) to `List`, `Set`, `Map`, `GcCow`, and `Obj`, and adds `#[repr(transparent)]` to `Obj<T>`.
3. **End-to-End Coupled vs. Factored `TreeBorrowsMemory` Correspondence Across All Operations and Prefixes:**
   - Separating recursive `Node` trees (`TreeReference`, `TreeMemory`) into an ordered tree topology plus a flat path-indexed store (`TreeFactored`, `TreeFactoredMemory`) preserves exact operational status, diagnostics, returned pointers/bytes, and reified residual states across `allocate` root birth, demonic allocator base-address selection, `load`/`store` with recursive reference provenance, live `reborrow` child insertion, `dereferenceable`, `deallocate` strong-protector UB checks, `exit` leak checks, and ordered `end_call` protector release lists (`TreeCorrespondence` through `TreeEndCallFailureControls`).
4. **MiniRust vs. Miri Per-Location Agreement and $\lambda_{\text{TB}}$ / Simuliris Program-Logic Boundaries:**
   - An exhaustive bounded transcription comparison (`support/minirust-tree-borrows-logic-correspondence-d821c6e/probe.py`) of MiniRust's unprotected/protected state machines against Miri (`0e1a23b0794bec7860df8c06a774f4316746795a`) over all four-action traces of length $0 \le k \le 6$ from 15 representative states finds **zero differences across 81,915 traces**, while operational differences remain in range compression, zero-sized reborrows on dead allocations, wildcard exposed provenance, and retag data-race reporting.
   - Peterson's 2025 $\lambda_{\text{TB}}$ thesis establishes Iris adequacy for a block/value calculus with unprotected static-size retags, permission weakening, subtree deletion, and lateral range splitting, but excludes byte encodings, `UnsafeCell` interior mutability, and the full protector lifecycle. The PLDI 2025 Simuliris development proves contextual optimization refinements (assuming source safety) rather than client-facing API safety for Rust or MiniRust.

## Applicability

- **MiniRust specification (`minirust/minirust`):** Commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (retained archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`):
  - `spec/mem/tree_borrows/memory.md` (9,666 bytes; SHA-256 `6dd36c2f4b18e8fa3775c79e0c1a158cf129224fb2cb606a8a3e134b04765e53`)
  - `spec/mem/tree_borrows/tree.md` (5,532 bytes; SHA-256 `9f2de7f400f31f0a130da77f51936be45b3e7f7fc8743934bc816aaebbb0e56c`)
  - `spec/mem/tree_borrows/reborrow_settings.md`
  - `spec/mem/tree_borrows/state_machine_unprotected.md` (4,507 bytes; SHA-256 `d21fa9d19e5c828416aa67fffe86137f54d1ffbe26dc42d282f704ff97a65668`)
  - `spec/mem/tree_borrows/state_machine_protected.md` (8,415 bytes; SHA-256 `770e0ebff4699c14284e699b6a48eb5a80147f6965056ca9000f74a353baaf98`)
  - `spec/mem/basic.md` (10,275 bytes; SHA-256 `8bb62a21b6cd0050e8ac2b0c690be89ef1e7de4b779b18666a98b683b63a3763`), `spec/lang/machine.md` (14,940 bytes; SHA-256 `121c624125adf8d8d988b6d088d8e85687e8a275ee703a80e486dcb05dfbd91c`), `spec/lang/step/reborrow.md` (8,450 bytes; SHA-256 `56dd4774650317972e4bb1dbbf170fd3899038c4e18bc0d4fd33dbcd1f4f6a00`), and `spec/lang/step/terminators.md` (9,938 bytes; SHA-256 `c24989ef7bc92298a11268bc7766cfab93b751bc4ca6f7f676c0115fd4bc768c`).
- **Specr runtime (`minirust/specr`):** Git commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348` (archive SHA-256 `7e39738319f77a43fd0ce8e185888306b3a777f7b3f9d3234ec1802b9da5e220`) vs. published crates.io `libspecr 0.1.41` (archive SHA-256 `a3c0c46f39513f6c4b533ec6bea7d623f6761fd0a610b1152db7f2e4dd385a61`). Both versions share the `GcCow::mutate` and `List::mutate_at` implementations, while differing on `Copy` derives and `#[repr(transparent)]` on `Obj<T>`.
- **Miri and external Tree Borrows literature:**
  - `rust-lang/miri` at commit `0e1a23b0794bec7860df8c06a774f4316746795a` (`src/borrow_tracker/tree_borrows/{mod.rs,perms.rs,tree.rs}`). Relevant configuration parameters include MiniRust's `implicit_writes` / `fn_implicit_writes` and Miri's `implicit_writes` / `precise_interior_mut`.
  - Tree Borrows PLDI 2025 paper (DOI `10.1145/3735592`, PACMPL 9 PLDI Article 188).
  - Rudy Peterson's 2025 ETH Zürich Master's thesis ($\lambda_{\text{TB}}$, stating Rocq development commit `ccca9f325f909dceed4fd88008862f64296dbfd9`; ETH GitLab source was inaccessible during observation, so $\lambda_{\text{TB}}$ claims are bounded by the published thesis text).
- **Mechanized and executable verification environments:**
  - Lean 4 `4.34.1` (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`), using only `{propext, Quot.sound, Classical.choice}`.
  - Python 3 execution of the 81,915-trace MiniRust/Miri transition table probe (`support/minirust-tree-borrows-logic-correspondence-d821c6e/probe.py`).

## Findings

### 1. Tree Borrows Permission Lattice, Subpath Relation, and Two-Stage Protector Release (`tree.md`, `memory.md`, `state_machine_*.md`)

**Basis:** `source` and `execution`

#### 1.1 Unprotected vs. Protected Permission Lattices (`TreePermissions.lean`)

In `spec/mem/tree_borrows/state_machine_unprotected.md` and `state_machine_protected.md`, each node in an allocation's borrow tree stores a `Protected` flag (`No`, `Weak`, `Strong`) and a byte-indexed permission vector `permissions: List<Permission>`, where `Permission` is a tagged sum `Unprotected(UnprotectedPermission)` or `Protected(ProtectedPermission)`:
- `UnprotectedPermission` has 6 states: `Cell`, `Reserved`, `ReservedIm`, `Unique`, `Frozen`, `Disabled`.
- `ProtectedPermission` has 5 constructors (8 concrete states): `Cell`, `Reserved { had_local_read: bool, had_foreign_read: bool }`, `Unique`, `Frozen { had_local_read: bool }`, and `Disabled`. Under a foreign write, a protected `Reserved { had_local_read: false, .. }` transitions to `Reserved { had_local_read: false, had_foreign_read: true }` rather than `Disabled`, whereas a foreign write against protected `Unique`, `Frozen`, or `Reserved { had_local_read: true, .. }` immediately throws UB (`foreignWriteProtected` in [`support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreePermissions.lean:45-177`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreePermissions.lean#L45-L177)).
- Calling `unprotect()` (`state_machine_protected.md:94-112`; [`TreePermissions.lean:179-203`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreePermissions.lean#L179-L203)) maps each `ProtectedPermission` to `(UnprotectedPermission, Option<AccessKind>)`:
  - `ProtectedPermission::Unique` $\mapsto$ `(UnprotectedPermission::Unique, Some(AccessKind::Write))`
  - `ProtectedPermission::Reserved { had_local_read: true, .. }` $\mapsto$ `(UnprotectedPermission::Reserved, Some(AccessKind::Read))`
  - `ProtectedPermission::Frozen { had_local_read: true }` $\mapsto$ `(UnprotectedPermission::Frozen, Some(AccessKind::Read))`
  - All other states emit `None` for the implicit access.

#### 1.2 Executable `Some(path)` vs. `None` Node Relation and Comment Reversal in `tree.md`

In `spec/mem/tree_borrows/tree.md` (`Node::access` and `Node::release_protector`), the parameter `path: Option<Path>` determines `NodeRelation`:
- **Executable equations (`tree.md:71-106`, mechanized in [`TreeReference.lean:100-110`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeReference.lean#L100-L110)):**
  - `let rel = if path.is_some() { NodeRelation::Local } else { NodeRelation::Foreign };`
  - For each child index `idx`, `let subpath = path.and_then(|path| if path.get(0) == Some(idx) { Some(path[1..]) } else { None });`
  - Consequently, every ancestor of the target node has `path = Some(idx :: rest)` (`Local`), the target node itself receives `path = Some([])` (`Local`), and **every descendant of the target node** receives `subpath = None` (`Foreign`), just like sibling subtrees.
- **Prose comment discrepancy (`tree.md:62-66`):** The comment above `Node::access` states the opposite convention (*"`path` is `None` if the accessed node is an ancestor of `self`, or `Some` of a path from `self` to the accessed node"*). Following the prose comment instead of the executable equations would invert `Local` and `Foreign` transitions on every ancestor and descendant ([`TreeMemoryControls.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeMemoryControls.lean)).

#### 1.3 Two-Stage `release_protector` and Subtree Skipping (`memory.md:201-235`, `tree.md:108-145`)

In `spec/mem/tree_borrows/memory.md:201-235`, `TreeBorrowsMemory::release_protector(p: Provenance)` executes in two distinct stages:
1. **Stage 1 — Targeted conversion and implicit-access extraction (`unprotectAt`, [`TreeReference.lean:273-305`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeReference.lean#L273-L305)):** Descends via `alloc.extra.root.access_node(p.path, ...)` to the single node at `p.path`, asserts `node.protected != Protected::No`, converts each byte's `Permission::Protected(perm)` via `perm.unprotect()`, writes the resulting `Permission::Unprotected` array back into `node.permissions`, and returns the per-byte implicit access vector `accesses: List<Option<AccessKind>>`.
2. **Liveness gate (`memory.md:223-227`):** Checks `if !self.mem.allocations[p.alloc_id.0].live { return ret(()); }`. If the allocation was already deallocated, Stage 1's conversion is retained and Stage 2 is skipped.
3. **Stage 2 — Complement traversal (`releaseCore` / `releaseTraverse`, [`TreeReference.lean:184-212,307-311`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeReference.lean#L184-L212)):** Calls `alloc.extra.root.release_protector(Some(p.path), accesses)` (`tree.md:108-145`). At `path == Some(Path::new())` (`Some([])`, i.e., the released node `p.path` itself), `Node::release_protector` sets `self.protected = Protected::No` and **immediately returns `ret(())` without applying `accesses` to `self` or recursing into `self.children`**. Thus **descendants of the released node `p.path` are never visited by the implicit access pass**, preserving returned child references derived from the protected argument, while ancestors receive `Local` implicit accesses and non-descendant cousins/siblings receive `Foreign` implicit accesses ([`TreeTraversal.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeTraversal.lean), [`TreeReleaseAgreement.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeReleaseAgreement.lean), [`TreeMemoryControls.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeMemoryControls.lean)).

---

### 2. Transactional `?` Rollback in `BasicMemory` vs. `GcCow` Copy-on-Write Persistence in `libspecr`

**Basis:** `source`, `execution`, and `derived`

1. **Outer `BasicMemory` allocation updates roll back on `T::access` UB (`spec/mem/basic.md:227-274`):**
   In `BasicMemory::store` and `BasicMemory::load`, the method copies `let mut alloc = self.allocations[id];`, mutates `alloc.extra` via `T::access(...)?`, and only reaches `self.allocations.set(id, alloc)` if `T::access` returns `Ok(())`. If `T::access` throws UB mid-traversal, the local copy `alloc` is dropped and `self.allocations[id]` in `BasicMemory` remains unchanged ([`TreeMemory.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeMemory.lean), [`TreeExceptions.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeExceptions.lean)).
2. **Inner `List::mutate_at` and `GcCow::mutate` commit before `?` inspects `Result` (`libspecr/src/list/mod.rs:140-149`, `libspecr/src/gc/gccow.rs:42-48`):**
   In `minirust/specr` (`15200eb5e676e2ee91f43bd79e674f8fc32e5348`), `List::mutate_at` calls `self.0.mutate(|v| f(&mut v[i]))`, where `GcCow::mutate` is:
   ```rust
   pub fn mutate<O>(&mut self, f: impl FnOnce(&mut T) -> O) -> O {
       let mut v = self.extract();
       let ret = f(&mut v);
       *self = GcCow::new(v);
       ret
   }
   ```
   Because `O` is unconstrained (`O = Result<(), TerminationInfo>` when invoked as `self.children.mutate_at(idx, |child| ...)?`), `GcCow::mutate` unconditionally allocates a new GC cell containing the mutated `v` and assigns `*self = GcCow::new(v)` **before** returning `ret` to the `?` operator.
3. **Mechanized verification of nested `GcCow` mutation ([`HelperValueHeap.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/HelperValueHeap.lean), [`HelperNestedMutation.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/HelperNestedMutation.lean), [`HelperValueControls.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/HelperValueControls.lean)):**
   Theorems `nested_exact`, `nested_observations`, `nested_error_exact`, and `nested_error_retains` ([`HelperNestedMutation.lean:145-209`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/HelperNestedMutation.lean#L145-L209)) prove that old handles (`root` and prior `RootImage` / `LeafImage` aliases) retain their original pure values (`readParent actual.heap root = some value`), so an outer caller that discards the mutated receiver handle on `Err` observes pure value rollback, while the mutated receiver handle (`actual.receiver = heap.next + 1`) and newly allocated heap cells (`heap.next`, `heap.next + 1`) remain installed in the heap even when the callback returns `.error error` (`rollback_discriminator` and `overwrite_discriminator` in [`HelperValueControls.lean:107-140`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/HelperValueControls.lean#L107-L140)).
4. **Packaging drift between crates.io `libspecr 0.1.41` and git `15200eb`:**
   Comparing `libspecr-0.1.41.crate` (SHA-256 `a3c0c46f39513f6c4b533ec6bea7d623f6761fd0a610b1152db7f2e4dd385a61`) against `minirust/specr` git commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348` shows that six files differ (`gc/gccow.rs`, `gc/obj.rs`, `list/mod.rs`, `map/mod.rs`, `set/mod.rs`, `Cargo.toml`): the git commit derives `Copy` (in addition to `Clone`) on `GcCow<T>`, `Obj<T>`, `List<T>`, `Map<K, V>`, and `Set<T>` and marks `Obj<T>` as `#[repr(transparent)]`, whereas the crates.io `0.1.41` tarball only derives `Clone`. Because MiniRust specs rely on implicit `Copy` semantics for `List` and `Map` values (such as `let mut alloc = self.allocations[id];`), MiniRust requires the git revision `15200eb5e676e2ee91f43bd79e674f8fc32e5348`.

---

### 3. Coupled vs. Factored `TreeBorrowsMemory` Correspondence Across All Operations and Prefixes

**Basis:** `execution` and `derived`

Across the 88 `Tree*.lean` modules in [`support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/), the coupled reference model (`TreeReference.Node` inside `TreeMemory.State`) and the factored model (`TreeFactored.State` separating `Topology` from path-indexed `Store : Path -> Entry` inside `TreeFactoredMemory.State`) are proved equivalent across six operational layers:

1. **Node & tree-level correspondence (`TreePermissions` .. `TreeUnprotectWidths`, 22 modules):**
   `TreeCorrespondence.reify` ([`TreeCorrespondence.lean:37-39`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeCorrespondence.lean#L37-L39)) reconstructs a recursive `TreeReference.Node` from `(topology, store)` while ignoring unrepresented store paths (`overwrite_absent_preserves_reify`, [`TreeCorrespondence.lean:103-113`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeCorrespondence.lean#L103-L113)). `TreeAgreement.access_agrees`, `TreeReleaseAgreement.releaseTraverse_agrees`, and `TreeUnprotectAgreement.unprotectAt_agrees` prove that recursive node access, Stage-2 protector traversal, and Stage-1 targeted `unprotect` conversion commute with `reify` on all valid and invalid paths.
2. **Memory-level composition and invariant preservation (`TreeFactoredMemory` .. `TreeGeometryControls`, 13 modules):**
   `TreeMemoryAgreement`, `TreeMemoryOperations`, and `TreeMemoryReleaseAgreement` lift node agreement to `TreeMemory.State` and `TreeFactoredMemory.State` across `load`, `store`, `dereferenceable`, `free` (including the `contains_active_strong_protector` UB check before `BasicMemory::deallocate`), `exit`, and `release`. `TreeMemoryDomain.WellSized` and `TreeMemoryPreservation` prove that per-allocation permission-array widths (`arraysSized node alloc.size`) and tree domains are preserved across all memory operations.
3. **Client prefix correspondence and canonical encoding (`TreeMemoryClient` .. `TreeEncodedPrefixes`, 9 modules):**
   `TreeMemoryPrefixes` and `TreeMemoryPrefixAgreement` prove all-prefix reachability and `NoUB` equivalence (`prefix_iff`, `noUB_iff`) for reactive client plans over `TreeMemory` and `TreeFactoredMemory`. `TreeEncoding`, `TreeMemoryEncoding`, `TreeEncodingNormalization`, and `TreeEncodedPrefixes` define `encode : TreeReference.Node -> TreeFactored.State`, prove `reify (encode node) = node`, and establish canonical normal forms for factored stores.
4. **Live reborrowing and child-node insertion (`TreeGraft` .. `TreeReborrowHistory`, 29 modules):**
   `TreeGraft` and `TreeFactoredReborrow` model `TreeBorrowsMemory::reborrow` (`spec/mem/tree_borrows/memory.md:133-199`): validating dereferenceability over the reborrowed span, reading parent path `p.path`, performing the initial child access over the reborrowed offset range, constructing the new child node (with `Protected::Strong` or `Protected::Weak` when `is_protected` is set, `Protected::No` otherwise, `DefaultPermission` inside the reborrowed range and `Unprotected(Disabled)` outside), appending the child at index `children.len()`, and registering the new provenance in `current_frame.protectors` when protected. `TreeReborrowAgreement`, `TreeReborrowClient`, `TreeReborrowPrefixes`, and `TreeReborrowClientCoverage` prove exact single-step and all-prefix correspondence for dynamic client programs that chain arbitrary `reborrow` replies into subsequent `load`, `store`, `release`, and nested `reborrow` commands.
5. **Allocation root birth and demonic base-address choice (`TreeAllocation` .. `TreeChoiceCoverage`, 13 modules):**
   `TreeAllocation` and `TreeAllocationFreshness` model `TreeBorrowsMemory::allocate` (`spec/mem/tree_borrows/memory.md:62-84`), which delegates to `BasicMemory::allocate` and initializes the fresh allocation's borrow tree to a single unprotected root node (`Path::new()`) with `[Permission::Unprotected(UnprotectedPermission::Unique); size]`. `TreeAllocationChoices`, `TreeChoiceClient`, `TreeChoicePrefixes`, and `TreeChoiceCoverage` lift demonic allocator base-address non-determinism (`candidate : Nat`) and pointer-reply continuation passing to the full coupled and factored `TreeBorrowsMemory` machines, proving exact all-prefix and `NoUB` correspondence.
6. **Ordered `end_call` multi-protector release (`TreeEndCall` .. `TreeEndCallFailureControls`, 4 modules):**
   `TreeEndCall` ([`TreeEndCall.lean:35-153`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeEndCall.lean#L35-L153)) models `TreeBorrowsMemory::end_call` (`spec/mem/tree_borrows/memory.md:92-99`), which iterates in order over `extra.protectors : List<Provenance>` and invokes `self.release_protector(p)?`. Theorem `endCall_agrees` ([`TreeEndCall.lean:148-152`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeEndCall.lean#L148-L152)) proves that under the sole structural precondition `WellSized memory`, coupled `rEndCall` and factored `fEndCall` agree on status, UB/unsupported diagnostics, and complete reified memory state across arbitrary protector lists (including duplicate registrations, dead allocations, and mid-list UB aborts where earlier releases remain committed while later registrations are skipped, verified in [`TreeEndCallProperties.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeEndCallProperties.lean), [`TreeEndCallConstructed.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeEndCallConstructed.lean), and [`TreeEndCallFailureControls.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeEndCallFailureControls.lean)).

---

### 4. MiniRust vs. Miri Transition Agreement and $\lambda_{\text{TB}}$ / Simuliris Program-Logic Boundaries

**Basis:** `source`, `documentation`, `execution`, and `derived`

#### 4.1 Per-Location Transition Table Equivalence (`81,915` Traces) vs. Whole-Memory Obligations

MiniRust's unprotected states (`Cell`, `Reserved`, `ReservedIm`, `Unique`, `Frozen`, `Disabled` in `spec/mem/tree_borrows/state_machine_unprotected.md`) correspond to Miri's (`rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`, `src/borrow_tracker/tree_borrows/perms.rs:130` and `tree.rs:130`) `Cell`, `ReservedFrz`, `ReservedIM`, `Unique`, `Frozen`, and `Disabled` states (with Miri's conflict bit irrelevant while unprotected). For protected locations, MiniRust encodes `had_local_read` and `had_foreign_read` inside `ProtectedPermission` variants (`state_machine_protected.md`), whereas Miri stores an `accessed` bit in `LocationState` and a `conflicted` bit in `ReservedFrz`, first updating the permission and then rejecting transitions to `Disabled` when protected and accessed.

The executable comparison script [`support/minirust-tree-borrows-logic-correspondence-d821c6e/probe.py`](support/minirust-tree-borrows-logic-correspondence-d821c6e/probe.py) (results archived in [`support/minirust-tree-borrows-logic-correspondence-d821c6e/results.json`](support/minirust-tree-borrows-logic-correspondence-d821c6e/results.json)) independently transcribes both state machines, normalizes their states, and enumerates every four-action trace (`local read`, `local write`, `foreign read`, `foreign write`) of length $0 \le k \le 6$ from 15 representative initial states: **all 81,915 traces produce identical outcomes (0 differences)**. Negative controls confirm that protected `Reserved` + foreign read + local write is rejected (whereas unprotected becomes `Unique`) and `ReservedIm` + foreign write + local write becomes `Unique` (whereas ordinary `Reserved` is rejected).

However, per-byte state-machine agreement does not identify the complete memory models of MiniRust and Miri:

| Operation / Mechanism | MiniRust (`d821c6e`) | Miri (`0e1a23b`) & Remaining Correspondence Obligation |
| :--- | :--- | :--- |
| **Ordinary read/write** | Explicit per-byte permission vector on every node; full recursive tree walk | Compressed location range maps, traversal skipping, and per-node defaults; requires proving range compression preserves per-byte state |
| **Retag range & `UnsafeCell` masks** | Child node gets allocation-wide vector with `UnsafeCellStrategy` inside permissions (`Frozen`/`Cell`/`ReservedIm`/`Unique`) and `Unprotected(Disabled)` outside (`spec/mem/tree_borrows/reborrow_settings.md:88`) | Inside range map plus outside default; parameter-dependent precise mask vs. whole-`!Freeze` approximation (`precise_interior_mut`) |
| **Protector release** | Two-stage conversion (`unprotect`) + complement traversal skipping released node's subtree | `perform_protector_end_access` visits accessed ranges and skips children; must relate exposed descendants |
| **Zero-size retag** | `BasicMemory::dereferenceable` succeeds for length 0; `Some(prov)` can insert a child node even for size 0 | Non-live allocations with zero-length reborrow can mint a new tag without tracking bytes |
| **Exposed provenance (`int2ptr`)** | `TreeBorrowsMemory` leaves `expose` and `int2ptr` as `unimplemented!()` (`spec/mem/tree_borrows/memory.md:122-130`); `IntPtrCast` uses angelic `predict` | Wildcard trees and exposure caches approximate uncertain parentage |
| **Retag & protector race integration** | `retag` and `end_call` delegate to `M` without adding `ConcurrentMemory` `Access` entries | Retag explicitly reports nonempty implicit read/write ranges to Miri's data-race detector (`src/borrow_tracker/tree_borrows/mod.rs:328,390`) |

#### 4.2 $\lambda_{\text{TB}}$ and PLDI 2025 Simuliris Program-Logic Boundaries

- **Rudy Peterson's $\lambda_{\text{TB}}$ thesis (2025):** Reports Iris adequacy for a simplified block/value operational calculus supporting permission weakening, subtree deletion, and lateral range splitting/recombination (§§4.1, 6.1–6.4). However, $\lambda_{\text{TB}}$ restricts retags to unprotected references with static sizes, requires a live block and ownership at the start offset for zero-size retags, omits vertical subtree separation (because child accesses exert foreign effects on parent nodes), and excludes byte-fragment encodings, `UnsafeCell` interior mutability, and the protected-call lifecycle.
- **PLDI 2025 Tree Borrows paper (Simuliris, DOI `10.1145/3735592`, §§5, 7):** Proves contextual optimization refinements under sequentially consistent interleavings (allowing data races and exploiting protector-exit implicit accesses). Optimization refinement assumes the source program is UB-free to justify a transformed target program; it does not supply the converse client-facing safety theorem needed to verify an `unsafe` Rust or MiniRust library implementation.
- **Caller-tree contract obligations (`spec/mem/tree_borrows/reborrow_settings.md`):** At MiniRust function entry, reference arguments receive `Protected::Strong` and `Box` arguments receive `Protected::Weak` (while mutable references/boxes to `!Unpin` pointees skip retagging). For a shared 4-byte aggregate with an `UnsafeCell` at bytes `1..3`, the retag mask is `[Frozen, Cell, Cell, Frozen]` (verified in [`support/minirust-tree-borrows-logic-correspondence-d821c6e/probe.py`](support/minirust-tree-borrows-logic-correspondence-d821c6e/probe.py)). A compositional function contract must therefore parameterize retag preconditions by pointee layout, `UnsafeCell` byte mask, `Freeze`/`Unpin` traits, protection strength, and `implicit_writes` policy, and must account for `end_call` protector release on both normal `Return` and exceptional `ResumeUnwind`.

## Boundaries

- **Known not to apply:**
  - Single-pass protector release (combining `unprotect()` and implicit access emission in a single top-down walk, or visiting the released node's own subtree during implicit access emission) disagrees with `spec/mem/tree_borrows/{memory.md,tree.md}` on protected descendant nodes (`TreeMemoryControls.lean`).
  - Treating `Some(path)` as `Foreign` and `None` as `Local` (as written in the prose comment at `tree.md:62-66`) disagrees with the executable equations at `tree.md:71-106`.
  - Assuming `GcCow::mutate` rolls back physical heap allocations when its closure returns `Err(Error)` is false (`HelperValueControls.rollback_discriminator`); rollback holds only at the level of pure value observations through unmutated caller handles (`HelperNestedMutation.nested_error_retains`).
  - Peterson's $\lambda_{\text{TB}}$ adequacy theorem does not cover byte-level representations, `UnsafeCell` interior mutability, or protected references.
- **Not examined in this package:**
  - Integer-to-pointer cast exposure and prediction (`expose` / `predict` in `spec/mem/intptrcast.md`), which `TreeBorrowsMemory` leaves as `unimplemented!()` at `spec/mem/tree_borrows/memory.md:122-130`, and Miri's wildcard provenance tree implementation.
  - Concurrent atomic memory operations and data-race detection (`spec/mem/concurrent.md`, examined in `reports/minirust-core-calculi-basic-memory-and-nondeterminism/REPORT.md`).
- **Unsupported / out-of-contract representations:**
  - Out-of-bounds child path indices (`invalidPath`), mismatched permission array lengths (`arrayLength`), releasing an unprotected node (`unprotectUnprotected`), or negative `specr::Int` indices are classified as `.unsupported` structural faults distinct from language-level `.ub` (`TreeReference.Structural`, [`TreeReference.lean:41-54`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeReference.lean#L41-L54)) and are proved unreachable on `WellSized` states with minted provenances (`TreeMemoryDomain`, `TreeAllocationFreshness`, `TreeReborrowDomain`).
- **Unknown:**
  - Exact Rocq theorem signatures and axiom closure of the $\lambda_{\text{TB}}$ development (`ccca9f325f909dceed4fd88008862f64296dbfd9`), whose ETH GitLab repository was inaccessible at observation time.
  - Whether upstream MiniRust will update the prose comment at `spec/mem/tree_borrows/tree.md:62-66` to match the executable `Some`/`None` convention, or publish a newer `libspecr` crate version on crates.io syncing commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348`.

## Evidence

All 93 Lean 4 modules, the 81,915-trace Python differential probe, and their verification ledgers are preserved under `support/`:

1. **Mechanized Tree Borrows and `libspecr` `GcCow` correspondence (`support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/`, 93 Lean modules, 1,026 audited theorems, recorded `2026-10-24`):**
   - Complete module-by-module SHA-256, timing, topological build order, and `#print axioms` audit ledger: [`support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/lean-verification-results.json`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/lean-verification-results.json).
   - Key entry-point modules across the 6 layers:
     - *Permissions, traversal, and two-stage release:* [`TreePermissions.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreePermissions.lean), [`TreeReference.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeReference.lean), [`TreeFactored.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeFactored.lean), [`TreeCorrespondence.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeCorrespondence.lean), [`TreeTraversal.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeTraversal.lean), [`TreeAgreement.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeAgreement.lean), [`TreeReleaseAgreement.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeReleaseAgreement.lean), [`TreeUnprotectAgreement.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeUnprotectAgreement.lean).
     - *Memory operations and prefix equivalence:* [`TreeMemory.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeMemory.lean), [`TreeFactoredMemory.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeFactoredMemory.lean), [`TreeMemoryAgreement.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeMemoryAgreement.lean), [`TreeMemoryOperations.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeMemoryOperations.lean), [`TreeMemoryPrefixes.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeMemoryPrefixes.lean), [`TreeMemoryPrefixAgreement.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeMemoryPrefixAgreement.lean), [`TreeEncodedPrefixes.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeEncodedPrefixes.lean).
     - *Live reborrowing, demonic allocation choices, and `end_call`:* [`TreeGraft.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeGraft.lean), [`TreeFactoredReborrow.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeFactoredReborrow.lean), [`TreeReborrowAgreement.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeReborrowAgreement.lean), [`TreeReborrowPrefixes.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeReborrowPrefixes.lean), [`TreeAllocation.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeAllocation.lean), [`TreeChoicePrefixes.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeChoicePrefixes.lean), [`TreeEndCall.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeEndCall.lean), [`TreeEndCallProperties.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeEndCallProperties.lean), [`TreeEndCallConstructed.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeEndCallConstructed.lean), [`TreeEndCallFailureControls.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/TreeEndCallFailureControls.lean).
     - *`GcCow` copy-on-write heap semantics:* [`HelperValueHeap.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/HelperValueHeap.lean), [`HelperNestedMutation.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/HelperNestedMutation.lean), [`HelperValueControls.lean`](support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence/HelperValueControls.lean).
2. **MiniRust vs. Miri transition probe and $\lambda_{\text{TB}}$ boundary evidence (`support/minirust-tree-borrows-logic-correspondence-d821c6e/`, observed `2026-10-14`):**
   - [`support/minirust-tree-borrows-logic-correspondence-d821c6e/probe.py`](support/minirust-tree-borrows-logic-correspondence-d821c6e/probe.py) and [`support/minirust-tree-borrows-logic-correspondence-d821c6e/results.json`](support/minirust-tree-borrows-logic-correspondence-d821c6e/results.json) — 81,915-trace bounded state-machine equivalence check and 4-byte `UnsafeCell` mask reconstruction.
   - [`support/minirust-tree-borrows-logic-correspondence-d821c6e/source-evidence.json`](support/minirust-tree-borrows-logic-correspondence-d821c6e/source-evidence.json), [`support/minirust-tree-borrows-logic-correspondence-d821c6e/artifact-hashes.json`](support/minirust-tree-borrows-logic-correspondence-d821c6e/artifact-hashes.json), [`support/minirust-tree-borrows-logic-correspondence-d821c6e/coverage.json`](support/minirust-tree-borrows-logic-correspondence-d821c6e/coverage.json), and [`support/minirust-tree-borrows-logic-correspondence-d821c6e/execution.json`](support/minirust-tree-borrows-logic-correspondence-d821c6e/execution.json).

## Revalidation

To re-check all 93 Lean 4 (`4.34.1`) modules in topological order and re-run the 81,915-trace MiniRust/Miri transition probe from the repository root:

```bash
python3 - <<'EOF'
import json, os, subprocess, tempfile

pkg_dir = "reports/minirust-tree-borrows-protectors-and-program-logic-correspondence"
tb_dir = os.path.join(pkg_dir, "support/minirust-d821c6e-tree-borrows-protectors-and-prefix-correspondence")
with open(os.path.join(tb_dir, "lean-verification-results.json")) as f:
    ledger = json.load(f)

with tempfile.TemporaryDirectory() as tmp:
    mod_dir = os.path.join(tmp, "AnnealResearch")
    os.makedirs(mod_dir, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = tmp
    for mod in ledger["topological_order"]:
        src = os.path.join(tb_dir, f"{mod}.lean")
        olean = os.path.join(mod_dir, f"{mod}.olean")
        subprocess.run(["lean", "-j1", "-M1024", "-o", olean, src], env=env, check=True)
    print(f"OK: verified {len(ledger['topological_order'])} Tree Borrows Lean modules.")

logic_dir = os.path.join(pkg_dir, "support/minirust-tree-borrows-logic-correspondence-d821c6e")
subprocess.run(["python3", os.path.join(logic_dir, "probe.py")], stdout=subprocess.DEVNULL, check=True)
print("OK: verified 81,915-trace MiniRust/Miri transition probe.")
EOF
```

Revalidate this package when `minirust/minirust` advances beyond `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `minirust/specr` advances beyond `15200eb5e676e2ee91f43bd79e674f8fc32e5348`, `rust-lang/miri` advances beyond `0e1a23b0794bec7860df8c06a774f4316746795a`, or the Lean 4 toolchain changes from `4.34.1`.
