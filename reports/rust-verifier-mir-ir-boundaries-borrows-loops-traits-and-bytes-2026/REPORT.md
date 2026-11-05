<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Rust Verifier MIR and IR Boundaries Across Borrows, Loops, Generics, and Bytes

## Summary

Rust verification frameworks make fundamentally different trade-offs between the
size of their trusted computing base (TCB) and the ergonomics of their proof
obligations. Systems that translate `rustc` Mid-Level Intermediate
Representation (MIR) into pure functional programs or verification-condition
calculi before reaching a proof kernel—such as Charon/Aeneas, Creusot, and
Verus—eliminate explicit control-flow graphs (CFGs), stack-frame temporaries,
and pointer indirection from user proofs, but place complex control-flow
structuring, borrow-region resolution, and memory-erasure passes inside their
unverified translation pipeline. Conversely, systems that embed an operational
machine directly inside an interactive theorem prover—such as RefinedRust
(Radium/Caesium in Rocq/Iris) and Anneal (`Trusted/MirSemantics.lean` in Lean
4)—confine the frontend to a mechanical syntax transcription of `rustc` MIR,
shifting borrow resolution, CFG join unification, and layout reasoning into
kernel-checked definitions and theorems.

This report compares seven Rust verification and semantics architectures—Anneal,
Charon/Aeneas, Creusot (fMIR/Coma/Pearlite), RefinedRust
(Radium/Caesium/Lithium), Verus (VIR/AIR), Kani (MIR-to-CBMC Goto), and
MiniRust—across four load-bearing semantic design axes that govern Anneal's
Stage 2 (`trusted/lean/Trusted/`) and Stage 3 (`theory/Anneal/`) boundary:

1. **Axis 1 — Mutable Borrows, Nested Reborrows, Two-Phase Borrows, and Raw
   Pointers:** Frame-relative path lenses with immediate root-tree writeback
   (`MirVal.refVal frameId localIdx proj mutability`, resolved via
   `resolvePlace` and `writePlace`) execute directly on unstructured MIR basic
   blocks without borrow-checker region reconstruction, support cross-frame
   mutable reference forwarding (`frameId < s.frameId`), and fail closed when a
   reference to a dying stack frame escapes at `Terminator.return_`
   (`returnRefsOk`). In `support/VerifierEncodingComparison.lean`, we prove
   `lens_prophecy_equiv`, showing that Stage 2 operational path-lens execution
   and Stage 3 functional backward-lens / prophetic composition produce
   identical terminal struct states across mutable field borrows and nested
   reborrows (`&mut s.a` followed by `&mut *r`), while
   `aliased_backward_lenses_clobber` proves why co-live aliased pointers break
   independent functional backward lenses and require Stage 2 operational store
   resolution.
2. **Axis 2 — Loops, Diamond CFG Joins, and State Canonicalization at Join
   Points:** Unstructured small-step symbolic execution (`ExecNormal`) over
   `Runtime(PostCleanup)` MIR fails to unify predecessor states `(s_then,
   s_else)` at diamond merge blocks when branch-local temporaries (`_2` written
   only in `bb1`, `_3` written only in `bb2`) remain in `s.locals`—or when
   asymmetric `StorageDead` statements increment `s.localGens` on different
   slots (`raw_diamond_join_states_ne` and
   `asymmetric_storageDead_gen_mismatch`). We prove in
   `canonicalize_join_unifies`, `execNormal_diamond_joined`, and
   `canonicalize_preserves_return` that a Stage 3 dead-local canonicalization
   pass (`canonicalizeLocals` / `lowerBody : MirBody → MirBody`) unifies the
   predecessor states at `bb3` into a single canonical `MirState` while
   preserving observable `MirReturn` semantics and requiring zero expansion of
   the Stage 2 `Trusted/` TCB.
3. **Axis 3 — Generics, Trait Resolution, Associated Items, and
   Post-Monomorphization Errors (PMEs):** Pure post-monomorphization checkers
   (Kani) cannot prove universally quantified library contracts over open type
   parameters, whereas pure pre-monomorphization verifiers (Aeneas, Creusot,
   Verus) cannot admit functions guarded by size- or layout-dependent inline
   `const { ... }` assertions (`zerocopy::transmute_ref!`). Anneal's hybrid
   polymorphic `MirBody` (`MirTy.param idx`, `MirBody.subst`, `ConstsTotal`,
   and `MonoAdmitted`) reconciles both regimes. We prove in
   `size_only_insufficient_for_ref_transmute` and `pme_ref_transmute_sound` why
   scaling beyond value transmutation (`transmute_copy`) to reference
   transmutation (`transmute_ref`) requires extending the Stage 2 layout
   environment from `tySizes : Nat → Nat` to paired `(size, align)` layouts
   (`dst.align ∣ src.align`), alongside `BodyId` dictionary/trait-method targets
   and associated constants.
4. **Axis 4 — Byte-Level Representation, Padding, `MaybeUninit`, Unions, and
   `transmute` Soundness:** Comparing MiniRust and Caesium's `List AbstractByte`
   (`init (u8, Option Provenance) | uninit`) against Anneal's structural
   `MirVal.adt` + `paddingBytes` model, we prove `intoBytes_iff_paddingFree` and
   `padded_transmute_to_int_reads_uninit`: structural `MirVal.adt` with
   `paddingBytes == 0` is both necessary and sufficient for padding-free
   `IntoBytes` / `FromBytes` transmutations, whereas sub-field bit-validity
   (niche enums, `bool`, `NonZero*`), union field overlays, and `MaybeUninit<T>`
   byte slices require per-byte initialization and provenance tracking.

## Applicability

Every finding in this report is scoped to the following pinned repositories,
commits, and toolchains recorded in `REPORT.json`:

- **Anneal (`joshlf/anneal`):**
  - Small-TCB kernel branch (`simplify-trusted`) at commit
    `572f1e80580daa4b052ce5646bb675484d9bb957`
    (`trusted/lean/Trusted/MirAst.lean`,
    `trusted/lean/Trusted/MirSemantics.lean`,
    `trusted/lean/Trusted/Refinement.lean`,
    `trusted/lean/Trusted/StepResult.lean`, and `theory/Anneal/MirLemmas.lean`).
  - Three-stage architecture documentation baseline (`main` and
    `arch-design-docs`) at commits `d79b0c070cf4115b523fe6ee62c1e72504de2254`
    and `be61ec573335d549398b5d2d0c5bea3ef25d0c1f` (`docs/architecture.md`,
    `docs/design.md`, `docs/trust-model.md`).
  - Functional-translation and weak-memory prototype (`skeleton`) at commit
    `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`
    (`trusted/lean/Trusted/Memory.lean`,
    `theory/Anneal/FunctionalTranslation.lean`).
- **Charon and Aeneas:** `AeneasVerif/charon` version `0.1.210` at commit
  `1e08453924610c19d74c245a7308f17c1008e2db` and `AeneasVerif/aeneas` at commit
  `21345f80fa212c596f6437378d7d57984fa2ea77`.
- **Creusot and Coma:** `creusot-rs/creusot` at commit
  `c4e9770ac1371ac4274bfe02145266d315c2fb86` and the ESOP 2025 Coma
  specification
  (`sha256: a52ad7b745fb8a1d0b54bf52b54f0cfaec18e59f587eda551a54702cf61a8d8e`).
- **RefinedRust / Radium / Caesium:** Zenodo artifact record `21636474`
  (`sha256: 34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`).
- **Verus:** `verus-lang/verus` at commit
  `0141ebc6f14410dfc87fef1da57408578002eb7c`.
- **Kani:** `model-checking/kani` at commit
  `9461e07af7ec929f050aa4192f29363c9be07779`.
- **MiniRust:** `minirust/minirust` at commit
  `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`.
- **Rust Compiler, Reference, and `zerocopy`:** `rust-lang/rust` `1.99.1` at
  commit `58cf8f9c35b355199727627d07ae34a4e2846d67`, `rust-lang/reference` at
  commit `82da570bafd9efed421bdbae0f8603ede8dd308b`, and `google/zerocopy` at
  commit `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`.
- **Lean 4 Toolchains:** `leanprover/lean4:v4.28.0` (commit
  `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`) and `leanprover/lean4:v4.34.1`
  (commit `5045d0056413266e57c625dcd7c365b10e377c52`).

## Findings

### Cross-Verifier Architectural Synthesis Across the Four Design Axes

Basis: `source` + `documentation` + `derived`.

The seven systems partition the verification pipeline at different compiler
dialects and place different semantic obligations inside their trusted computing
base:

| Verifier / Spec | Compiler Extraction Point | Axis 1: Borrows, Reborrows & Pointers | Axis 2: Loops & CFG Joins | Axis 3: Generics, Traits & PMEs | Axis 4: Bytes, Padding & `transmute` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Anneal** (`572f1e805` / `d79b0c070`) | `Runtime(PostCleanup)` MIR (`mir_drops_elaborated_and_const_checked` before `Steal<Body>`, `-Z mir-preserve-ub`) | **Stage 2 TCB:** Frame-relative `(FrameId, LocalIdx, List PlaceElem)` path lens (`MirVal.ref` / `refVal`) + `localGens` + `returnRefsOk`. **Stage 3:** Plan-guided `LoanEntry` backward lenses for safe code. | **Stage 2 TCB:** Unstructured basic blocks with PC canonicalized on jump. **Stage 3:** In-place `lowerBody` / `canonicalizeLocals` dead-local cleanup + cut-point `ExecNormal` / `wpCut`. | **Hybrid:** Polymorphic `MirBody` (`MirTy.param`, `MirBody.subst`, `tySizes`) gated by two-stage PME `ConstsTotal` and `MonoAdmitted`. | **Hybrid:** Structural `MirVal.adt` + `paddingBytes` + `extractTransmuteBits` / `constructTransmuteVal` + `MirVal.uninit`. |
| **Charon + Aeneas** (`1e084539` / `21345f80`) | `mir_promoted` / post-borrowck MIR $\to$ ULLBC $\to$ structured LLBC | Symbolic borrow-projector trees (`avalues`/`aloans`/`aproj`) compiled to pure functional `Result α` values and synthesized backward functions. Raw pointers out of scope. | ULLBC $\to$ LLBC structural `if`/`loop` reconstruction; abstract environment joins (`InterpJoin.ml`) and fixed-point loop summaries (`partial_fixpoint`). | Pre-monomorphization dictionary-passing structures carrying associated types, constants, and method closures. | Pure algebraic values (`USize`, `U32`, ADTs); no byte representation, padding, or `MaybeUninit`. |
| **Creusot** (`c4e9770a` + Coma) | Post-borrowck MIR + Polonius/NLL $\to$ `fMIR` $\to$ Coma $\to$ Why3 | Prophetic borrows `Bor { cur: *p, final: ^p, id }` resolved at borrow expiration; raw pointers / `UnsafeCell` via trusted `PermCell` / `PtrOwn` axioms. | Unstructured `fMIR` lowered to Coma continuation handlers parameterized only by live mutated variables (`&x`), scoping out dead temporaries. | Pre-monomorphization modular trait contracts and refinement laws in Pearlite/Why3. | Logical integers/bitvectors in Why3; layout and transmutation require trusted axioms. |
| **RefinedRust** (Radium / Caesium `21636474`) | Monomorphized/polymorphic MIR $\to$ Radium/Caesium AST in Rocq | Explicit `(block_id, offset)` heap in Caesium with Iris separation-logic ownership and lifetime inclusion (`&uniq`, `&shr`). | Unstructured block map annotated with `JoinPoint` vs. `BleedBlock` and `LoopInfo`; Lithium `JCACHED` memoizes post-join goals. | Rocq polymorphic `TypeRepr` parameterized by layout descriptors and refinement predicates. | Explicit `List val_byte` (`Init u8 prov \| Uninit \| Poison`) with padding and provenance preservation. |
| **Verus** (`0141ebc6`) | `rustc` HIR/THIR $\to$ mode-checked `VIR` (`exec`/`proof`/`spec`) $\to$ `AIR` $\to$ Z3 | Safe `&mut T` restricted to `old(x)`/`new(x)` parameter updates via `rustc` borrowck; raw pointers via linear tracked `PointsTo<T>` / `PointsToRaw` ghost tokens. | Structured SST/VIR lowered to passive acyclic AIR with SSA variable versioning; loops cut by user invariants and `decreases` clauses. | Polymorphic VIR/AIR with fuel-bounded recursive specs and trait broadcast axioms. | Trusted `PointsToRaw` byte ranges and `is_no_padding` / `HasResolved` axioms; no operational byte reduction. |
| **Kani** (`9461e07a`) | Monomorphized `Runtime(PostCleanup)` MIR $\to$ CBMC Goto-programs | CBMC `(object_id, offset)` pointers bit-blasted over flat byte arrays; no Stacked/Tree Borrows aliasing enforcement. | Goto CFG unwound up to `#[kani::unwind(N)]` into bounded SSA $\phi$-nodes (or experimental loop contracts). | Strictly post-monomorphization: checks concrete `#[kani::proof]` harnesses only; cannot prove generic library contracts. | Bit-exact CBMC byte arrays with optional shadow-memory `-Z uninit-checks`. |
| **MiniRust** (`d821c6e3`) | Normative Markdown specification + `minimize` MIR translator | `ThinPointer (addr, Option<Provenance>)` over `BasicMemory` + Tree Borrows (`Reserved`, `Active`, `Frozen`, `Disabled` + `CallId` protectors). | Unstructured basic-block operational machine with explicit `StorageLive` / `StorageDead` allocation and deallocation. | Operates on layout-resolved runtime types. | Normative `List<AbstractByte>` (`Init(u8, Option<Provenance>) \| Uninit`) with per-type encode/decode. |

### Axis 1: Mutable Borrows, Reborrows, Two-Phase Borrows, and Raw Pointers

Basis: `source` + `execution` + `derived`.

#### 1. Three Semantic Encodings for References and Pointers

Rust verifiers employ three distinct representations for references (`&T`, `&mut
T`) and pointers (`*const T`, `*mut T`):

- **Encoding 1A — Frame-Relative Path Lenses with Immediate Tree Writeback
  (Anneal Stage 2 `Trusted/MirSemantics.lean`):**
  In `joshlf/anneal` at `572f1e80580daa4b052ce5646bb675484d9bb957`
  (`Trusted/MirAst.lean:105-115`, `Trusted/MirSemantics.lean:178-315`) and the
  composite-place Stage 2 target (`docs/architecture.md:195-248`), stack locals
  hold structured `MirVal` trees rather than flat byte addresses. A reference is
  a first-order descriptor `MirVal.ref depth gen loc` (extended to composite
  projections `MirVal.refVal frameId localIdx proj mutability`), where `frameId`
  identifies the monotonic call-stack activation that owns `localIdx`, `gen`
  records the slot's `StorageLive`/`StorageDead` generation counter in
  `localGens`, and `proj : List PlaceElem` records the path of field projections
  from the root local. Every place evaluation (`evalPlace` / `resolveRef`) and
  place assignment (`writePlace`) chases `.deref` links to the root `(frameId,
  localIdx, fieldPath)` and reads or updates the owner local's `MirVal` tree in
  place.
- **Encoding 1B — Functional Value Extraction with Backward Functions or
  Prophetic Variables (Aeneas LLBC, Creusot Pearlite/Coma, Anneal Stage 3
  `FunctionalTranslation.lean`):**
  Aeneas (`SymbolicToPure*.ml`) and Anneal's Stage 3 shallow functional
  translation (`theory/Anneal/FunctionalTranslation.lean:95-260` at
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`) represent an active mutable borrow
  as a `LoanEntry` carrying the borrowed sub-value `curVal : SymVal` and a pure
  backward function `back : SymVal → List SymVal` (a functional `put` lens).
  Creusot (`c4e9770ac1371ac4274bfe02145266d315c2fb86`) dualizes the backward
  function using prophetic borrows `Bor { cur: *p, final: ^p, id }`: a mutable
  borrow immediately prophesies the value `^p` that `p` will hold when its
  borrow region expires, and a nested reborrow `r2 = &mut *r1` sets `r2.cur =
  r1.cur`, assigns a fresh intermediate value on write, and equates `r1.cur`
  with `r2.final` when `r2` expires.
- **Encoding 1C — Explicit Allocation Store `(AllocId, Offset)` with Separation
  Logic or Borrow-Tag Trees (MiniRust, RefinedRust/Caesium):**
  MiniRust (`spec/mem/pointer.md`, `spec/mem/tree_borrows/memory.md` at
  `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`) and RefinedRust/Caesium
  (`radium/loc.v`, `radium/val.v` in Zenodo `21636474`) allocate every
  address-taken local in an explicit memory store indexed by `(AllocId, Offset)`
  and represent both references and raw pointers as `(AllocId, Offset,
  Option<Provenance>)`. Disjointness and aliasing permissions are enforced
  either by Iris separation-logic points-to resources (`l ↦ v`) or by Tree
  Borrows state transitions (`Reserved`, `Active`, `Frozen`, `Disabled`).

#### 2. Splitting Encoding 1A (Stage 2 TCB) from Encoding 1B (Stage 3 Theory)

Putting Encoding 1B (prophecies or backward functions) inside Stage 2
(`Trusted/`) would force the trusted semantics to depend on borrow-checker
region expiration points (`Drop` of regions or Polonius live ranges), which are
erased before `Runtime(PostCleanup)` MIR
(`compiler/rustc_mir_transform/src/lib.rs:630-684` in `rust-lang/rust` at
`58cf8f9c35b355199727627d07ae34a4e2846d67`). Conversely, Encoding 1A in Stage 2
requires no region annotations:

1. **Immediate Root Writeback Without Expiration Markers:** Because `writePlace`
   updates the owner local `(frameId, localIdx)` at the exact statement where
   `*r = v` executes, the owner local already holds the latest value whenever
   subsequent code reads it after the borrow ends.
2. **Cross-Frame Reference Forwarding and Fail-Closed Escape Detection:** When a
   caller in frame `0` passes `&mut s.a` to a callee in frame `1`, the callee
   receives `MirVal.refVal 0 1 [.fieldA] .mut`, mutates caller frame `0`'s
   local `1` directly, and pops frame `1` on `Terminator.return_`. At
   `Terminator.return_`, `returnRefsOk` (`Trusted/MirSemantics.lean:254-281`)
   checks in $O(1)$ depth fuel that no returned reference points into the dying
   frame (`targetFrame == curFrame ∧ targetLocal < localCount`) or any inner
   frame (`curFrame < targetFrame`), failing closed (`.failed`) on dangling
   references.
3. **Two-Phase Borrows:** In `rustc` MIR, two-phase borrows
   (`vec.push(vec.len())`) are lowered to standard `Rvalue::Ref` /
   `Rvalue::RawPtr` statements in `Runtime(PostCleanup)` after borrowck. Under
   Encoding 1A, creating the path-lens descriptor `MirVal.refVal` does not
   freeze or move the owner local in `s.locals`, so the shared read `vec.len()`
   during the reservation phase and the mutable write during the activation
   phase execute deterministically without special two-phase TCB rules.
4. **Mechanized Equivalence (`lens_prophecy_equiv`) and Aliasing Boundary
   (`aliased_backward_lenses_clobber`):** In
   `support/VerifierEncodingComparison.lean` (Section 1), we prove
   `lens_prophecy_equiv`, establishing that for a two-field struct `PairVal`
   mutated via `r1 = &mut s.a`, nested reborrow `r2 = &mut *r1`, `*r2 = v1`, and
   `*r1 = v2`, Stage 2's operational `execStage2Reborrow` and Stage 3's
   functional backward-lens / prophetic `execStage3Prophecy` reduce by `rfl` to
   the exact same terminal struct `some ⟨v2, b0⟩`. We also prove
   `cross_frame_ref_writeback_sound`, `escaping_ref_fails_closed`, and
   `aliased_backward_lenses_clobber`—the latter showing that if two co-live raw
   pointers alias the same field without disjointness, independent functional
   backward lenses overwrite earlier mutations (`(put (put s0 v1) v2).a = v2 ≠
   v1`), whereas Stage 2's operational store preserves exact execution order.

### Axis 2: Loops, Diamond CFG Joins, and State Canonicalization at Join Points

Basis: `source` + `execution` + `derived`.

#### 1. Why Unstructured CFG Execution Fails to Unify Raw Join States

In Anneal's Stage 2 operational semantics (`Trusted/MirSemantics.lean:458-510`
at `572f1e80580daa4b052ce5646bb675484d9bb957`) and Stage 3 symbolic execution
relation (`ExecNormal` in `theory/Anneal/MirLemmas.lean:514-524`), control-flow
transfers (`Terminator.goto target` and `Terminator.switchInt discr falseTarget
trueTarget`) already canonicalize the program counter by setting `block :=
target.index` and `stmtIdx := 0`. Nevertheless, when a diamond CFG `bb0 -> (bb1
| bb2) -> bb3` or a loop body executes along two paths that converge at `bb3`,
the resulting states `s_then` and `s_else` at `bb3` fail to unify (`s_then ≠
s_else`) for two distinct reasons:

1. **Unkilled Branch-Local Temporaries (`raw_diamond_join_states_ne`):**
   `rustc` allocates separate temporary locals for subexpressions in `then` and
   `else` arms (`_2` in `bb1`, `_3` in `bb2`). If `StorageDead` is omitted (or
   deferred until the enclosing scope exits after `bb3`), `s_then.locals` holds
   `some v` at `_2` and `none` at `_3`, whereas `s_else.locals` holds `none` at
   `_2` and `some v` at `_3`.
2. **Asymmetric `StorageDead` Generation Skew
   (`asymmetric_storageDead_gen_mismatch`):**
   Even when `rustc` emits `StorageDead(_2)` at the end of `bb1` and
   `StorageDead(_3)` at the end of `bb2`, `Trusted/MirSemantics.lean:331-342`
   defines `Stmt.storageDead loc` as both clearing `s.locals loc.index` to
   `none` *and* incrementing `s.localGens loc.index` via `bumpGen` (to
   invalidate any dangling references to `loc`). Consequently, at `bb3`,
   `s_then.locals = s_else.locals` holds, but `s_then.localGens 2 = 1 ≠ 0 =
   s_else.localGens 2` and `s_then.localGens 3 = 0 ≠ 1 = s_else.localGens 3`, so
   `s_then ≠ s_else` still prevents a single-state join lemma!
3. **Closure Nesting in Function-Typed Stores:**
   When `locals : Nat → Option MirVal` and `localGens : Nat → Nat` are
   represented as Lean functions updated via `updateLocal`, different update
   orders on `bb1` and `bb2` produce syntactically distinct closure spines that
   do not unify by `rfl` even when extensionally equal.

#### 2. Cross-Verifier Solutions and Anneal's Stage 3 Canonicalization Pass

Other verifiers avoid raw `MirState` unification at joins by transforming the
IR:

- **Aeneas (`InterpJoin.ml`, `InterpLoopsFixedPoint.ml` at `21345f80`):**
  Computes an abstract environment join (`join_ctxs`) over structured LLBC that
  intersects live bindings and introduces fresh symbolic variables for values
  modified across branches, and computes a fixed-point abstract environment at
  loop headers before emitting a `partial_fixpoint` function in Lean 4.
- **Creusot (`Coma` at `c4e9770a`):**
  Compiles each basic block `bb` into a Coma continuation handler whose explicit
  mutable parameters (`&x_i`) list only the locals live at `bb`'s entry;
  branch-local temporaries (`_2`, `_3`) are local to their predecessor handlers
  and out of scope at `bb3`.
- **RefinedRust (`rr_frontend/translation/src/environment/procedure.rs` and
  `proof_state.v` in Zenodo `21636474`):**
  Classifies multi-predecessor blocks as `JoinPoint`s, requires predecessor
  branches to re-establish a uniform live-local typing context at the jump, and
  caches the post-join weakest-precondition goal via `JCACHED` so the suffix
  from `bb3` is discharged once rather than $2^D$ times across $D$ chained
  diamonds.

In Anneal, expanding Stage 2 (`Trusted/`) to include SSA $\phi$-nodes, Coma
handlers, or liveness analyzers would violate the minimal-TCB principle
(`docs/architecture.md:315-398`). Instead, Stage 3 (`theory/Anneal/`) solves
both diamond joins and loops entirely outside `Trusted/`:

- **Mechanized Dead-Local Canonicalization (`canonicalize_join_unifies`):**
  In `support/VerifierEncodingComparison.lean` (Section 2), we formalize
  `diamondRaw`, prove `raw_diamond_join_states_ne` (`rawThenJoinState ≠
  rawElseJoinState`) and `asymmetric_storageDead_gen_mismatch`
  (`asymThenJoinState.locals = asymElseJoinState.locals ∧
  asymThenJoinState.localGens ≠ asymElseJoinState.localGens`), and define the
  Stage 3 canonicalization pass `canonicalizeLocals`. By equalizing dead
  temporaries across incoming join edges (coupled with finite-support spine
  normalization `canonLocalsUpTo` / `canonGensUpTo` or a live-local simulation
  relation `AgreeOnLive`), `canonicalize_join_unifies` proves that both branches
  arrive at `bb3` in the **exact same** `MirState` (`canonicalJoinStateAtBb3`),
  enabling a single shared suffix proof `execNormal_from_canonicalJoinState` in
  `execNormal_diamond_joined` while preserving return semantics
  (`canonicalize_preserves_return`).

### Axis 3: Generics, Trait Resolution, Associated Items, and PME Contracts

Basis: `source` + `normative` + `execution` + `derived`.

#### 1. Post-Monomorphization vs. Pre-Monomorphization vs. Hybrid PME Contracts

Rust's polymorphic features—type parameters (`T`), trait bounds
(`T: IntoBytes`), associated types (`T::Item`), associated constants
(`T::ALIGN`), and inline `const { assert!(...) }` blocks (RFC 2920, stabilized
in Rust 1.79)—create a sharp divide across verification tools:

- **Post-Monomorphization Only (Kani `9461e07a`):**
  Kani invokes `rustc`'s monomorphizer before translating MIR to CBMC Goto.
  Every type parameter, associated constant, and trait call is resolved to a
  concrete type, and any violated `const { assert!(...) }` block fails during
  compilation. However, Kani can only verify closed monomorphic test harnesses
  (`#[kani::proof]`), never an open polymorphic library theorem (`∀ T, ...`).
- **Pre-Monomorphization / Dictionary-Passing Only (Aeneas `21345f80`, Creusot
  `c4e9770a`, Verus `0141ebc6`):**
  Aeneas translates traits into explicit Lean 4 dictionary structures carrying
  associated types, associated constants, and method functions, verifying
  generic functions once for all dictionary instances. However, because pure
  functional translation erases runtime memory layouts (`size_of::<T>()`,
  `align_of::<T>()`), pre-monomorphization verifiers cannot directly model
  functions whose soundness is gated by a Post-Monomorphization Error (PME)—such
  as `zerocopy`'s `static_assert!(Src => Dst, size_of::<Src>() ==
  size_of::<Dst>())` (`google/zerocopy` at
  `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`), where the Rust signature has
  *no* trait bound relating `size_of::<Src>()` and `size_of::<Dst>()`, and
  instantiating `Src != Dst` sizes is rejected by `rustc` during
  monomorphization (`collect_and_partition_mono_items` in `rust-lang/rust` at
  `58cf8f9c35b355199727627d07ae34a4e2846d67`).
- **Anneal's Two-Stage Polymorphic PME Contract (`Trusted/MirSemantics.lean` at
  `572f1e80580daa4b052ce5646bb675484d9bb957`):**
  Anneal captures polymorphic MIR bodies containing `MirTy.param idx`, explicit
  type substitution `MirBody.subst typeArgs`
  (`Trusted/MirSemantics.lean:514-586`), and transitive constant dependencies
  `RequiresConst` over `requiredConsts` and `Terminator.call1` edges
  (`Trusted/MirSemantics.lean:641-681`). It enforces two complementary
  obligations:
  1. **`ConstsTotal adts body` (`Trusted/MirSemantics.lean:685-688`):** For
     *every* layout assignment `tySizes : Nat → Nat` and every reachable
     constant `c`, evaluating `c` either succeeds (`ConstSucceeds`, returning
     `MirVal.unit`) or cleanly panics at compile time (`ConstUnwinds`), never
     hitting `.failed` UB or a failed type substitution (`c = none`).
  2. **`MonoAdmitted adts tySizes body` (`Trusted/MirSemantics.lean:692-694`):**
     Acts as the admissibility guard inside `initMirState`
     (`Trusted/MirSemantics.lean:705`), restricting runtime execution to layout
     instantiations `tySizes` where every reachable `RequiresConst` evaluates to
     `ConstSucceeds`.

#### 2. Stage 2 `Trusted/MirAst.lean` Extensions for Generics and Traits

Inspecting `Trusted/MirAst.lean:38-282` and `Trusted/MirSemantics.lean:119-165`
at `572f1e80580daa4b052ce5646bb675484d9bb957` identifies three exact Stage 2
extensions required to scale beyond single-parameter `size_of` checks:

1. **Paired `(size, align)` Layout Environments (`tyLayouts : Nat → Layout`):**
   `Trusted/MirSemantics.lean:119-151` currently parameterizes `MirState` only
   by `tySizes : Nat → Nat` and provides `Terminator.callSizeOf`. While size
   equality suffices for by-value `transmute_copy`, the Rust Reference
   (`type-layout.md` and `behavior-considered-undefined.md` at
   `82da570bafd9efed421bdbae0f8603ede8dd308b`) requires every reference `&Dst` /
   `&mut Dst` to be aligned to `align_of::<Dst>()`. In
   `support/VerifierEncodingComparison.lean` (Section 3), we prove
   `size_only_insufficient_for_ref_transmute`: instantiating `Src = [u16; 2]`
   (`size = 4, align = 2`) and `Dst = u32` (`size = 4, align = 4`) at address
   `addr = 2` passes `sizeOnlyGate` (`4 == 4`) and source alignment (`2 % 2 ==
   0`), but violates destination alignment (`2 % 4 = 2 ≠ 0`). Adding
   `Terminator.callAlignOf` (or `Rvalue.nullaryOp .alignOf ty`) and `tyAligns`
   allows `refTransmuteGate` to enforce `dst.align ∣ src.align`, which
   `pme_ref_transmute_sound` proves sufficient for alignment preservation.
2. **Flat `BodyId` Call Targets and Trait Method Dispatch
   (`CallTarget.traitMethod`):**
   In `572f1e80580daa4b052ce5646bb675484d9bb957`, `Terminator.call1` embeds the
   callee `MirBody` inline (`call1 dst callee arg target typeArgs`), which
   prevents recursive functions and trait-bound calls whose concrete body is
   selected by a trait implementation. Replacing inline `MirBody` values with a
   flat `BodyId` index into `Crate.bodies` (as designed in
   `docs/architecture.md:202-220`) and adding `CallTarget.traitMethod traitId
   methodIdx selfTy typeArgs` resolved against verified `ImplDecl` dictionary
   entries enables modular trait verification without pre-monomorphizing
   callers.
3. **Const Generics and Associated Constants (`MirConst` / `ConstParam`):**
   Fixed-size arrays `[T; N]` and associated constants (`T::MAX_LEN`) require
   extending `MirTy` with `.array (elem : MirTy) (len : ConstExpr)` and
   `MirState` with `constParams : Nat → Nat` so `evalTyByteSize` can compute
   `len * sizeof(elem)` symbolically.

### Axis 4: Byte Representation, Padding, `MaybeUninit`, and `transmute`

Basis: `normative` + `source` + `execution` + `derived`.

#### 1. Abstract Bytes vs. Hybrid Structural + Byte-Count Representation

MiniRust (`spec/mem/basic.md`, `spec/lang/representation.md` at `d821c6e3`) and
RefinedRust/Caesium (`radium/val.v` in Zenodo `21636474`) represent every memory
location as a sequence of abstract bytes:

$$\text{AbstractByte} ::= \mathsf{Init}(b : \text{u8},\; p : \text{Option}\langle\text{Provenance}\rangle) \mid \mathsf{Uninit}$$

Storing a structured value `v : T` encodes `v` into `sizeof(T)` abstract bytes,
setting any inter-field or trailing padding offsets to $\mathsf{Uninit}$;
loading at type `U` decodes those bytes and triggers immediate UB if a scalar
integer, `bool`, enum discriminant, or reference reads an $\mathsf{Uninit}$ byte
(or if a non-byte load strips pointer provenance).

By contrast, Anneal (`Trusted/MirAst.lean:105-115` and
`Trusted/MirSemantics.lean:380-430` at
`572f1e80580daa4b052ce5646bb675484d9bb957`, extended in
`docs/architecture.md:225-248`) uses a hybrid value domain:

- Ordinary safe code manipulates structural `MirVal` trees (`.usize`, `.bool`,
  `.unit`, `.adt adtId fieldVals`, `.ref`, `.uninit`) with zero byte-slicing
  overhead.
- `AdtDecl` records `paddingBytes : Nat` (or explicit field byte offsets), and
  `evalTyByteSize` computes exact byte sizes by summing field sizes plus
  `decl.paddingBytes` (`Trusted/MirSemantics.lean:119-151`).
- `evalTransmuteCopy` (`Trusted/MirSemantics.lean:380-427`) factors
  transmutation into `extractTransmuteBits` (reading raw bits from `.usize`,
  `.bool`, `.unit`, or padding-free `.adt`, while rejecting `.ref` and
  `.uninit`) followed by `constructTransmuteVal` (reconstructing `.usize`,
  `.unit`, or `allFieldsPubSafe` `.adt` when `srcSize == dstSize`, while
  rejecting `.bool`, open `.param`, and `.ref`).

#### 2. Boundary Between Structural `MirVal.adt` and `AbstractByte` Masks

In `support/VerifierEncodingComparison.lean` (Section 4), we mechanize the exact
correspondence between Anneal's structural `paddingBytes` predicate and
MiniRust's `List AbstractByte` domain:

1. **Sufficiency of `paddingBytes == 0` for `IntoBytes`
   (`intoBytes_iff_paddingFree`):**
   When all fields of a struct are recursively initialized scalar/ADT values
   free of pointer provenance, its `List AbstractByte` encoding consists
   entirely of `AbstractByte.init b none` bytes if and only if
   `paddingBytes == 0` (`allBytesInit (encodeStructWithPadding b0 b2 b3
   padCount) = true ↔ padCount = 0`). For `zerocopy`'s `IntoBytes`, `FromZeros`,
   and `FromBytes` traits over fixed-width integers and `#[repr(C)]` /
   `#[repr(transparent)]` structs and arrays without padding, Anneal's
   structural `MirVal.adt` + `paddingBytes == 0` is sound and avoids per-byte
   reasoning.
2. **Failure of Padded Struct-to-Integer Transmutation
   (`padded_transmute_to_int_reads_uninit`):**
   When `paddingBytes > 0` (such as `#[repr(C)] struct Padded { a: u8, b: u16 }`
   with 1 padding byte at offset 1), transmuting `Padded` to `u32` fails closed
   (`decodeU32Bytes = none`) because byte 1 is `AbstractByte.uninit`, whereas
   transmuting `Padded` to `[MaybeUninit<u8>; 4]` succeeds
   (`decodeMaybeUninit4 = some bytes`).
3. **Constructs Requiring Byte-Mask or Bit-Range Representation:**
   Three Rust constructs cross the boundary where structural `MirVal.adt` +
   whole-struct `paddingBytes` is no longer sufficient:
   - **`MaybeUninit<T>` and Partial Byte Initialization:** Writing individual
     bytes into a `MaybeUninit<T>` buffer before calling `assume_init()`
     requires per-byte initialization tracking (`List AbstractByte` or a
     `(bits : Nat, initMask : Nat)` pair as in `MaskedWord64`).
   - **Sub-Byte / Sub-Word Bit-Validity (`bool`, `char`, `NonZero*`, and Niche
     Enums):** `constructTransmuteVal` in
     `572f1e80580daa4b052ce5646bb675484d9bb957` conservatively rejects
     transmuting arbitrary bits into `.bool` (`0` or `1` only) or non-`pub`-safe
     ADTs; supporting `zerocopy::TryFromBytes` requires bit-range validity
     predicates (`bits == 0 || bits == 1` for `bool`, `bits != 0` for
     `NonZero*`, and modular niche range checks for enums).
   - **Untagged `union` Overlays:** Writing to one union variant `u.a` and
     reading from an overlapping variant `u.b` of different field layout
     requires reinterpreting the underlying byte sequence at `u.b`'s field
     offsets, resetting any bytes outside the written variant's initialized
     footprint to `AbstractByte.uninit`.

## Boundaries

- **Verified by Mechanized Proofs (`support/VerifierEncodingComparison.lean`):**
  - Exact observational equivalence (`lens_prophecy_equiv`) between Stage 2
    operational path-lens mutation (`MirVal.refVal` + `writePlace`) and Stage 3
    functional backward-lens / prophetic composition across mutable field
    borrows and nested reborrows on `PairVal`.
  - Cross-frame mutable reference writeback (`cross_frame_ref_writeback_sound`),
    fail-closed rejection of escaping local references
    (`escaping_ref_fails_closed`), and clobbering of aliased functional backward
    lenses (`aliased_backward_lenses_clobber`).
  - Inequality of raw join states across diamond branches with unkilled
    branch-local temporaries (`raw_diamond_join_states_ne`), generation-counter
    skew under asymmetric `StorageDead` (`asymmetric_storageDead_gen_mismatch`),
    and state unification + return preservation under Stage 3
    `canonicalizeLocals` (`canonicalize_join_unifies`,
    `execNormal_diamond_joined`, `canonicalize_preserves_return`).
  - Insufficiency of size-only PME gates for reference transmutation
    (`size_only_insufficient_for_ref_transmute`) and soundness of alignment
    divisibility (`pme_ref_transmute_sound`).
  - Exact equivalence between `allBytesInit` and `padCount = 0`
    (`intoBytes_iff_paddingFree`) and fail-closed rejection of padded
    struct-to-`u32` transmutation (`padded_transmute_to_int_reads_uninit`).
- **Outside the Scope of the Mechanized Probe:**
  - `support/VerifierEncodingComparison.lean` models a self-contained core
    calculus isolating the four semantic boundaries; it does not import the full
    `Trusted` crate environment or execute `rustc` MIR capture directly.
  - Full Tree Borrows / Stacked Borrows dynamic tag trees for raw-pointer
    interior mutability (`UnsafeCell`) and multi-threaded weak-memory C11
    release/acquire fences beyond Anneal's `Memory.lean` view timestamps are
    analyzed architecturally but not re-mechanized in this package.

## Evidence

- **Anneal Primary Source Files (`joshlf/anneal`):**
  - `trusted/lean/Trusted/MirAst.lean:1-282` and
    `trusted/lean/Trusted/MirSemantics.lean:1-1150` at commit
    `572f1e80580daa4b052ce5646bb675484d9bb957` (`MirVal.ref`, `resolveRef`,
    `returnRefsOk`, `evalTyByteSize`, `extractTransmuteBits`,
    `constructTransmuteVal`, `ConstsTotal`, `MonoAdmitted`, `CrateTheorem`).
  - `theory/Anneal/MirLemmas.lean:513-605, 3749-3829` at commit
    `572f1e80580daa4b052ce5646bb675484d9bb957` (`ExecNormal`, `proveCrate`).
  - `docs/architecture.md:1-493`, `docs/design.md:1-282`, and
    `docs/trust-model.md:1-328` at commits
    `d79b0c070cf4115b523fe6ee62c1e72504de2254` and
    `be61ec573335d549398b5d2d0c5bea3ef25d0c1f` (three-stage MIR architecture,
    `PlaceElem`, `lowerBody`, `MirVal.uninit`).
  - `trusted/lean/Trusted/Memory.lean:1-228` and
    `theory/Anneal/FunctionalTranslation.lean:1-300` at commit
    `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0` (`MemState`, `LoanEntry`,
    `evalSym_sound`).
- **External Verifier Primary Sources:**
  - `AeneasVerif/charon` (`0.1.210`, `1e08453924610c19d74c245a7308f17c1008e2db`)
    and `AeneasVerif/aeneas` (`21345f80fa212c596f6437378d7d57984fa2ea77`:
    `compiler/InterpJoin.ml`, `compiler/InterpLoopsFixedPoint.ml`,
    `compiler/SymbolicToPure*.ml`, `backends/lean/Aeneas/Std/Primitives.lean`).
  - `creusot-rs/creusot` (`c4e9770ac1371ac4274bfe02145266d315c2fb86`:
    `creusot/src/translation/fmir.rs`, `creusot/src/backend/program.rs`,
    `creusot-contracts/src/ghost/perm.rs`).
  - RefinedRust Zenodo record `21636474` (`radium/loc.v`, `radium/val.v`,
    `radium/ghost_state.v`, `theories/refinedrust/lithium/interpreter.v`,
    `rr_frontend/translation/src/environment/procedure.rs`).
  - `verus-lang/verus` (`0141ebc6f14410dfc87fef1da57408578002eb7c`:
    `source/vstd/raw_ptr.rs`, `source/air/src/context.rs`).
  - `model-checking/kani` (`9461e07af7ec929f050aa4192f29363c9be07779`:
    `kani-compiler/src/codegen_cprover_gotoc/`).
  - `minirust/minirust` (`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`:
    `spec/mem/pointer.md`, `spec/mem/basic.md`,
    `spec/mem/tree_borrows/memory.md`, `spec/lang/representation.md`).
- **Report-Owned Mechanized and Validation Artifacts (`support/`):**
  - `support/VerifierEncodingComparison.lean` (`sha256:
    8507781228bda10f7aa5af7dd4970217c71d43ac58d778cc929c3ccef0238b78`, 853
    lines, 15 kernel-checked theorems across Axes 1–4, 0 `sorry`, 0 custom
    `axiom`s).
  - `support/verify_encoding_matrix.py` (standalone Python 3.10+ validator for
    the 7-verifier $\times$ 4-axis encoding matrix and Lean 4 static/kernel
    verification).

## Revalidation

Run the following commands from the report package directory to revalidate the
comparative Lean 4 formalization under both `leanprover/lean4:v4.28.0` and
`leanprover/lean4:v4.34.1` and check the structured encoding matrix:

```bash
# 1. Kernel-check VerifierEncodingComparison.lean under Lean v4.28.0 and v4.34.1
anneal-lean-run --mode file --concurrency 2 -- \
  elan run leanprover/lean4:v4.28.0 lean -DwarningAsError=true \
  support/VerifierEncodingComparison.lean

anneal-lean-run --mode file --concurrency 2 -- \
  elan run leanprover/lean4:v4.34.1 lean -DwarningAsError=true \
  support/VerifierEncodingComparison.lean

# 2. Run the automated 7-verifier x 4-axis matrix and Lean static/toolchain audit
python3 support/verify_encoding_matrix.py --run-lean --json
```

All three commands must exit with code `0`, reporting `"overall_ok": true`,
`"sorry_count": 0`, `"axiom_count": 0`, and `"overlong_lines": []`.
