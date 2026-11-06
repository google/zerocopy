# Hybrid Functional-Spatial Translation, Plan-Guided Shallow Embeddings, Finite-Heap Checkers, and Resource Adapters in Lean 4

## Summary

This report synthesizes six primary-source and Lean 4 prototype investigations covering hybrid functional-spatial program translation (`support/HybridBorrowHeapPrototype.lean`), plan-guided shallow functional embeddings (`support/ShallowPlanPrototype.lean`), kernel-verified finite-heap spatial derivation checkers (`support/Heap.lean`), reflection and resource-extension gates (`support/InvariantGate.lean`), constructive imperative refinement memory bridges (`cslib`, `lean-mlir`, `lean-llvm`, Aeneas, AutoCorres2, seL4, Cogent, VST, Cerberus), and resource-interpretation adapters (`support/Adapter.lean`, `support/HeapCore.lean`):

1. **Hybrid Functional-Spatial Translation (`support/HybridBorrowHeapPrototype.lean`, Lean `4.28.0` & `4.34.1`)**: Safe Rust places (`&T`, `&mut T`, local struct fields) and raw-pointer heap locations (`*const T`, `*mut T`, `UnsafeCell`) can be verified within a single Lean 4 obligation without forcing pure code through a global memory state or trusting an unverified boundary axiom. A two-zone state splits execution into a functional borrow zone (`BorrowState`, transformed by pure forward values and backward prophecy-free functions) and an explicit partial heap (`Heap := Nat → Option Int`, reasoned about via spatial predicates `ptsTo`, `sep`, and `wand`). Bridges occur only at explicit address-freezing (`freezeRefToRaw`) and raw-dereference (`thawRawToVal`) operations, each guarded by disjointness and ownership preconditions.
2. **Plan-Guided Shallow Functional Translation (`support/ShallowPlanPrototype.lean`, Lean `4.28.0` & `4.34.1`)**: Instead of verifying a deep-embedded compiler pass in Lean or trusting an external AST printer uncritically, an untrusted external planner emits a structured `TranslationPlan` (specifying place read/write paths, backward-function schedules, and loop fuel/invariant templates) that a small Lean 4 validator (`validatePlan`) checks against a typed intermediate representation (`MirStmt`) before producing a shallow functional specification (`evalShallow`). Soundness (`validatePlan_sound`) holds for every accepted plan (`validatePlan prog plan = some spec`), while malformed plans (stale borrow reads, unscheduled backward updates, mismatched write paths, or invalid loop exits) are rejected deterministically.
3. **Finite-Heap Spatial Derivation Checker (`support/Heap.lean`, Lean `4.30.0-rc2` & `4.34.1`)**: A 320-line reflective spatial derivation checker in Lean 4 (`CheckResult`, `CertStep`, `checkCert`, `checkCert_sound`) verifies separation-logic frame updates, multi-step pointer-chain traversals, and mutable-borrow restoration certificates via kernel-reducible `decide` / `rfl` evaluation. Across 10 benchmark fixtures (`support/fixture-results.json`), the checker accepts valid single-cell updates (`good-update.lean`) and 3-node chain traversals (`good-chain.lean`) and rejects 8 classes of soundness bugs (`missing-owned`, `overlap`, `damaged-frame`, `wrong-old`, `wrong-original`, `unlinked`, `out-of-domain`, `unknown`). Matched-cost measurement (`support/matched-costs.json`) shows data-certificate checking (`data-cost.lean`) requires 7 lines / 189 bytes of user proof text and 286 kernel WHNF steps vs. 31 lines / 984 bytes and 614 steps for direct hand-written heap-disjointness proofs (`direct-cost.lean`).
4. **Reflection Rewriting and Resource-Extension Gates (`support/InvariantGate.lean`, Lean `4.34.1`, and `iris-lean` `4ed71d6e`)**: Evaluates four architectural extension gates in Lean 4: (G1) when to retain pure Aeneas functional backward translation, (G2) when to introduce a reflective finite-heap checker (`Heap.lean`), (G3) when to add single-threaded shared-alias / `Cell` invariant gates (`support/InvariantGate.lean`, 148 lines, proving `cell_swap_preserves_sum_inv` and rejecting unguarded re-entrant alias writes), and (G4) when full step-indexed Iris (`iris-lean` `4ed71d6e54b58aa74f976fd00d62dfbe84eb2185` / Rocq Iris) is required for impredicative higher-order ghost state or concurrency.
5. **Constructive Imperative Refinement and Memory Bridges (9-system comparative source analysis)**: Audits how `cslib` (`5ebac2eb`), `lean-mlir` (`7b2d9a9b`), `lean-llvm` (`1f6ef26c`), Aeneas (`767c4eb9`), AutoCorres2 (`c05d67ab`), seL4 (`f3cefbe8`), Cogent (`8f1df80f`), VST (`1b1bf662`), and Cerberus (`c8c085d4`) structure the bridge between byte-level memory, typed heap views, and pure functional specifications. Identifies the exact soundness obligations required when lifting raw bytes to typed references (`align_ok`, `bounds_ok`, `init_ok`, `disjoint_ok`) and when composing functional lenses with spatial frames (`lens_frame_bridge`).
6. **Resource-Interpretation Adapters and Encoding Costs (`support/Adapter.lean`, `support/HeapCore.lean`, Lean `4.34.1`)**: Mechanizes bidirectional resource adapters (`PureBorrowPkg`, `FlatHeapSlice`, `IndexedPtsTo`, `liftPureBorrowToHeap`, `projectHeapToPureBorrow`) connecting pure functional borrow packages to spatial heap assertions (`support/adapter-results.json`). Quantifies term-size, proof-line, and kernel-checking overhead across pure functional, reflective certificate, and explicit spatial encodings (`support/encoding-costs.json`) alongside literature baselines from Aeneas (ICFP 2022), Gillian-Rust (PLDI 2025), RefinedC (PLDI 2021), CN (POPL 2023), and Diaframe (PLDI 2022).

---

## Applicability

| Component / Artifact | Repository / Local Path | Pinned Revision / Toolchain | Scope & Verification Status |
|---|---|---|---|
| Hybrid Borrow-Heap Prototype | `support/HybridBorrowHeapPrototype.lean` | Replayed on Lean `4.28.0` and `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | 248 lines; 8 machine-checked theorems (`zero sorry`, standard axioms only); 3 negative rejection tests in `support/hybrid-functional-spatial-translation/verification-results.json` |
| Plan-Guided Shallow Prototype | `support/ShallowPlanPrototype.lean` | Replayed on Lean `4.28.0` and `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | 276 lines; `validatePlan_sound` + positive/negative plan validation cases in `support/plan-guided-shallow-functional-translation/verification-results.json` |
| Finite-Heap Spatial Checker | `support/Heap.lean` + 10 fixtures (`support/*.lean`, `support/*.json`) | Replayed on Lean `4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `4.34.1` (`support/parent-lean434/fixture-results.json`) | `checkCert_sound` + 2 positive (`good-update`, `good-chain`) and 8 negative fixtures (`support/fixture-results.json`, `support/matched-costs.json`) |
| Invariant Gate Prototype | `support/InvariantGate.lean` | Replayed on Lean `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | 148 lines; proves `cell_swap_preserves_sum_inv` and `reentrant_double_open_rejected` (`support/observations.json`) |
| `iris-lean` (upstream snapshot) | `leanprover-community/iris-lean` | `4ed71d6e54b58aa74f976fd00d62dfbe84eb2185` | Inspected for `BI`, `OFE`/`CMRA`, `UPred`, `HeapView`, and MoSeL tactic overhead |
| Resource Interpretation Adapter | `support/Adapter.lean`, `support/HeapCore.lean` | Replayed on Lean `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | Proves `lift_project_roundtrip`, `hybrid_frame_adapter_sound`, and `slice_split_rejoin_sound` (`support/adapter-results.json`, `support/encoding-costs.json`) |
| Comparative Memory-Bridge Corpus | `cslib` (`5ebac2eb`), `lean-mlir` (`7b2d9a9b`), `lean-llvm` (`1f6ef26c`), `aeneas` (`767c4eb9`), `autocorres2` (`c05d67ab`), `seL4` (`f3cefbe8`), `cogent` (`8f1df80f`), `VST` (`1b1bf662`), `cerberus` (`c8c085d4`) | Pinned commit hashes in `REPORT.json` | Source-level comparative analysis of typed-heap liftings and refinement bridges |

---

## Findings

### 1. Hybrid Functional-Spatial Translation in Lean 4 (`support/HybridBorrowHeapPrototype.lean`)

**Basis: executable Lean 4 prototype and verification receipts (`support/HybridBorrowHeapPrototype.lean`, `support/hybrid-functional-spatial-translation/verification-results.json`, `support/hybrid-functional-spatial-translation/revalidate.py`).**

#### 1.1 Two-Zone State Architecture
Pure functional translation (as in Aeneas) eliminates spatial framing for safe Rust references (`&T`, `&mut T`), but breaks down when functions mix safe borrows with raw pointers (`*const T`, `*mut T`) or `UnsafeCell`. Conversely, translating all code into a monadic heap separation logic destroys pure equational simplicity for safe code.

`support/HybridBorrowHeapPrototype.lean` resolves this tension via a two-zone state `HybridState`:
- **Pure Borrow Zone (`BorrowState`)**: Holds safe value bindings and pure backward functions (` BorrowLoan : Int → Int`) representing open mutable borrows without heap addresses or global aliasing.
- **Spatial Heap Zone (`Heap := Nat → Option Int`)**: Holds address-taken and raw-pointer memory cells, equipped with disjoint union (`Heap.disjoint`, `Heap.union`) and spatial propositions (`HProp := Heap → Prop`, `ptsTo a v`, `sep P Q`, `wand P Q`, `pureProp φ`).

#### 1.2 Explicit Zone-Bridge Operations and Machine-Checked Theorems
Values cross between the pure borrow zone and the spatial heap zone only through two explicit bridge primitives:
1. **`freezeRefToRaw (v : Int) (back : Int → Int) (addr : Nat) (h : Heap)`**: Materializes a safe mutable borrow into a fresh heap address `addr` only when `h addr = none`, allocating `ptsTo addr v` in the spatial zone and recording a frozen restoration token `FrozenBorrow addr back`.
2. **`thawRawToPure (fb : FrozenBorrow) (h : Heap)`**: Consumes `ptsTo fb.addr v'` from the spatial heap, deallocating `fb.addr` (`Heap.erase h fb.addr`) and applying the pure backward function `fb.back v'` to restore the updated value in the pure borrow zone.

All 8 core theorems in `support/HybridBorrowHeapPrototype.lean` compile with zero `sorry` (`support/hybrid-functional-spatial-translation/verification-results.json`):

| Theorem | Verified Property |
|---|---|
| `pure_borrow_step_preserves_spatial_frame` | Any pure borrow update leaves the entire spatial `Heap` and any spatial assertion `P h` syntactically unchanged (`rfl`) |
| `spatial_step_preserves_pure_borrows` | Local heap mutation at `addr` under `sep (ptsTo addr v) Frame` preserves all pure borrow bindings and `Frame` |
| `freeze_thaw_roundtrip_sound` | Freezing a mutable borrow to a fresh raw pointer `addr`, mutating `*addr` via a verified spatial step `f`, and thawing `addr` produces the exact pure result `back (f v)` while restoring the external spatial frame `Frame` |
| `hybrid_wp_frame` | Compositional frame rule for `HybridWP` over the spatial zone without touching pure borrow variables |
| `hybrid_wp_bind` | Sequential composition (`bind`) for hybrid computations mixing pure backward steps and spatial mutations |
| `disjoint_raw_and_safe_borrow_commute` | A raw pointer write at `addr` and a safe mutable borrow update on local state commute with zero alias side conditions |
| `freeze_requires_fresh_addr` | Attempting to freeze a borrow onto an already-allocated address `h addr = some v0` is rejected (`freezeRefToRaw = none`) |
| `thaw_requires_matching_ownership` | Attempting to thaw a frozen borrow when `addr` is unmapped or owned by another frame fails (`thawRawToPure = none`) |

Three negative tests in `support/hybrid-functional-spatial-translation/verification-results.json` (`neg_overlapping_freeze`, `neg_use_after_thaw`, `neg_unowned_raw_write`) confirm that Lean rejects proof obligations when raw-pointer alias disjointness or thaw-consumption preconditions are violated.

---

### 2. Plan-Guided Shallow Functional Translation (`support/ShallowPlanPrototype.lean`)

**Basis: executable Lean 4 prototype and verification receipts (`support/ShallowPlanPrototype.lean`, `support/plan-guided-shallow-functional-translation/verification-results.json`, `support/plan-guided-shallow-functional-translation/revalidate.py`).**

#### 2.1 Architecture: Untrusted Translation Plan + Kernel-Checked Validator
Deeply embedding a full MIR-to-Lean compiler pass inside Lean requires proving compiler correctness over complex AST transformations, while an external OCaml/Rust translator (like Charon/Aeneas) enlarges the trusted computing base if its translation rules are unverified.

`support/ShallowPlanPrototype.lean` implements an intermediate architecture:
- **Source Language (`MirStmt`)**: An explicit statement representation supporting local assignments (`Assign`), field projections (`ProjRead`, `ProjWrite`), mutable borrows (`BorrowMut`), dereference writes (`DerefWrite`), borrow termination (`EndBorrow`), conditionals (`IfThenElse`), and bounded loops (`WhileLoop`).
- **Untrusted Certificate (`TranslationPlan`)**: A compact schedule instructing the shallow generator which pure state projection to read, when to synthesize a backward function `back`, and in what order to close active loans (`LoanId`) at join points and function exit.
- **Kernel-Checked Validator (`validatePlan : List MirStmt → TranslationPlan → Option ShallowFn`)**: Checks at translation/elaboration time that:
  1. No borrowed source place is read or written directly while an active mutable loan (`activeLoans`) covers an overlapping path (`pathOverlaps`).
  2. Every `DerefWrite` targets an active `LoanId`.
  3. Every active loan is closed (`EndBorrow`) in LIFO/disjoint order before its underlying root variable is observed or returned.
  4. Both branches of `IfThenElse` close identical loan sets at the join point.

#### 2.2 Soundness and Negative Rejection Results
- **`validatePlan_sound` (`ShallowPlanPrototype.lean:198–246`)**: Proves that for any statement sequence `stmts` and `plan`, if `validatePlan stmts plan = some shallowFn` and the operational reference semantics `evalMir stmts env` succeeds with zero active loans remaining, then `shallowFn env` produces the exact same final environment (`evalMir stmts env = some (shallowFn env)`).
- **Verified positive and negative fixtures (`support/plan-guided-shallow-functional-translation/verification-results.json`)**:
  - **Accepted (`pos_two_field_split_borrow`, `pos_reborrow_chain`, `pos_branch_join_borrow`)**: Disjoint struct-field borrows (`x.fst` and `x.snd`), nested reborrows, and branch-uniform borrow endings validate via `rfl` and reduce to pure Lean functions.
  - **Rejected (`neg_read_while_mut_borrowed`, `neg_unclosed_loan_at_exit`, `neg_overlapping_field_borrow`, `neg_branch_loan_mismatch`)**: `validatePlan` returns `none` when a plan attempts to read a mutably borrowed root, leaves a loan open at exit, borrows overlapping paths, or closes a loan in only one conditional branch.

---

### 3. Finite-Heap Spatial Derivation Checker (`support/Heap.lean`)

**Basis: executable Lean 4 checker and 10 fixture receipts (`support/Heap.lean`, `support/check_fixtures.py`, `support/fixture-results.json`, `support/matched-costs.json`, `support/parent-lean434/fixture-results.json`).**

#### 3.1 Reflective Spatial Certificate Calculus
For verification obligations that require explicit heap reasoning over finite pointer graphs, manual application of associativity/commutativity lemmas for separating conjunction (`sep_assoc`, `sep_comm`) creates quadratic proof scripts. `support/Heap.lean` replaces manual permutation tactics with a kernel-checked reflective derivation checker:
- **Heap and Atoms**: A finite map `FinHeap` of typed cells `(addr : Nat, val : Nat)` and borrow tags (`Owned addr val`, `Borrowed id addr cur orig`, `Linked src dst`).
- **Certificate Steps (`CertStep`)**:
  - `WriteOwned addr newVal`: updates `Owned addr oldVal` to `Owned addr newVal`.
  - `WriteBorrowed id newVal`: updates `Borrowed id addr oldVal orig` to `Borrowed id addr newVal orig`.
  - `EndBorrow id`: restores `Owned addr cur` from `Borrowed id addr cur orig` while recording the pure backward equation `cur = f orig`.
  - `FollowLink src dst`: witnesses a pointer hop from `src` to `dst` when `Linked src dst` and `Owned dst v` are present.
- **Soundness Theorem (`checkCert_sound`, `support/Heap.lean:245–298`)**: If `checkCert pre post steps = CheckResult.ok` and `interpSpatial pre h` holds on concrete heap `h` (including pairwise address disjointness and borrow coherence), then executing the concrete memory trace yields `h'` satisfying `interpSpatial post h'` with all untouched frame cells preserved identically.

#### 3.2 Complete 10-Fixture Matrix and Matched-Cost Comparison
Verified identically under both Lean `4.30.0-rc2` (`support/fixture-results.json`) and Lean `4.34.1` (`support/parent-lean434/fixture-results.json`):

| Fixture (`support/<name>.lean` / `.json`) | Expected Status | Actual Checker Result (`CheckResult`) | Failure / Acceptance Mechanism |
|---|---|---|---|
| `good-update` | Accept | `CheckResult.ok` (compiled `0`) | Valid borrow creation, write, and restoration preserving disjoint frame |
| `good-chain` | Accept | `CheckResult.ok` (compiled `0`) | Valid 3-node linked-list hop traversal and tail update preserving head/middle frame |
| `missing-owned` | Reject | `error "missing owned cell"` (exit `1` on `rfl` proof) | Attempts to write to an address not present in the spatial precondition |
| `overlap` | Reject | `error "duplicate address in precondition"` | Precondition contains two spatial atoms claiming the same physical address |
| `damaged-frame` | Reject | `error "postcondition frame mismatch"` | Postcondition alters a frame cell that was never modified by any `CertStep` |
| `wrong-old` | Reject | `error "stale old value"` | Postcondition claims the wrong pre-mutation value in a history atom |
| `wrong-original` | Reject | `error "modified borrow origin"` | Step alters the immutable `orig` snapshot recorded when the borrow began |
| `unlinked` | Reject | `error "missing link edge"` | `FollowLink` step traverses a pointer edge absent from the spatial graph |
| `out-of-domain` | Reject | `error "borrow id not found"` | `EndBorrow` references a non-existent or already-closed borrow identifier |
| `unknown` | Reject | `error "unresolved symbolic atom"` | Pre/post contains an uninstantiated atom outside the decidable finite fragment |

In the matched-cost experiment on the same 3-cell framed borrow-update obligation (`support/matched-costs.json`, `support/measure.py`):
- **Reflective Certificate (`support/data-cost.lean`)**: 7 lines, 189 bytes, `by decide` (1 tactic invocation), 286 kernel WHNF reduction steps.
- **Direct Hand-Written Proof (`support/direct-cost.lean`)**: 31 lines, 984 bytes, 14 tactic steps (`simp`, `omega`, `funext`, `split`), 614 kernel WHNF reduction steps.

---

### 4. Reflection Rewriting and Resource-Extension Gates (`support/InvariantGate.lean`)

**Basis: executable Lean 4 gate prototype and `iris-lean` comparison (`support/InvariantGate.lean`, `support/observations.json`, `support/reflection-rewriting-and-resource-extension-gates/evidence.json`).**

To prevent premature escalation to heavyweight separation-logic encodings when verifying Rust in Lean 4, `support/InvariantGate.lean` and `support/observations.json` establish a four-tier escalation gate:

| Gate Tier | Target Rust Pattern | Mechanized Substrate | Escalation Trigger to Next Tier |
|---|---|---|---|
| **Tier 1: Pure Functional (Aeneas LLBC)** | Exclusive `&mut T`, shared `&T`, algebraic data types, acyclic borrows | Pure Lean functions (`s → (a × s)`) and backward functions | Presence of raw pointers (`*mut T`), pointer aliasing across unknown offsets, or interior mutability (`UnsafeCell` / `Cell`) |
| **Tier 2: Reflective Finite-Heap Checker (`support/Heap.lean`)** | Bounded raw-pointer graphs, doubly-linked nodes, explicit disjoint slice splits | `FinHeap` + `checkCert_sound` (`by decide`) | Shared alias mutation through an invariant (e.g., two `&Cell<i32>` references governed by a relational invariant) |
| **Tier 3: Mask-Gated Local Invariant (`support/InvariantGate.lean`)** | Single-threaded shared interior mutability (`Cell<T>`, `RefCell<T>`) with open/close mask tracking | `InvMask` (bitset of open invariant IDs), `openInv`, `closeInv`, `cell_swap_preserves_sum_inv` | Concurrent threads (`Atomic*`, `Send`/`Sync`), higher-order stored predicates, or impredicative protocol recursion |
| **Tier 4: Full Step-Indexed Iris (`iris-lean` / Rocq Iris)** | Concurrent lock-free atomics, recursive ghost state, life-shortening impredicative borrows | `UPred M`, `CMRA`, step-indexed `▷`, fancy updates `\|={E1,E2}=>` | N/A (general-purpose foundation) |

In `support/InvariantGate.lean` (replayed on Lean `4.34.1`, exit `0`, zero `sorry`):
- `InvState` tracks a physical cell map alongside an active mask `openSet : List InvId` and a relational invariant `invRel : CellMap → Prop`.
- `cell_swap_preserves_sum_inv` (`InvariantGate.lean:88–119`) proves that opening invariant `0`, transferring `delta` between two aliased or distinct `Cell` locations `c1` and `c2` while temporarily violating `c1 + c2 = K`, and closing invariant `0` after restoring `c1 + c2 = K` succeeds and preserves the global invariant.
- `reentrant_double_open_rejected` (`InvariantGate.lean:122–146`) proves that attempting to re-open an already-open invariant ID (`id ∈ s.openSet`) returns `GateResult.err .reentrantOpen`, blocking the classic re-entrant aliasing unsoundness of unguarded `Cell`/`RefCell` access without requiring step-indexing.

---

### 5. Constructive Imperative Refinement and Memory Bridges (9-System Comparative Analysis)

**Basis: source inspection across `cslib`, `lean-mlir`, `lean-llvm`, Aeneas, AutoCorres2, seL4, Cogent, VST, and Cerberus (`REPORT.json`).**

#### 5.1 Comparative Memory-Model and Typed-Lifting Taxonomy
Across the nine inspected verification ecosystems, bridging low-level byte arrays to typed algebraic or spatial representations decomposes into four explicit architectural patterns:

| System & Pinned Revision | Low-Level Memory Representation | Typed Lifting / Bridge Mechanism | Key Soundness Side Conditions |
|---|---|---|---|
| **AutoCorres2 (`c05d67ab`) & seL4 (`f3cefbe8`)** | Flat byte-addressed `heap_mem` (`addr → word8`) with `typ_uinfo` tags | `lift_global_heap` / `heap_typing_fold`: projects flat bytes into per-type partial heaps (`t_hrs`) for disjointly typed regions | `c_guard p` (non-null, aligned `align_td`, no address-space wraparound) and valid type footprint tag in `hrs_htd` |
| **Cogent (`8f1df80f`)** | Dual semantics: pure functional value semantics (`Val`) + C heap semantics (`UpdateSemantics`) | Linear uniqueness types guarantee every mutable record has a single active pointer; refinement connects `UpdateSemantics` to `ValueSemantics` via a frame relation | Linear uniqueness typing (`splitting`/`sharing` context rules) + absence of aliasing between active linear pointers |
| **Aeneas (`767c4eb9`)** | LLBC symbolic values (`SymbolicValue`, `Loan`, ` Borrow` projectors) | Pure functional backward translation (`primitives.lean`): eliminates memory addresses altogether for safe Rust | Absence of raw-pointer arithmetic, `union` type punning, and unstructured interior mutability outside axiomatized primitives |
| **Princeton VST (`1b1bf662`)** | CompCert `Mem.mem` lifted to step-indexed `rmap` (`veric/juicy_mem.v`) | `mapsto sh t p v` and `data_at sh t v p` (`floyd/field_at.v`): decomposes C struct/array layouts via `field_compatible t gfs p` | `size_compatible`, `align_compatible`, `legal_nested_field`, and fractional share validity (`readable_share` / `writable_share`) |
| **Cerberus (`c8c085d4`)** | PNVI-ae-udi / VIP provenance-aware allocation map (`mem_state`: `alloc_id ↦ object` + byte array) | Core intermediate language with explicit `kill`, `create`, `store`, `load`, and pointer-provenance operations | Allocation liveness, in-bounds offset, matching provenance `alloc_id`, and initialization status (`unspecified` vs. initialized bytes) |
| **`lean-mlir` (`7b2d9a9b`) & `lean-llvm` (`1f6ef26c`)** | Dialect-parameterized SSA regions (`Com`, `Denote`) and LLVM bitvector/memory state (`LLVM.MemState`) | Monadic refinement `Refines` over poison/UB-aware `BitVec` and block-indexed memory | Explicit poison propagation and in-bounds block-offset checks before reducing memory reads/writes to pure `BitVec` terms |
| **`cslib` (`5ebac2eb`)** | Transition systems (`LTS`) and simulation/bisimulation hierarchies in Lean 4 | Compositional forward/backward simulation relations | Preserving initial states and step transitions across abstract and concrete state types |

#### 5.2 Four Mandatory Byte-to-Typed Lifting Obligations and Lens-Frame Composition
Synthesizing these systems shows that any sound bridge in Lean 4 that lifts a raw byte slice or pointer `(base, len)` into a typed value `v : T` (or a pure borrow lens `Lens S T`) must discharge four non-negotiable obligations before entering the pure or typed spatial zone:
1. **Alignment (`align_ok`)**: `base % alignOf T = 0`.
2. **Bounds and Non-Wraparound (`bounds_ok`)**: `len = sizeOf T` and `base + len ≤ USize.max`.
3. **Initialization & Validity (`init_ok`)**: Every non-padding byte in `[base, base + len)` is initialized and the decoded bit pattern satisfies `ValidBitPattern T` (critical for `bool`, enums, references, and `NonNull`).
4. **Disjoint Frame Isolation (`disjoint_ok` / `lens_frame_bridge`)**: While the lifted value is borrowed in the pure zone (`BorrowLoan`), the spatial footprint `[base, base + len)` is removed from the active spatial heap (or frozen read-only) so no concurrent raw write can invalidate the pure value before the backward function restores it. Given disjoint spatial frames `FrameA` and `FrameB`, composing a pure lens `L : Lens T Field` on a frozen footprint `ptsToSlice base T` preserves `FrameA * FrameB` without re-checking byte-level layout for `FrameA` or `FrameB`.

---

### 6. Resource-Interpretation Adapters and Encoding Costs (`support/Adapter.lean`, `support/HeapCore.lean`)

**Basis: executable Lean 4 adapter proofs and cost measurements (`support/Adapter.lean`, `support/HeapCore.lean`, `support/adapter-results.json`, `support/encoding-costs.json`, `support/resource-interpretation-adapters-and-encoding-costs/publication-normalization.json`).**

#### 6.1 Verified Resource-Interpretation Adapters (`support/Adapter.lean`)
Different verification modules within a single project often represent the same memory state in three incompatible formats:
- **Representation A (`PureBorrowPkg`)**: A pure value `(cur : Nat, orig : Nat, back : Nat → Nat)` used by Aeneas-style functional specifications.
- **Representation B (`FlatHeapSlice`)**: A contiguous byte/word list `(base : Nat, words : List Nat)` used by slice and serialization specs.
- **Representation C (`IndexedPtsTo`)**: An address-indexed partial map `Nat → Option Nat` with separating conjunction used by pointer-graph specs.

`support/HeapCore.lean` and `support/Adapter.lean` (replayed on Lean `4.34.1`, exit `0`, zero `sorry`, `support/adapter-results.json`) mechanize lossless adapters between all three representations:
- `liftPureBorrowToHeap` and `projectHeapToPureBorrow`, accompanied by `lift_project_roundtrip` (`Adapter.lean:74–96`), proving that lifting a pure borrow package into a singleton heap cell at `addr`, applying an in-place heap update, and projecting back equals applying the pure update directly.
- `sliceToPtsToMap` and `ptsToMapToSlice`, accompanied by `slice_split_rejoin_sound` (`Adapter.lean:102–148`), proving that splitting a contiguous `FlatHeapSlice` at index `k` into two disjoint `IndexedPtsTo` sub-heaps (`h_left ⊥ h_right`), mutating `h_left`, and rejoining yields `words.take k` (updated) ++ `words.drop k`.
- `hybrid_frame_adapter_sound` (`Adapter.lean:152–189`), proving that an adapter roundtrip on a sub-heap `h_local` preserves any disjoint spatial frame `h_frame` (`HeapCore.Disjoint h_local h_frame`).

#### 6.2 Quantitative Encoding-Cost Comparison (`support/encoding-costs.json`)
Measured on Lean `4.34.1` across equivalent local update and frame-preservation obligations (`support/encoding-costs.json`):

| Encoding Strategy in Lean 4 | Representative Artifact | User Proof Size (Lines / Bytes) | Tactic / Kernel Check Profile | Best-Fit Domain |
|---|---|---|---|---|
| **Pure Functional Borrow (`PureBorrowPkg`)** | `support/ShallowPlanPrototype.lean` / `support/Adapter.lean` | 3–5 lines / ~120 B | `rfl` / `simp` (zero heap disjointness side conditions) | Safe Rust (`&T`, `&mut T`), algebraic data types, acyclic borrows |
| **Reflective Finite-Heap Certificate (`CertStep`)** | `support/Heap.lean` (`support/data-cost.lean`) | 7 lines / 189 B | `by decide` (286 WHNF steps; linear pass over finite atom list) | Bounded pointer hops, local unsafe node splices, fixed-arity slice splits |
| **Adapter-Bridged Hybrid Zone (`HybridState`)** | `support/HybridBorrowHeapPrototype.lean` / `support/Adapter.lean` | 12–16 lines / ~410 B | 4–6 tactic steps (1 bridge lemma + pure `simp`) | Functions encapsulating a local raw-pointer/slice operation inside a safe Rust signature |
| **Direct Spatial Heap Proof (`IndexedPtsTo`)** | `support/direct-cost.lean` | 31 lines / 984 B | 14 tactic steps (`omega`, `funext`, case splits; 614 WHNF steps) | Unbounded pointer graphs or custom spatial predicates not covered by `CertStep` |

These local Lean 4 measurements align with published multi-system comparisons normalized in `support/resource-interpretation-adapters-and-encoding-costs/publication-normalization.json`:
- **Aeneas (ICFP 2022, DOI `10.1145/3547647`)**: Eliminates spatial framing entirely for safe Rust by translating borrows to pure backward functions.
- **Gillian-Rust (PLDI 2025, DOI `10.1145/3729289`)**: Combines a hybrid symbolic heap (spatial tree-block memory + pure prophecy-enabled borrow tokens) to avoid spatial unfolding on safe borrows while retaining layout precision for `unsafe` code.
- **RefinedC (PLDI 2021, DOI `10.1145/3453483.3454036`) & Diaframe (PLDI 2022, DOI `10.1145/3519939.3523432`)**: Automate Iris separation-logic framing via syntax-directed goal rules (`liRStep` / bi-abductive hints), at the cost of requiring foundational Rocq proof terms for every step.
- **CN (POPL 2023, DOI `10.1145/3571207`)**: Uses explicit let-normalized resource terms with SMT discharge of pure constraints rather than interactive separation-logic tactics.

---

## Boundaries

1. **Prototype Scope vs. Full Rust MIR**: `support/HybridBorrowHeapPrototype.lean`, `support/ShallowPlanPrototype.lean`, `support/Heap.lean`, `support/InvariantGate.lean`, and `support/Adapter.lean` are self-contained, machine-checked Lean 4 models over integer/natural-number values and finite heaps. They do not parse full `rustc` MIR or Charon ULLBC/LLBC JSON directly.
2. **Single-Threaded & First-Order Restriction**: The reflective finite-heap checker (`support/Heap.lean`) and mask-gated cell invariant (`support/InvariantGate.lean`) handle deterministic single-threaded execution and first-order heap predicates. Concurrent atomics, thread spawning, and higher-order impredicative invariants require full step-indexed Iris (`iris-lean` + a `program_logic` layer).
3. **Byte-Level Alignment & Padding**: While `support/Adapter.lean` mechanizes word-slice splitting and joining (`FlatHeapSlice`), full sub-word bitfields, uninitialized padding bytes, and provenance-tagged pointer casts (as in Cerberus VIP/PNVI-ae-udi) are not yet mechanized inside `Adapter.lean`.
4. **Comparative Corpus**: The 9 external repositories in Section 5 (`cslib`, `lean-mlir`, `lean-llvm`, Aeneas, AutoCorres2, seL4, Cogent, VST, Cerberus) were inspected at their pinned commits for architectural synthesis and were not built or executed in this workspace.

---

## Evidence

All Lean 4 source files, revalidation scripts, compiler outputs, and JSON receipts are stored in `support/`:

- **Hybrid Functional-Spatial Translation (`2026-10-29`)**:
  - `support/HybridBorrowHeapPrototype.lean` (also `support/hybrid-functional-spatial-translation/HybridBorrowHeapPrototype.lean`)
  - `support/hybrid-functional-spatial-translation/verification-results.json` and `support/hybrid-functional-spatial-translation/revalidate.py`
- **Plan-Guided Shallow Functional Translation (`2026-10-29`)**:
  - `support/ShallowPlanPrototype.lean` (also `support/plan-guided-shallow-functional-translation/ShallowPlanPrototype.lean`)
  - `support/plan-guided-shallow-functional-translation/verification-results.json` and `support/plan-guided-shallow-functional-translation/revalidate.py`
- **Finite-Heap Spatial Derivation Checker**:
  - `support/Heap.lean`, `support/check_fixtures.py`, `support/measure.py`, `support/fixture-results.json`, `support/matched-costs.json`, `support/parent-lean434/fixture-results.json`
  - Fixtures and logs: `support/good-update.lean`, `support/good-chain.lean`, `support/missing-owned.lean`, `support/overlap.lean`, `support/damaged-frame.lean`, `support/wrong-old.lean`, `support/wrong-original.lean`, `support/unlinked.lean`, `support/out-of-domain.json`, `support/unknown.json`, `support/data-cost.lean`, `support/direct-cost.lean` (plus `.stdout`/`.stderr` logs and `support/finite-heap-spatial-derivation-checker/`)
- **Reflection Rewriting and Resource-Extension Gates (`2026-10-14`)**:
  - `support/InvariantGate.lean`, `support/InvariantGate.stdout`, `support/InvariantGate.stderr`, `support/observations.json`, `support/README.md` (and `support/reflection-rewriting-and-resource-extension-gates/`)
- **Resource-Interpretation Adapters and Encoding Costs**:
  - `support/Adapter.lean`, `support/HeapCore.lean`, `support/adapter.stdout`, `support/adapter.stderr`, `support/core.stdout`, `support/core.stderr`, `support/adapter-results.json`, `support/encoding-costs.json`
  - `support/resource-interpretation-adapters-and-encoding-costs/publication-normalization.json`, `support/resource-interpretation-adapters-and-encoding-costs/coverage.json`, `support/resource-interpretation-adapters-and-encoding-costs/evidence.json`

---

## Revalidation

1. **Hybrid Borrow-Heap & Plan-Guided Shallow Prototypes**:
   - Run `lean support/HybridBorrowHeapPrototype.lean` and `lean support/ShallowPlanPrototype.lean` (or `python3 support/hybrid-functional-spatial-translation/revalidate.py` and `python3 support/plan-guided-shallow-functional-translation/revalidate.py`) and confirm exit code `0` for both positive files and expected failure on all negative test harnesses.
2. **Finite-Heap Spatial Checker & 10 Fixtures**:
   - Run `python3 support/check_fixtures.py` and `python3 support/measure.py`:
     - Verify `support/Heap.lean`, `support/good-update.lean`, `support/good-chain.lean`, `support/data-cost.lean`, and `support/direct-cost.lean` exit with code `0`.
     - Verify all 8 negative fixtures (`missing-owned`, `overlap`, `damaged-frame`, `wrong-old`, `wrong-original`, `unlinked`, `out-of-domain`, `unknown`) fail kernel checking as recorded in `support/fixture-results.json`.
3. **Invariant Gate & Resource Adapters**:
   - Run `lean support/InvariantGate.lean`, `lean support/HeapCore.lean`, and `lean support/Adapter.lean` and confirm exit code `0` with zero `sorry` warnings (`support/adapter-results.json`, `support/observations.json`).
