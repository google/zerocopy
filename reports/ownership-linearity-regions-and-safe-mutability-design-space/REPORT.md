# Ownership, Linearity, Regions, and Safe Mutability Design Space

## Summary

Static memory safety and data-race freedom span four largely orthogonal axes beyond Rust's affine per-node borrow checker (`aliasing XOR mutability` over trees), verified across 13 peer-reviewed papers and 7 pinned upstream repositories:

1. **Exclusivity Granularity (Per-Node Trees vs. Isolated Regions & Branded Tokens)**: Strict per-node exclusive ownership is isomorphic to an acyclic forest (in-degree $\le 1$) and rejects cyclic rings and mutable DAGs. Lexical stack regions (**Tofte–Talpin/MLKit**, **Cyclone**) lift cycles into arenas at the cost of LIFO lifetime bloat; **GhostCell** separates shared topology from a rank-2 branded `GhostToken<'id>` for zero-overhead sequential graph mutation; **Project Verona** (**Reggio** + **Behaviour-Oriented Concurrency**) elevates isolation to a forest of linearly owned *regions* with swappable bridge objects (`iso`), permitting arbitrary internal cyclic mutation inside a single thread-local *window of mutability*, pluggable per-region memory management (`Trace`, `Arena`, `Rc`) with zero atomic RC, and deadlock-free multi-region transactions via 2PL-ordered `cowns`.
2. **Reference First-Classness (Second-Class Projections vs. `~Escapable` References)**: **Mutable Value Semantics (MVS)** (**Hylo**, early **Swift**) bans shared mutable state via second-class `let`/`inout`/`set`/`sink` parameter conventions and yield-once coroutine subscripts (`project`/`end_project`). Both **Hylo** (`Docs/RemoteParts.md`) and **Swift** (`SE-0377` $\to$ `SE-0390` $\to$ `SE-0427` $\to$ `SE-0446` $\to$ `SE-0447` $\to$ `SE-0467` $\to$ `SE-0519`) hit expressive walls on stored views, slices, and iterators, converging back toward bounded **nonescapable (`~Escapable`) first-class references** (`Span`, `MutableSpan`, `Ref`, `MutableRef`) carrying lifetime dependencies.
3. **Consumption Obligation (Affine Drop vs. Must-Linearity vs. Arrow Multiplicities)**: **Affine** ownership (Rust `Drop`, safe `mem::forget`) enforces *at-most-once* use but cannot statically require explicit protocol discharge across early returns or panic unwinding. Type-based must-linearity (**Austral**) enforces *exactly-once* consumption via a 4-state table, branch-identical exits, and loop-depth reassignment tracking—at the price of banning exceptions (`abort` calls `_Exit(-1)`), closures, and implicit destructors (while still making `WriteRef`/`SpanMut` implicitly droppable in `LinearityCheck.ml`). Arrow-based linearity (**Linear Haskell**) avoids splitting container libraries via multiplicity polymorphism (`A ->_p B`), but its lazy linearity guarantee holds only *conditionally* on complete evaluation of the result and collapses vacuously under divergence or imprecise exceptions.
4. **Aliasing Discipline (Borrow Graphs vs. Deny Reference Capabilities)**: Borrow graphs (**Polonius** 9-rule Datalog; **Place Capability Graphs** covering 97.7% of functions across 491 public Rust crates) capture path-sensitive loans and function/loop summaries without altering concurrency models. **Pony**'s 6-capability deny matrix (`iso`/`trn`/`ref`/`val`/`box`/`tag`) provides lifetime-free actor data-race freedom, at the cost of complex viewpoint adaptation (which evolved from AGERE! 2015 to modern `ponyc` on `(iso, trn)`, `(iso, ref)`, `(trn, ref)`), non-monotonic `cap_safetomove` under subtyping (`trn <: box`), and open generic-capability soundness issues (`ponyc#1931`).

All algebraic, region-framing, and linearity invariants are mechanically checked by [support/verify_ownership_paradigms.py](support/verify_ownership_paradigms.py).

## Applicability

This report maps static ownership, region, linearity, mutable-value-semantics, and reference-capability systems **beyond** Rust's intraprocedural borrow checker alone. Its 20 subjects in `REPORT.json` (13 papers and 7 pinned GitHub repositories) form a four-pillar cross-paradigm comparison: (1) Tofte–Talpin/MLKit, Cyclone, `rust-lang/polonius`, Place Capability Graphs, and GhostCell; (2) Racordon et al. MVS, `hylo-lang/hylo`, and `swiftlang/swift-evolution` (`SE-0377` through `SE-0519`); (3) `austral/austral` and Linear Haskell; and (4) Pony (Clebsch et al. '15 and `ponylang/ponyc`) and Project Verona (Arvidsson et al. '23, Cheeseman et al. '23, `microsoft/verona-rt`, and `microsoft/verona`).

**Cross-referenced corpus packages (not duplicated here)**:
- Rust operational aliasing models (Stacked Borrows, Tree Borrows, MiniRust, LLVM `noalias`, `UnsafeCell` protectors): `rust-aliasing-models-stacked-tree-minirust-and-llvm-attributes`.
- Rust semantic soundness (Iris/RustBelt) and deductive ownership verifiers (RustHornBelt, RefinedRust, Verus, Creusot): `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`.
- Language-isolated kernels, Calculus of Capabilities, $L^3$, Sing#, Metal, and Typechain: `metal-typechain-language-isolated-kernels-1995-2026`.
- Symbolic borrow translation and Rust frontend verification: `aeneas-borrows-symbolic-ownership-and-resource-semantics` and `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering`.

**Version specificity**: Repository claims apply strictly to the pinned 40-character commit SHAs in `REPORT.json`. Version divergences preserved explicitly below include Pony's viewpoint-adaptation upgrade between AGERE! 2015 and `ponylang/ponyc` (`b2d900f328`), and Swift's phased ownership rollout across Swift 5.9 (`SE-0377`/`SE-0390`), 6.0 (`SE-0427`/`SE-0429`), 6.2 (`SE-0446`/`SE-0447`/`SE-0467`), and 6.4 (`SE-0519`).

## Findings

### 1. Cross-Paradigm Design-Space Matrix

Basis: normative + source + documentation + derived

| System / Paradigm | Exclusivity Unit | Consumption Discipline | First-Class Refs / Lifetimes | Safe Cyclic Mutable Graphs | Multi-Thread DRF | Primary Wall or Failure Mode |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Tofte–Talpin / MLKit** (1994–97) | Lexical LIFO region stack | Unrestricted (inferred regions) | Implicit inferred region params | Yes (within region) | Sequential | Tail-recursion region-endomorphism space leaks without `atbot` reuse |
| **Cyclone** (2002–06) | Lexical + dynamic regions + unique/RC ptrs | Affine unique ptrs; bulk regions | Explicit `'r` ptrs + `<'r>` existentials | Yes (within region) | Sequential base | Annotation overhead; dynamic regions require explicit `open` + key threading |
| **Rust NLL / Polonius / PCG** (2018–25) | Per-node place tree (`&mut`) + loans | Affine (`Drop`, safe `mem::forget`) | First-class `&'a T`, `&'a mut T` | No without `unsafe`, `Rc<RefCell>`, indices, or `GhostCell` | Yes (`Send`/`Sync` + AXM) | Cyclic graphs, `Pin<P>` self-refs, interprocedural partial borrows, loop reborrows |
| **GhostCell** (ICFP '21) | Branded cell group (`GhostToken<'id>`) | Affine token + shared `&GhostCell` | Rank-2 invariant `'id` | Yes (sequential via `&mut GhostToken`) | Yes (parallel `&GhostToken` reads) | No simultaneous `iter_mut`; single token serializes disjoint subgraphs; external free |
| **Hylo (MVS)** (`6889158246`) | Value tree + second-class accesses | Affine/linear IR registers (`sink`, `deinit`) | Second-class `yield` projections; `remote` parts in design | No (indices / escape) | Value independence | Stored slices require `remote` parts; coroutine lowering hurts `mem2reg`; no cycles |
| **Swift 5.9–6.4** (`6385c2aee6`) | Value exclusivity (`SE-0176`) + `~Copyable`/`~Escapable` | Affine `~Copyable` + `deinit` / `discard self` | Evolved to `~Escapable` `Span`, `MutableSpan`, `Ref`, `MutableRef` (`SE-0519`) | Via ARC `class` + dynamic exclusivity | Yes (`Sendable` + actors) | `~Escapable` cannot escape into classes/globals/escaping closures; cycles use ARC |
| **Austral** (`0962d2a8a5`) | Linear values + lexical region borrows | **Must-linear** (`LinearUniverse`; `WriteRef`/`SpanMut` affine) | Region-typed `&[T, R]` / `&![T, R]` | No | Single-threaded core | No exceptions (`abort` = `_Exit(-1)`), no closures, no implicit `Drop` |
| **Linear Haskell** (POPL '18) | Linear arrow (`A ⊸ B`) | Conditional exact-once on full result eval | GC heap (no borrow lifetimes) | Via GC / scoped `MArray` | Orthogonal | Linear arrow $\neq$ unique ptr; vacuous under divergence (`repeat 1 ++ xs`) or exceptions |
| **Pony** (2015; `ponyc` `b2d900f328`) | 6-capability deny matrix (`iso`–`tag`) | Destructive read / `consume` (`^`) | GC object refs (no lifetimes) | Yes (`ref` locally; cycles inside `iso`) | Yes (actors + `{iso, val, tag}`) | Generic cap explosion, `recover` rigidity, non-monotonic `cap_safetomove`, `ponyc#1931` |
| **Project Verona** (2023; `verona-rt` `5cb8e8cf36`) | Isolated region forest (`iso` bridge) + `cowns` | Linear `iso` region roots + `when` | Region-scoped `mut`/`tmp`/`paused`/`imm` + `cowns` | Yes (unrestricted cycles in active region; bulk freed) | Yes (2PL MCS-queue `when`; zero atomic RC) | Single window of mutability (one active region/thread); cross-region edges restricted to bridges/immutables |

---

### 2. From Explicit Stack Regions (`Tofte–Talpin`, `Cyclone`) to Borrow Graphs (`Polonius`, `PCG`) and Structural Walls (`Pin<P>`, Partial Borrows, `GhostCell`)

#### 2.1 Tofte–Talpin Region Inference and Tail-Recursion Space Leaks

Basis: normative + documentation + derived

Tofte & Talpin (POPL '94, DOI `10.1145/174675.177855`; expanded in *Information and Computation* 1997, DOI `10.1006/inco.1996.2613`) replaced tracing GC for polymorphic call-by-value $\lambda$-calculi with an inferred **stack of regions**:

- Every heap value carries an allocation target `at ρ`; `letregion ρ in e` introduces and pops `ρ` in strict LIFO lexical order. Function arrows carry latent read/write/allocation effects ($\tau_1 \xrightarrow{\varepsilon} \tau_2$) and region polymorphism ($\forall \vec{\rho}. \tau$).
- Soundness holds because no value reachable from `e`'s result or escaping closures mentions `ρ` in its type once `letregion ρ` exits.

**Failure mode — tail-recursive region-endomorphism leaks**: Under strict LIFO nesting ($\rho_{\text{inner}} \subseteq \rho_{\text{outer}}$), a tail-recursive function whose accumulator preserves the same region parameter across iterations (*region endomorphism*) cannot pop the accumulator's outer region between steps. Every iteration allocates into the same outer infinite region, turning $O(1)$ tail recursion into an $O(N)$ space leak, and minor syntactic edits can silently hoist allocations into global regions.

Two static analyses mitigated this rigidity:
1. **Aiken, Fähndrich & Levien (PLDI '95, DOI `10.1145/223428.207137`)**: decoupled region allocation from deallocation via constraint-based flow analysis, inserting early `freeregion` calls inside loops and higher-order functions.
2. **Birkedal, Tofte & Vejlstrup (POPL '96, DOI `10.1145/237721.237771`) — MLKit Storage-Mode Analysis**: classified regions as finite (stack-sized) or infinite (page-linked) and inferred **storage modes** (`atbot`, `attop`, dynamic `sat`). When liveness proves all prior objects in an infinite region `ρ` are dead before a tail call, `atbot` resets `ρ`'s allocation pointer to its bottom page in place—recovering $O(1)$ space without leaving lexical syntax.

#### 2.2 Cyclone: Explicit Regions, Existential Packing, Dynamic Regions, and Unique Pointers

Basis: normative + documentation

Cyclone (Grossman et al., PLDI '02, DOI `10.1145/512529.512563`; extended with safe manual memory management in Hicks et al., ISMM '04, DOI `10.1145/1029873.1029883`, and Swamy et al., SCP 2006, DOI `10.1016/j.scico.2006.02.003`) adapted regions to C-layout pointers:

- **Pointer region annotations & outlives**: Pointers carry explicit region names (`T *@region('r)` / `T *'r`), with global GC heap `'H`, lexical blocks `region r { ... }`, and outlives constraints `'r1 > 'r2`.
- **Existential region packing**: Structs hide internal region names via existentials (`struct S { <'r> int *'r p; }`), requiring explicit unpacking to name `'r` before dereference.
- **Non-LIFO extensions** (Hicks et al. '04; Swamy et al. '06): To avoid arena bloat in long-lived servers, Cyclone added (1) **dynamic growable regions** created via `new_ukey()` (returning a linear unique key), accessed only inside lexical `open(key)` blocks, and reclaimed explicitly via `free_ukey(key)`; (2) **unique pointers** (`` `U ``) and **reference-counted pointers** (`` `RC ``) via alias qualifiers (`ALIASABLE`, `UNIQUE`, `REFCNT`); and (3) **`alias` coercion** (`alias <'r> T *'r x = unique_ptr;`), temporarily viewing a unique pointer as a scoped region pointer so region-polymorphic code runs uniformly over all pointer kinds—a direct precursor to Rust's borrows.

#### 2.3 Polonius and Place Capability Graphs (PCGs)

Basis: source + normative + documentation

Rust's Non-Lexical Lifetimes (NLL) models lifetimes as path-insensitive CFG point sets, rejecting sound conditional-escape patterns such as **Problem Case #3** (returning a mutable borrow on one branch vs. mutating on the fallback branch, e.g., `rust-lang/polonius` `inputs/issue-47680/issue-47680.rs`).

**Polonius (`rust-lang/polonius@bfd4c945b7`, `polonius-engine/src/output/naive.rs:93-248`)** replaces point sets with **origins** (sets of loans) computed via nine Datalog rules:
1. `subset(O1, O2, P) :- subset_base(O1, O2, P)`
2. `subset(O1, O3, P) :- subset(O1, O2, P), subset(O2, O3, P)`
3. `subset(O1, O2, P2) :- subset(O1, O2, P1), cfg_edge(P1, P2), origin_live_on_entry(O1, P2), origin_live_on_entry(O2, P2)`
4. `origin_contains_loan_on_entry(O, L, P) :- loan_issued_at(O, L, P)`
5. `origin_contains_loan_on_entry(O2, L, P) :- origin_contains_loan_on_entry(O1, L, P), subset(O1, O2, P)`
6. `origin_contains_loan_on_entry(O, L, P2) :- origin_contains_loan_on_entry(O, L, P1), !loan_killed_at(L, P1), cfg_edge(P1, P2), origin_live_on_entry(O, P2)`
7. `loan_live_at(L, P) :- origin_contains_loan_on_entry(O, L, P), origin_live_on_entry(O, P)`
8. `errors(L, P) :- loan_invalidated_at(L, P), loan_live_at(L, P)`
9. `subset_errors(O1, O2, P) :- subset(O1, O2, P), placeholder_origin(O1), placeholder_origin(O2), !known_placeholder_subset(O1, O2)`

Polonius accepts Problem Case #3 because loans remain live only along paths where a containing origin stays live, but its fixed-point Datalog evaluation is costly: Grannan et al. (2025 §4.2) note Polonius took **>1 hour on individual crates** in their top-500 evaluation.

**Place Capability Graphs (PCGs)** (Grannan, Bílá, Fiala, Geer, de Medeiros, Müller & Summers, OOPSLA '25, DOI `10.1145/3763122`, `arXiv:2503.21691v5`) extract a borrow-checker-agnostic capability model (supporting both NLL and Polonius) for verifiers (Prusti) and analyzers (Flowistry):
- **Nodes & Capabilities (Def. 3.1)**: Generalised places $P ::= p \mid p\ \text{at}\ l \mid \text{origin}(i)$ carry $c \in \{\mathbf{E}\text{ (exclusive)}, \mathbf{W}\text{ (write/uninit)}, \mathbf{R}\text{ (read)}, \emptyset\}$. Every readable place ($\mathbf{R}$ or $\mathbf{E}$) carries **lifetime projection nodes** $\langle\langle P \downarrow \tilde{r} \rangle\rangle$ representing sets of active borrows stored inside $P$.
- **Six Hyper-Edge Kinds (Def. 3.2)**: `b` (borrow $\{P\}\!\to\!\{L\}$), `u` (unpack $\{P\}\!\to\!\{\vec{P}\}$), `f` (borrow-flow $\{L\}\!\to\!\{L\}$), `a` (abstraction summary for calls and loops $\{\vec{L}\}\!\to\!\{\vec{L}\}$), `l` (alias $\{P\}\!\to\!\{P\}$), and `d` (deref $\{P,L\}\!\to\!\{P\}$).
- **Loops & Empirical Coverage (§2.5, §4.2 Table 2)**: Abstraction edges summarize arbitrary loop iterations (e.g., `penultimate_mut`) so deductive verifiers can attach loop invariants/magic wands. On 491 compiling crates from crates.io's top 500 (Rust nightly `2024-12-15`, 94 min on 6-core Xeon E-2236 / 64 GB RAM), PCGs succeeded on **118,483 / 121,271 functions (97.7%)**. Failures were 2,776 explicitly unsupported unsafe constructs (`DerefUnsafePtr`: 1,584; `CallWithUnsafePtrWithNestedLifetime`: 1,039; `InlineAssembly`: 80; `MoveUnsafePtrWithNestedLifetime`: 73) plus **12 `rustc` limitations** (`ExpansionOfAliasType`: 6; `IndexingNonIndexableType`: 5; `AssignBorrowToNonReferenceType`: 1) where type-alias normalization erased required lifetimes.

#### 2.4 Structural Walls: Partial Borrows, `Pin<P>`, Custom Pointer Wrappers, and `GhostCell`

Basis: normative + documentation + execution + derived

Four structural barriers persist beyond intraprocedural borrow graphs:
1. **Interprocedural Partial Borrows ("View Types")**: Intraprocedural field splitting (`&mut s.a` alongside `&s.b`) collapses at `&mut self` method boundaries because encapsulation hides private fields while disjoint borrowing demands an explicit footprint; trait-level view types require abstract disjoint capability groups.
2. **Self-Referential Structs & `Pin<P>`**: Value-based bitwise relocation (`memcpy`) conflicts with address-pinned invariants (async state machines, intrusive heads, self-slicing buffers). Library-level `Pin<P>` + `Unpin` + drop-guarantee projection is viral without first-class immobility/in-place-construction modes (see `rust-aliasing-models-stacked-tree-minirust-and-llvm-attributes` for Rust's `Pin`/`noalias` interaction).
3. **Custom Pointer Invariants Without Native Capabilities**: Encoding custom aliasing $\times$ alignment $\times$ validity $\times$ `UnsafeCell`-absence $\times$ dynamic borrow-guard invariants purely in phantom-typed raw pointer wrappers repeatedly produces subtle variance, aliasing-iterator, and guard-detachment bugs even under expert audit.
4. **Cyclic Graphs & `GhostCell` (Yanovski, Dang, Jung & Dreyer, ICFP '21, DOI `10.1145/3473597`)**:
   - **API (§3.1)**: Separates shared data topology (`GhostCell<'id, T>`) from exclusive/shared permission (`GhostToken<'id>`) via an invariant phantom lifetime (`InvariantLifetime<'id>`) instantiated by a rank-2 closure:
     ```rust
     struct GhostToken<'id> { _marker: InvariantLifetime<'id> }
     struct GhostCell<'id, T: ?Sized> { _marker: InvariantLifetime<'id>, value: UnsafeCell<T> }
     impl<'id> GhostToken<'id> {
         fn new<R>(f: impl for<'new_id> FnOnce(GhostToken<'new_id>) -> R) -> R
     }
     impl<'id, T> GhostCell<'id, T> {
         fn new(value: T) -> Self; fn into_inner(self) -> T;
         fn get_mut(&mut self) -> &mut T; fn from_mut(t: &mut T) -> &mut Self;
         fn borrow<'a>(&'a self, token: &'a GhostToken<'id>) -> &'a T;
         fn borrow_mut<'a>(&'a self, token: &'a mut GhostToken<'id>) -> &'a mut T;
     }
     ```
   - **Soundness & Performance (§4–§5)**: Mechanized sound in Coq/Iris extending RustBelt (`'id` maps to ghost-state name $\kappa_{\text{id}}$; see `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`). On a 100k-node doubly-linked list 4-thread immutable iteration benchmark (Rust 1.52.1, 4-core i5), `GhostCell` was **$\ge 10\times$ faster** than `Mutex`/`RwLock` due to zero atomic/lock traffic.
   - **Verified Limitations (§3.2.2; checked in `support/verify_ownership_paradigms.py` Part B)**: (a) **No safe simultaneous `iter_mut`** (cycles could yield aliasing `&mut` to the same node, so `&mut GhostToken` serializes mutation to one node at a time); (b) **single-token write serialization** across disjoint subgraphs under one brand; and (c) **orthogonal deallocation** (requires an arena—no individual node free—or `Arc` with runtime RC and manual cycle breaking).

---

### 3. Mutable Value Semantics (`Hylo`) and Swift's Trajectory from `~Copyable` to First-Class `~Escapable` References

#### 3.1 Core MVS and `hylo-lang/hylo` Compiler Architecture

Basis: normative + source + documentation

Racordon, Shabalin, Zheng, Abrahams & Saeta (*Journal of Object Technology* 21(2), 2022, DOI `10.5381/jot.2022.21.2.a2`) formalize **Mutable Value Semantics (MVS)**: ban shared mutable state rather than mutation, confining references to **second-class** function/subscript boundaries governed by the **Law of Exclusivity** (`SE-0176`). Because overlapping mutations are illegal, conceptual call-by-value-return `inout` parameters compile to zero-copy pass-by-reference in-place updates; fixed-size values live on the stack while dynamic containers use uniqueness-checked copy-on-write (COW) buffers.

Direct inspection of `hylo-lang/hylo` (`6889158246df571baa9079115817ab2bff61156b`) establishes how Hylo implements MVS:
- **Five `AccessEffect` conventions (`Sources/FrontEnd/AccessEffect.swift:1-39`)**: `let` (`1`, immutable borrow), `set` (`2`, write-only uninitialized destination for in-place construction), `inout` (`4`, exclusive mutable borrow), `sink` (`8`, consuming move), and `yielded` (`16`, effect-polymorphic subscript placeholder).
- **Access Reification & Definite Initialization (`Sources/IR/Analysis/Module+AccessReification.swift:1-191`, `Docs/LocalBindings.md:162-210`)**: Worklist pass `reifyAccesses` narrows multi-capability `Access`/`ProjectBundle` instructions to the weakest required capability across an acyclic client forest. Definite Initialization (DI) models IR registers as linear resources and stack storage across four states (`Raw`, `Uninitialized`, `Initialized`, `Partial`), inserting deterministic `deinit`/`dealloc_stack` on every path.
- **Yield-Once Subscript Coroutines (`Docs/Subscripts.md:1-174`)**: Subscripts replace lifetime-returning references by executing **exactly one `yield`** on every path (`yield` forbidden in loops; `Module+CheckYieldCoherence.swift`), bracketed at call sites by `project`/`end_project`. Hylo documents three lowerings:
  1. *Subscripts-as-continuations*: splits into *ramp* + *slides*, sizing caller continuations by dominance frontiers to handle non-nested overlapping projections (`t`, then `u`, closing `t` before `u`).
  2. *Subscripts-as-sessions*: ramp returns the yielded address using a caller-allocated fixed-size frame buffer—requiring a frame-size helper for ABI stability and prohibiting dynamic `alloca` in ramps.
  3. *Addressors*: subscripts directly computing a stored sub-object address need no slide.
  - `Docs/Subscripts.md:161-169` explicitly notes that target-independent materialized frames for continuations/sessions can disable LLVM `mem2reg` promotion.

#### 3.2 Expressive Walls of Strict MVS — Hylo `RemoteParts.md` and Swift's 8-Proposal Convergence

Basis: source + normative + derived

Strict second-class MVS hits three walls: (1) **stored projections** (`Slice<Base>`, parser cursors, iterators stored in structs), (2) **cyclic/shared-mutable graphs** (all MVS values are disjoint trees), and (3) **escaping async continuations** (breaking synchronous ramp/slide stack discipline).

Both Hylo and Swift independently broke out of Wall #1 by re-introducing bounded borrowed types:
- **Hylo (`Docs/RemoteParts.md:1-95`)**: Designs *remote parts* (`var base: remote base_access Base`) inside effect-polymorphic structs (`type Slice<Base: Collection, base_access: access = sink>`), where `remote sink T` $\equiv$ `T`, initializer arguments bind the struct's lifetime, and remote parts cannot be reseated.
- **Swift (`swiftlang/swift-evolution@6385c2aee6`)**: Evolved step-by-step from `SE-0176` exclusivity back to **safe, first-class, nonescapable references** (`SE-0519`):

| Proposal | Release | Mechanism Added | Key Boundary Documented |
| :--- | :--- | :--- | :--- |
| **`SE-0377`** | Swift 5.9 | `borrowing` / `consuming` parameter & method modifiers; disables implicit copies (`copy x` required) | `consuming` banned on nonescaping closures; no implicit convention conversion for `~Copyable` |
| **`SE-0390`** | Swift 5.9 | `~Copyable` structs/enums with unique ownership, `deinit`, `discard self` | Excluded from generics/protocols (except `Sendable`)/tuples; `discard self` initially limited to structs without component cleanups (rejecting Rust `mem::forget` field leaks) |
| **`SE-0427`** | Swift 6.0 | Noncopyable generics (`<T: ~Copyable>`) via suppressible `Copyable` | Default `Copyable` retained for source/ABI compatibility |
| **`SE-0429`** | Swift 6.0 | Partial consumption of `~Copyable` struct fields (deinit-less or inside `deinit`) | Requires same-module or `@frozen` layout |
| **`SE-0446`** | Swift 6.2 | Suppressible `~Escapable` orthogonal to `~Copyable` (local copies OK; no globals/classes/escaping closures) | Returning `~Escapable` (and initializers) requires lifetime-dependency annotations |
| **`SE-0447`** | Swift 6.2 | `Span<Element: ~Copyable>: Copyable, ~Escapable` & `RawSpan` (`unsafeLoad*`) | Does not conform to `Collection`; `_read` accessor narrows element borrow to single access |
| **`SE-0467`** | Swift 6.2 | `MutableSpan` & `MutableRawSpan` (`~Copyable, ~Escapable`) | Distinct from `Span` so API author—not caller `var`—controls mutability |
| **`SE-0519`** | Swift 6.4 | First-class safe references: `Ref<Value: ~Copyable>: Copyable & ~Escapable` (`@_lifetime(borrow target)`) and `MutableRef<Value: ~Copyable>: ~Copyable & ~Escapable` (`@_lifetime(&target)`) with `SE-0507` `borrow`/`mutate` accessors | Confined to `~Escapable` scopes (no classes/globals/escaping closures); reintroduces `@_lifetime(...)` annotations at API boundaries |

**Takeaway (derived)**: Swift's 2023–2026 arc empirically demonstrates that pure second-class MVS cannot sustain zero-overhead views, spans, and struct-stored borrows without adding `~Escapable` first-class references and lifetime-dependency annotations—converging toward Rust's `&'a`/`&'a mut` while keeping lifetimes localized to `~Escapable` APIs.

---

### 4. True Must-Linearity vs. Affine Drop (`Austral`, `Linear Haskell`, and the Unwind Paradox)

#### 4.1 Why Affine Ownership Cannot Enforce Must-Consume Protocols

Basis: normative + execution + derived

In **affine** systems (Rust, Swift `~Copyable`), values are used *at most once*: scope exit, early return (`?`), overwrite, or panic unwinding silently triggers `Drop::drop(&mut self)` / `deinit`, and Rust permits `std::mem::forget` and `Rc` cycle leaks in safe code. Affine types therefore cannot statically enforce obligations whose discharge requires extra arguments, a fallible `Result`, `async` completion, or a mandatory post-state witness (e.g., `Receipt` from `commit(tx)` / `abort_tx(tx)`).

#### 4.2 Austral: Type-Based Must-Linearity and Source-Verified Nuances

Basis: source + documentation + execution

**Austral (`austral/austral@0962d2a8a5`)** enforces type-based must-linearity in its OCaml compiler (`lib/Type.ml`, `lib/TypeSystem.ml`, `lib/LinearityCheck.ml`, `lib/DesugarBorrows.ml`, `lib/prelude.c`):
- **Four Universes (`lib/Type.ml:15-20`, `lib/TypeSystem.ml:12-28`)**: `FreeUniverse` (primitives, `ReadRef`, `Span`, `Address`, `Pointer`, `FnPtr`, `Free` types), `LinearUniverse` (user linear types, `RootCapability : Linear` in `lib/builtin/Pervasive.aui:29`, `WriteRef`, `SpanMut`), `TypeUniverse` (generic over `Free`/`Linear`, conservatively treated as linear-ish by `universe_linear_ish`, `LinearityCheck.ml:25-28`), and `RegionUniverse` (`RegionTy`).
- **Four-State Linearity Checker (`lib/LinearityCheck.ml:18-23, 98-123, 306-754`)**: Tracks `(ty, loop_depth, var_state)` over `{Unconsumed, BorrowedRead, BorrowedWrite, Consumed}` plus a `pending` set:
  - `tables_are_consistent` (lines 306–355) requires identical `var_state` across all `TIf`/`TCase` branches.
  - Consuming a linear variable defined at an outer `loop_depth` adds it to `pending` (lines 404–419); overwriting an `Unconsumed` linear variable fails (lines 553–560), while reassigning a `Consumed` variable restores `Unconsumed` and clears `pending` (lines 562–568); any remaining `pending` variable at loop exit raises `LinearityError` (lines 592–618).
  - Scope exit (`remove_entry`, lines 98–123) and `TReturn` (lines 685–714) reject any unconsumed linear-ish variable.
  - Anonymous `&x`/`&!x` borrows desugar into statement-scoped `ABorrow` blocks with fresh `_tmp_region_N` (`lib/DesugarBorrows.ml:138-156`).
- **Two Crucial Source-Level Nuances**:
  1. **Mutable references are affine inside Austral (`lib/LinearityCheck.ml:107-108, 696-702`)**: Although `WriteRef` (`&!`) and `SpanMut` (`Span!`) live in `LinearUniverse` (preventing duplication/aliasing), `remove_entry` and `TReturn` explicitly exempt both to **drop implicitly**. Austral thus separates no-aliasing uniqueness from must-consume obligation.
  2. **Control-flow price (`lib/prelude.c:92-117`, `lib/Type.ml:54`)**: Austral has no exceptions, no unwinding, no closures (`FnPtr` only), and no implicit destructors; `abort` and bounds/overflow traps call C `_Exit(-1)` directly, terminating the process so execution never unwinds past live linear values. (Separately, `LinearityCheck.ml:648-657` resets a `BorrowedRead` variable to `Unconsumed` on inner read-borrow exit rather than preserving `BorrowedRead`, illustrating state-table fragility on nested borrows.)

#### 4.3 Linear Haskell: Arrow Multiplicities and Laziness/Divergence Boundaries

Basis: normative + documentation + execution

Linear Haskell (Bernardy, Boespflug, Newton, Peyton Jones & Spiwack, POPL '18, DOI `10.1145/3158093`, `arXiv:1710.09756v2`) avoids bifurcating container libraries by placing linearity on **function arrows** ($A \to_p B$, with $A \multimap B \equiv A \to_1 B$ and $A \to B \equiv A \to_\omega B$) over the $\{1, \omega\}$ semiring ($0+m=m$, $1+1=\omega$, $1\cdot 1=1$, $\omega\cdot m=\omega$):
```haskell
map   :: forall p.   (a ->_p b) -> [a] ->_p [b]
foldl :: forall p q. (a ->_p b ->_q a) -> a ->_p [b] ->_q a
(.)   :: forall p q. (b ->_p c) %1 -> (a ->_q b) ->_p a ->_(p*q) c
```
Unrestricted payloads travel inside `Unrestricted a` (`Ur a`), and I/O protocols use multiplicity-indexed `IOL p a` (`openFile :: FilePath -> IOL 1 File`, §2.3).

**Two critical semantic boundaries (§2.1, §3.3)**:
1. **Linear arrow $\neq$ unique pointer**: `f :: a ⊸ b` constrains `f`'s use of its argument, not whether the caller aliased it; safe in-place `MArray` updates still require a rank-2/scoped allocation boundary (`alloc :: Int -> (MArray a ⊸ Unrestricted b) ⊸ b`).
2. **Conditional laziness & divergence vacuity (Def. 2.1, §3.3)**: `f :: A ⊸ B` guarantees that *if the result of `f u` is consumed completely exactly once*, then `u` is consumed exactly once. Consequently, `f :: [Int] ⊸ [Int]; f xs = repeat 1 ++ xs` typechecks as linear while never evaluating `xs` (vacuously true because the infinite result cannot be completely consumed); imprecise exceptions (`error`) similarly bypass cleanup.

#### 4.4 The Unwind Paradox and Container Overwrite Split

Basis: derived + execution

As verified in `support/verify_ownership_paradigms.py` (Part C), must-linearity conflicts with both **unwinding/cancellation** (requiring either no unwinding like Austral's `_Exit(-1)`, panic-free effect gating of linear scopes, or typed unwind handlers consuming live obligations) and **overwriting generic containers** (`Vec::clear`, `HashMap::insert` discarding old values), forcing either a `Free`/`Linear` universe split or explicit value-returning container APIs.

---

### 5. Reference Capabilities and Region Isolation (`Pony` and `Project Verona` Reggio/`cowns`)

#### 5.1 Pony: Deny Capability Matrix, Viewpoint Evolution, and `ponyc` Edge Cases

Basis: normative + source + execution

Pony (Clebsch, Drossopoulou, Blessing & McNeil, AGERE! '15, DOI `10.1145/2824815.2824816`; `ponylang/ponyc@b2d900f3287e40e8e048b6f715a9f461932e14c1`) classifies references by **deny properties**—operations forbidden to other local (same-actor) vs. global (other-actor) aliases:

| Local Denied \ Global Denied | Deny Global R & W | Deny Global W | Allow Global R & W |
| :--- | :--- | :--- | :--- |
| **Deny Local R & W** | **`iso`** *(R/W, sendable)* | *(impossible)* | *(impossible)* |
| **Deny Local W** | **`trn`** *(R/W, write-unique)* | **`val`** *(R-only, sendable)* | *(impossible)* |
| **Allow Local R & W** | **`ref`** *(R/W, local)* | **`box`** *(R-only, local writes possible)* | **`tag`** *(opaque, sendable)* |

Monotonicity (`local_denied ⊆ global_denied`) selects exactly **6 of 9 cells** (verified in `support/verify_ownership_paradigms.py` Part A).

- **Aliasing (`!`), Ephemerals (`^`), and Sendability (`cap.c:10-60, 1265-1280`, `alias.c:18-60`)**: Aliasing maps `iso!` $\to$ `tag`, `trn!` $\to$ `box`, `#send!` $\to$ `#share`, `#any!` $\to$ `#alias`. Consuming/destructive-reading produces ephemeral `iso^`/`trn^`. Exhaustive checking over all locally compatible aliases proves `sendable == {iso, val, tag}`: `trn` races with local `box` readers, `ref` races with local `ref` writers, and **`box` races with local `trn`/`ref` writers** despite `box` being globally compatible with another `box`!
- **Viewpoint Adaptation (`origin -> field`) — Exact Evolution Between AGERE! 2015 and Modern `ponyc` (`cap.c:808-1009`)**:

| Origin $\to$ Field | `iso` | `trn` | `ref` | `val` | `box` | `tag` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`iso`** | `iso` | **`iso`** *(2015: `tag`; read `!` $\to$ `tag`)* | **`iso`** *(2015: `tag`; read `!` $\to$ `tag`)* | `val` | `tag` | `tag` |
| **`iso^`** | `iso^` | `iso^` | `iso^` | `val` | **`val`** | `tag` |
| **`trn`** | `iso` | `trn` | **`trn`** *(2015: `box`; read `!` $\to$ `box`)* | `val` | `box` | `tag` |
| **`trn^`** | `iso^` | `trn^` | `trn^` | `val` | **`val`** | `tag` |
| **`ref`** | `iso` | `trn` | `ref` | `val` | `box` | `tag` |
| **`val`** | `val` | `val` | `val` | `val` | `val` | `tag` |
| **`box`** | `tag` | `box` | `box` | `val` | `box` | `tag` |
| **`tag`** | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ |

  Because writes into `iso` are restricted to sendable `{iso, val, tag}`, internal `ref`/`trn` fields inside an `iso` are region-isolated; modern `ponyc` types the *path* `iso -> ref` as `iso` (`iso^ -> ref` as `iso^`), while non-destructive read applies `alias_single` (`iso!` $\to$ `tag`, `trn!` $\to$ `box`), recovering AGERE! 2015 Table 2 while unlocking `iso^`/`trn^ -> box = val`.
- **Subtle Compiler Constraints (`cap.c`, `safeto.c`, `alias.c`, `expr/control.c`)**:
  - **Non-monotonic `cap_safetomove` (`cap.c:1214-1262`, `safeto.c:39-67`)**: Under subtyping (`cap.c:117-126`), `trn <: box`, yet `cap_safetomove(trn, trn, WRITE) == true` while `cap_safetomove(trn, box, WRITE) == false` (whereas `EXTRACT(trn, box) == true`). `safe_field_move` must therefore conservatively reject arrow types whose lower bound is an ephemeral generic approximation (`lower(trn, #read) = trn^`).
  - **Recovery rigidity (`expr/control.c:489`, `alias.c:61, 550`)**: `recover` blocks lift internal `ref`/`trn` to `iso^`/`val` and `box` to `val`, but capturing any single non-sendable outer variable rejects the entire block.
  - **Generic unsoundness (`cap.c:410-413`)**: `is_cap_compat_cap` marks `TK_CAP_ANY` as `"a hack and is part of generic unsoundness"` citing `ponyc#1931`.

#### 5.2 Project Verona: Isolated Region Forest (`Reggio`), Single Window of Mutability, and `cowns`

Basis: normative + source + documentation + execution

Project Verona (Arvidsson et al., OOPSLA '23, DOI `10.1145/3622846`, `arXiv:2309.02983v1`; Cheeseman et al., OOPSLA '23, DOI `10.1145/3622852`; `microsoft/verona-rt@5cb8e8cf36`; `microsoft/verona@ed33fdf1c2`) moves isolation from individual objects to a **forest of isolated regions**:

- **Bridge Objects & Unrestricted Internal Cycles (Arvidsson et al. '23 §3.2.1, §3.2.5)**: Each closed region has one externally unique **bridge object** (`iso`); no other external incoming pointers exist, and outgoing persistent edges target only `imm` objects or nested closed-region bridges. Inside an open region, arbitrary `mut` cyclic graphs are unrestricted. Any internal object can be designated as the new bridge upon closing (§3.2.5); dropping the `iso` frees the region and all nested regions iteratively via an `ObjectStack` worklist (`verona-rt/src/rt/region/region.h:123-135`).
- **Single Window of Mutability & Five Capabilities (Arvidsson et al. '23 Table 1 & §4.1 Table 2)**: Entering a region (`enter a { r => ... }`) pushes it onto a per-thread LIFO stack: only the top region is **`active`** (mutable/allocating), outer open regions are **`suspended`** (read-only), and unopened regions are **`closed`**. Five capabilities enforce this without mixed-capability aliasing: `mut` (active persistent), `tmp` (active temporary permitted to hold `paused` refs; invalidated on close), `imm` (deeply immutable), `iso` (closed bridge), and `paused` (suspended outer region). Exact viewpoint adaptation ($\alpha \odot \beta$, Table 2):

| $\alpha \odot \beta$ | `mut` | `tmp` | `imm` | `iso` | `paused` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`mut`** | `mut` | $\bot^\dagger$ | `imm` | $\bot$/`iso` | $\bot^\dagger$ |
| **`tmp`** | `mut` | `tmp` | `imm` | $\bot$/`iso` | `paused` |
| **`imm`** | `imm` | `imm` | `imm` | `imm` | `imm` |
| **`iso`** | $\bot$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ |
| **`paused`** | `paused` | `paused` | `imm` | $\bot$/`iso` | `paused` |

  Entering a nested region adapts every captured variable `v : k τ` to `(paused ⊙ k) τ`—turning outer `mut`/`tmp` read-only while keeping `iso` openable. `merge : iso -> mut` absorbs a closed region into the active region (re-parenting direct child regions); `freeze : iso -> imm` recursively freezes a region and all nested subregions, dissolving region boundaries (§3.2.6).
- **Per-Region Pluggable Memory Management (`verona-rt/src/rt/region/region.h:15-176`)**: Each region chooses `RegionType::Trace` (local tracing GC), `RegionType::Arena` (bump arena), or `RegionType::Rc` (local RC) at creation. Because each active region is thread-exclusive and MM inspects only the active region, RC updates use **zero atomics** and tracing GC causes **zero stop-the-world pauses** (Arvidsson et al. '23 §8.2).
- **Behaviour-Oriented Concurrency (`cowns` + `when`, Cheeseman et al. '23; `verona-rt/src/rt/cpp/when.h`, `src/rt/boc/behaviourcore.h`)**:
  - A `cown` wraps an `iso` region root; `when(c1, ..., cn) << lambda` asynchronously acquires any set of cowns in `AccessMode::Write` or `AccessMode::Read` (`const T`), supporting zero-refcount borrowed lvalues (`Ownership::Borrowed`), rvalue transfers (`Ownership::Transferred`), and atomic multi-behaviour `Batch<Size>` scheduling (`when.h:64-113, 303-358`).
  - **Deadlock-free lock-free 2PL (`behaviourcore.h:67-142, 1230, 1521`)**: Each cown uses an MCS-style lock-free slot queue (`STATUS_WAIT`, `STATUS_READY`, `STATUS_READAVAILABLE`, `STATUS_CHAIN_CLOSED`, `Read(Slot*)`, `Write(BehaviourCore*)`) with 3 low-bit flags (`COWN_MOVE_FLAG`, `COWN_READER_FLAG`, `COWN_DUPLICATE_FLAG`). `BehaviourCore::schedule_many` deduplicates and sorts slots by canonical `cown()` pointer (`std::sort`, line 1521) before 2PL acquisition—guaranteeing an acyclic wait-for graph without actor coordination state machines.

---

### 6. Architectural Trade-Off Synthesis

Basis: execution + derived

No single paradigm simultaneously yields zero-annotation ergonomics, arbitrary cyclic mutable graphs, synchronous cross-region pointers, non-panicking must-linear obligations, and lock-free concurrency:
- **Tree vs. Region Ownership**: Per-node exclusive trees give fine-grained aliasing optimizations and deterministic drop order, while Verona-style isolated regions absorb internal cycles, heterogeneous memory managers (`Trace`/`Arena`/`Rc`), and FFI heap boundaries under a single linear handle (`iso`/`cown`) at the cost of a single mutability window and bridge-only cross-region edges.
- **Second-Class vs. Bounded First-Class Borrows**: Second-class MVS minimizes annotation overhead for simple APIs, but real systems code forces re-introducing `~Escapable` first-class borrows (`Span`, `Ref`, `MutableRef` / `remote` parts) with localized lifetime dependencies.
- **Affine vs. Must-Linear**: Strict must-linearity is practical only when explicitly stratified from droppable affine types (even Austral makes `WriteRef`/`SpanMut` affine) and paired with unwinding control (process-terminating abort, panic-free effect scopes, or linear-consuming unwind handlers).

## Boundaries

- **known not to apply**:
  - **Linear Haskell arrow linearity $\neq$ uniqueness or unconditional cleanup**: `a ⊸ b` does not prevent aliased callers without scoped allocators (`alloc`), and lazy Definition 2.1 holds only vacuously under divergence (`repeat 1 ++ xs`) or imprecise exceptions.
  - **Strict second-class MVS does not cover stored views or cycles**: Both Hylo (`Docs/RemoteParts.md`) and Swift (`SE-0446`/`0447`/`0467`/`0519`) confirm stored slices/references require `~Escapable` lifetime-dependent types, and cyclic mutable graphs remain outside tree value semantics.
  - **Pony `box` sendability**: Global compatibility of `(box, box)` does not make `box` sendable, because `box` admits co-existing local `ref`/`trn` writers.
  - **Austral `WriteRef`/`SpanMut` must-linearity**: Although in `LinearUniverse`, both are explicitly exempted to drop implicitly (`lib/LinearityCheck.ml:107-108, 696-702`).
- **unsupported**:
  - **PCGs on raw pointers & inline assembly**: 2,776 of 121,271 functions in Grannan et al. (2025 Table 2) failed on unsupported raw-pointer/inline-asm constructs, plus 12 on `rustc` type-alias lifetime erasure.
  - **Simultaneous `iter_mut` on cyclic `GhostCell` lists**: Unsupported safely in Rust without a non-local acyclicity invariant (Yanovski et al. '21 §3.2.2).
  - **Exceptions, unwinding, and closures in Austral (`0962d2a8a5`)**: Explicitly excluded by design (`abort` calls `_Exit(-1)`; `FnPtr` only).
  - **Simultaneous synchronous mutation of two Verona regions**: Disallowed by Reggio's Single Window of Mutability (outer open regions are `suspended` read-only).
- **not examined**:
  - **Vale generational references, Reachability Types (Bao et al. '21 / Wei et al. '24), Mezzo, Idris 2 QTT, and OxCaml modes**: Not audited against pinned source commits here.
  - **Weak-memory model checking of `verona-rt` `BehaviourCore` atomics**: Code and ordering comments were inspected, but no C11 litmus/GenMC proof was executed.
  - **Local benchmark re-execution**: GhostCell ($\ge 10\times$) and PCG (94 min top-500) figures come directly from the primary papers.
- **unknown**:
  - **Resolution of Pony generic capability soundness (`ponyc#1931`)**: Still annotated as an active hack in `ponyc/src/libponyc/type/cap.c:410-413` at `b2d900f328`.
  - **Austral nested read-borrow state reset (`lib/LinearityCheck.ml:648-657`)**: Exiting an inner read-borrow resets the outer variable to `Unconsumed` rather than `BorrowedRead`; whether earlier passes block unsound consumption in all reachable programs was not exhaustively verified.
  - **Interprocedural trait-level view types via PCGs**: Open research; no deployed Rust implementation exists as of `2026-11-19`.
- **Stronger conclusions not established**: Passing `support/verify_ownership_paradigms.py` checks the encoded algebraic models, not a mechanized soundness proof of full compilers; Verona's 2PL BoC eliminates `when` deadlocks and data races but not livelock, scheduling starvation, or unbounded `RegionArena` growth.

## Evidence

### Primary Peer-Reviewed Papers

1. **Tofte & Talpin (1994)** — *Implementation of the Typed Call-by-Value $\lambda$-Calculus using a Stack of Regions*, POPL '94, pp. 188–201, DOI `10.1145/174675.177855`; **Tofte & Talpin (1997)**, *Region-Based Memory Management*, Information and Computation 132(2), DOI `10.1006/inco.1996.2613`.
2. **Aiken, Fähndrich & Levien (1995)** — *Better Static Memory Management: Improving Region-Based Analysis of Higher-Order Languages*, PLDI '95, DOI `10.1145/223428.207137`.
3. **Birkedal, Tofte & Vejlstrup (1996)** — *From Region Inference to von Neumann Machines via Region Representation Inference*, POPL '96, DOI `10.1145/237721.237771`.
4. **Grossman et al. (2002)** — *Region-Based Memory Management in Cyclone*, PLDI '02, pp. 282–293, DOI `10.1145/512529.512563`; **Hicks et al. (2004)**, ISMM '04, DOI `10.1145/1029873.1029883`; **Swamy et al. (2006)**, *Safe Manual Memory Management in Cyclone*, SCP 62(2), pp. 122–144, DOI `10.1016/j.scico.2006.02.003`.
5. **Clebsch, Drossopoulou, Blessing & McNeil (2015)** — *Deny Capabilities for Safe, Fast Actors*, AGERE! '15, DOI `10.1145/2824815.2824816` (full PDF: Tables 1–3, Fig. 4).
6. **Bernardy, Boespflug, Newton, Peyton Jones & Spiwack (2018)** — *Linear Haskell: Practical Linearity in a Higher-Order Polymorphic Language*, PACMPL 2(POPL), Art. 5, DOI `10.1145/3158093`, `arXiv:1710.09756v2` (full PDF: Def. 2.1, §2.2–§2.6, §3.1–§3.3).
7. **Yanovski, Dang, Jung & Dreyer (2021)** — *GhostCell: Separating Permissions from Data in Rust*, PACMPL 5(ICFP), Art. 92, DOI `10.1145/3473597` (full PDF: §3.1–§3.2.3, §4, §5.1).
8. **Racordon, Shabalin, Zheng, Abrahams & Saeta (2022)** — *Implementation Strategies for Mutable Value Semantics*, JOT 21(2), DOI `10.5381/jot.2022.21.2.a2` (full PDF from `hylo-lang/hylo@6889158246` `Docs/ImplementationStrategiesForMutableValueSemantics.pdf`).
9. **Arvidsson, Castegren, Clebsch, Drossopoulou, Noble, Parkinson & Wrigstad (2023)** — *Reference Capabilities for Flexible Memory Management*, PACMPL 7(OOPSLA2), DOI `10.1145/3622846`, extended `arXiv:2309.02983v1` (full PDF: §3.2, Tables 1–2, §4.1, Listing 1, §8.2).
10. **Cheeseman, Parkinson, Clebsch, Kogias, Drossopoulou, Chisnall, Wrigstad & Liétar (2023)** — *When Concurrency Matters: Behaviour-Oriented Concurrency*, PACMPL 7(OOPSLA2), DOI `10.1145/3622852`.
11. **Grannan, Bílá, Fiala, Geer, de Medeiros, Müller & Summers (2025)** — *Place Capability Graphs: A General-Purpose Model of Rust's Ownership and Borrowing Guarantees*, PACMPL 9(OOPSLA2), Art. 344, DOI `10.1145/3763122`, `arXiv:2503.21691v5` (full PDF: §2.5, §3.1–§3.4, §4.2 Table 2).

### Pinned Upstream Repositories Inspected (`2026-11-19`)

- **`ponylang/ponyc`** @ `b2d900f3287e40e8e048b6f715a9f461932e14c1`: `src/libponyc/type/cap.h` (L1–132), `cap.c` (`cap_aliasing` L10–60, `is_cap_sub_cap` L62–166, `TK_CAP_ANY` L410–425, `cap_view_upper` L808–1009, `cap_view_lower` L1011–1212, `cap_safetomove` L1214–1262, `cap_sendable` L1265–1280), `safeto.c` (`safe_field_move` L8–98, non-monotonicity L39–44), `viewpoint.c` (`viewpoint_type_impl` L18, `viewpoint_upper` L192), `alias.c` (`alias_single` L18, `recover_single` L61, `recover_type` L550), `expr/control.c` (`expr_recover` L489, `expr_return` L573).
- **`hylo-lang/hylo`** @ `6889158246df571baa9079115817ab2bff61156b`: `Sources/FrontEnd/AccessEffect.swift` (L1–39), `Sources/IR/Analysis/Module+AccessReification.swift` (L1–191), `Docs/Subscripts.md` (L1–174), `Docs/RemoteParts.md` (L1–95), `Docs/LocalBindings.md` (L1–210).
- **`swiftlang/swift-evolution`** @ `6385c2aee62d21727333b2539b06458a9476fb2d`: `proposals/{0377-parameter-ownership-modifiers,0390-noncopyable-structs-and-enums,0427-noncopyable-generics,0429-partial-consumption,0446-non-escapable,0447-span-access-shared-contiguous-storage,0467-MutableSpan,0519-ref-mutableref-types}.md`.
- **`austral/austral`** @ `0962d2a8a5d77f7daacd7f696819520733f4897d`: `lib/Type.ml` (L15–56), `lib/TypeSystem.ml` (L12–28), `lib/LinearityCheck.ml` (L18–28, L98–123, L141–177, L306–355, L404–419, L545–715), `lib/DesugarBorrows.ml` (L138–156), `lib/builtin/Pervasive.aui` (L27–31), `lib/prelude.c` (L92–117).
- **`rust-lang/polonius`** @ `bfd4c945b7713d0e66a3cde80475d9a4494740df`: `polonius-engine/src/output/naive.rs` (L93–248), `inputs/issue-47680/issue-47680.rs` (L1–16).
- **`microsoft/verona-rt`** @ `5cb8e8cf3699fa53c8a9b8dc34e4431c40d6230f`: `src/rt/region/region.h` (L15–176), `src/rt/cpp/when.h` (L52–113, L303–358, L404–483), `src/rt/boc/behaviourcore.h` (L67–142 `Slot`, L1230 `schedule`, L1521 `std::sort`).
- **`microsoft/verona`** @ `ed33fdf1c2e249a0393ead1cffd6e40503c70f2c`: `docs/faq.md` (L1–104), `docs/publications.md` (L1–68).

### Execution Evidence

Command executed `2026-11-19` (Python 3 stdlib only, exit `0`):
```console
python3 -B reports/ownership-linearity-regions-and-safe-mutability-design-space/support/verify_ownership_paradigms.py
```
Observed JSON receipt:
- `part_a_pony_capabilities`: 6 deny-matrix cells, 36 viewpoint pairs, derived `sendable = ["iso", "tag", "val"]`, race witnesses `{"box": ["box", "trn"], "ref": ["ref", "ref"], "trn": ["trn", "box"]}`, 3 AGERE! '15 $\to$ `ponyc` path upgrades (`(iso, trn)`, `(iso, ref)`, `(trn, ref)`), and `cap_safetomove` non-monotonicity (`trn <: box`, `WRITE(trn, trn)=true`, `WRITE(trn, box)=false`, `EXTRACT(trn, box)=true`).
- `part_b_regions_and_ghostcell`: per-node tree ownership rejected both cyclic ring and diamond DAG; Verona accepted cyclic ring + bridge swap (`A -> B`), rejected cross-region non-bridge edge (`m -> C`) and suspended-window mutation, and canonicalized 2PL cown acquisition orders to `["cown_1", "cown_2"]`; GhostCell permitted sequential cyclic mutation and rejected cross-brand access and simultaneous two-node `borrow_mut`.
- `part_c_affine_vs_must_linear`: affine accepted missed post-state witnesses on early return and unwind; must-linear rejected early return, unwind, branch mismatch, and un-reassigned loop consumption while accepting balanced branches, reassigned loop vars, and Austral's `WriteRef` implicit-drop exemption; Linear Haskell `{1, ω}` semiring verified.

## Revalidation

1. **Re-run the standalone probe** (<1s): `python3 -B reports/ownership-linearity-regions-and-safe-mutability-design-space/support/verify_ownership_paradigms.py`.
2. **Pony**: Diff `ponylang/ponyc` `src/libponyc/type/{cap,safeto}.c` against `b2d900f328` for `cap_view_upper`, `cap_safetomove`, and `ponyc#1931`.
3. **Hylo**: Diff `hylo-lang/hylo` `Sources/FrontEnd/AccessEffect.swift`, `Docs/Subscripts.md`, and `Docs/RemoteParts.md` against `6889158246` to check whether `remote` parts move from design doc to IR passes.
4. **Swift**: Check `swiftlang/swift-evolution` proposals `0507`, `0519`, and subsequent lifetime-dependency proposals after `6385c2aee6`.
5. **Austral**: Diff `austral/austral` `lib/LinearityCheck.ml` (`remove_entry`, `TReturn`, nested `TBorrow` L648–657) against `0962d2a8a5`.
6. **Verona**: Diff `microsoft/verona-rt` `src/rt/region/region.h` and `src/rt/boc/behaviourcore.h` against `5cb8e8cf36`, and `microsoft/verona` `docs/publications.md` against `ed33fdf1c2`.
7. **Polonius / PCG**: Diff `rust-lang/polonius` `polonius-engine/src/output/naive.rs` against `bfd4c945b7`, and check upstream `rustc` `-Zpolonius=next` and PCG releases for raw-pointer or type-alias lifetime-preservation updates.
