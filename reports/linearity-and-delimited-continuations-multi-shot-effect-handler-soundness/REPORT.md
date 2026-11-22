# Linearity and Delimited Continuations: Typing and Operational Soundness Under Multi-Shot and 0-Shot Effect Handlers

## Summary

Combining linear or affine capabilities (file descriptors, session channels, exclusive memory ownership, hardware DMA tokens, self-referential stack frames) with delimited continuations and algebraic effect handlers exposes a two-sided soundness collision: standard value-linearity type systems assume every continuation executes **exactly once**, whereas an unrestricted handler can invoke a captured continuation **$\ge 2$ times** (multi-shot duplication, causing double-consumption or use-after-free) or **0 times** (abortive drop-skipping, causing linear resource leaks or bypassed cleanup).

Key established findings across five formal and production paradigms, accompanied by a Mathlib-free Lean 4 (`v4.34.1`) toy mechanization (`[kernel-checked proof]` `[toy model]`; **Model–system relation: none proved.**):

1. **Control-flow linearity and graded coeffects close both halves statically.** Tang, Hillerström, Lindley, and Morris (POPL 2024) formalize **control-flow linearity** in $F^\circ_{\text{eff}}$ and infer it without programmer annotations via qualified types in $Q^\circ_{\text{eff}}$, forbidding control-flow-unrestricted (`Unr`) effects whenever a linear variable is live across the suspension point. Affine-only systems such as Alms (Tov & Pucella, POPL 2011) prevent duplication ($\ge 2$-shot) via kind-indexed subkinding and abstract affine sealing but allow 0-shot discard. Graded modal and quantitative calculi (Petricek et al., ICFP 2014; Atkey, LICS 2018; Orchard et al., ICFP 2019) generalize usage accounting to semiring grades (such as $\{0, 1, \omega\}$), of which control-flow linearity is the continuation-variable specialization.
2. **Koka separates 0-shot finalization from $\ge 2$-shot safety and heap-memory reuse.** Operation sorts (`fun`, `final ctl`, `ctl`, `raw ctl`, and `linear effect`) fix clause control flow statically (`MSR-TR-2018-10`). Deep finalization (`finally`) and automatic finalization of unresumed `ctl` clauses prevent 0-shot cleanup skipping, and (`derived`) Perceus reference counting (PLDI 2021) preserves heap memory safety under multi-shot `ctl` because shared continuation closures carry reference counts exceeding 1 and disable in-place reuse. However, Koka does not *statically* forbid multi-shot `ctl` resumption across external linear capabilities (such as OS file handles): `finally` alone double-closes on multi-shot resumption, while the Koka Book (§3.4.11) reference-counted `with-file` idiom pairs `initially` with `finally` to close once only as an unchecked programmer discipline.
3. **Effekt enforces lexical capability lifetime safety, which is orthogonal to single-shot linearity.** Treating effect handlers as lexically scoped second-class capabilities (OOPSLA 2020) and tracking escaped closures with `Box` capture sets (OOPSLA 2022) statically prevents handler escape and accidental dynamic capture, but does not restrict resumption multiplicity: multi-shot `resume` remains permitted and requires an orthogonal linearity discipline to prevent capability duplication or 0-shot abandonment.
4. **OCaml 5 enforces at-most-once dynamically and leaves at-least-once unchecked; OxCaml adds static modal affinity and effect-yielding axes.** OCaml 5's runtime destructively consumes continuations so a second `continue`/`discontinue` raises `Effect.Continuation_already_resumed`, while requiring programmers by convention to call `Effect.Deep.discontinue` to unwind abandoned fibers and run `Fun.protect` cleanup. The Iris-based separation logic for effect handlers of de Vilhena and Pottier (POPL 2021) is restricted to one-shot continuations (permitting exclusive ownership transfer across `perform`/`resume`), sketching multi-shot protocols only as future work (§8). OxCaml (Lorenzen et al., ICFP 2024; OxCaml Mode System) introduces orthogonal static modes—`local`/`global` (escape), `unique`/`aliased` (past ownership), `once`/`many` (future closure affinity, statically banning $\ge 2$-shot invocation of closures capturing `unique` values), and `yielding`/`unyielding` (whether a function may perform effects handled in its parent stack)—enforcing affine non-duplication statically while still permitting 0-shot dropping.
5. **Rust `Pin<P>` + `Future::poll` replaces linear drop-always with a conditional drop-before-storage-reuse invariant.** Stackless `async` state machines prevent $\ge 2$-shot frame duplication through affine `&mut` ownership, while RFC 1066 (`std::mem::forget`) explicitly establishes that Rust is affine (0-shot drop-skipping is memory-safe). RFC 2349 and `std::pin` reconcile self-referential suspended coroutines with safe leaking via the **Drop guarantee**: once a `!Unpin` value is pinned, its address cannot move and its backing storage cannot be deallocated, overwritten, or reused until `Drop::drop` runs to completion. Leaking via `mem::forget` is sound precisely because leaked storage is never reused, whereas bypassing `Drop` before reuse (such as projecting `Pin` inside `ManuallyDrop`) causes undefined behavior.
6. **Lean `v4.34.1` toy mechanization (`lean/`).** Fourteen kernel-checked theorems with zero `sorry` and at most the standard Lean axiom `[propext]` (11 of 14 theorems depend on zero axioms; `[kernel-checked proof]` `[toy model]`; **Model–system relation: none proved.**) formalize: (a) 2-shot double-consumption of a syntactically value-linear body, (b) 0-shot silent `dropK` leaking a capability even inside `withFinally`, (c) inductive exact single-use soundness (`acquired = true ∧ consumes = 1 ∧ faultDoubleConsume = false`) for all well-typed programs under control-flow linearity plus explicit `discontinue`/`withFinally` discipline (with static rejection proofs for the counterexamples), and (d) structural `Pin` separation showing unpinned moves invalidate internal self-pointers, drop-skip-then-reuse violates the `Pin` Drop guarantee, `mem::forget` without reuse preserves it, and arbitrary traces of `Pin`-conforming operations preserve both invariants inductively.

## Applicability

This report is a comparative analysis of formal typing disciplines, operational soundness mechanisms, and official specifications across five paradigms, evaluated against the specific problem of preventing linear/affine capability duplication ($\ge 2$-shot) and cleanup-skipping (0-shot) under delimited control:

| Subject group | Role in this report | Relationship among subjects |
| --- | --- | --- |
| Tang et al. (`10.1145/3632896`, `arXiv:2307.09383v2`), Tov & Pucella (`10.1145/1926385.1926436`), Petricek et al. (`10.1145/2628136.2628160`), Atkey (`10.1145/3209108.3209189`), Orchard et al. (`10.1145/3341714`) | Formal type-theoretic foundations (control-flow linearity, affine kinds, coeffect/QTT/graded-modal calculi) | Establishes the theoretical taxonomy against which the four language designs below are compared |
| Leijen (`10.1145/3009837.3009872`, `MSR-TR-2018-10`), Reinking et al. (`10.1145/3453483.3454032`) | Koka operation sorts, deep finalization (`initially`/`finally`), `linear effect`, and Perceus RC reuse under multi-shot control | Contrasts runtime deep finalization + RC memory safety against static control-flow linearity |
| Brachthäuser et al. (`10.1145/3428194`, `10.1145/3527320`) | Effekt second-class lexical capabilities, `Box` capture polymorphism, and region/lifetime safety | Separates lexical capability escape safety (coeffect/region safety) from single-shot continuation linearity |
| Sivaramakrishnan et al. (`10.1145/3453483.3454039`), de Vilhena & Pottier (`10.1145/3434314`), OCaml 5.3 Manual, Lorenzen et al. (`10.1145/3674642`), OxCaml Mode System docs | Dynamic one-shot fibers + `discontinue` convention, separation-logic protocol rules, and static modal `local`/`unique`/`once`/`yielding` axes | Shows progression from dynamic one-shot checks to static modal affinity + effect-yielding modes |
| Rust RFC 2349, RFC 1066, `std::pin` documentation (`std 1.100.0`, `rust-lang/rust` commit `0ef1bc386059596dada8fb65b50425aab2ea637a`, stabilized `1.33.0`) | Stackless delimited continuations (`Future::poll`), affine `mem::forget`, structural pinning, and drop-before-storage-reuse | Demonstrates how a systems language with affine drop-skipping soundly hosts address-sensitive suspended frames |
| Lean 4 (`leanprover/lean4` `v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`) | Executable formal toy model (`lean/Toy/LinearEffects.lean`, `lean/Toy/PinInvariant.lean`) | Mechanizes the core counterexamples and preservation theorems; **Model–system relation: none proved.** |

**Cross-references to adjacent corpus packages (material intentionally NOT duplicated here):**
- Evidence-passing compilation (`evv`, `yield-bind`, `clause-tail*`), dynamic vs. lexical dispatch benchmarks, OCaml 5 fiber C struct layout/sizes, and handler-ordering non-commutativity are covered in `algebraic-effects-handlers-coeffects-and-capability-tracking`.
- Core compiler lowering pipelines for Koka (`Core.AnalysisResume`) and Effekt (`CapabilityScope`, `effekt/machine/Tree.scala`), WebAssembly Stack Switching, WASI Preview 3 Component Model Async Canonical ABI, OpenJDK JEP 491 native-frame pinning, and LLVM `swifterror` register channels are covered in `control-flow-linearity-effect-compilation-and-stackless-stackful-unification`.
- `rustc` MIR coroutine state-machine lowering (`StateTransform`), unwind drop flags, and borrow-checker internals for Rust generators/async blocks are covered in `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics`, `pin-structural-projection-address-stability-and-drop-guarantee`, and `rust-pin-drop-guarantee-mem-forget-leaks-and-async-cancellation-invariants`.

Scope limits:
- All claims about OCaml 5, OxCaml, Koka, Effekt, and Rust derive from published papers, RFCs, and official specifications/documentation observed on `2026-11-22`; no compiler binaries for those languages were executed here.
- **Model–system relation: none proved.** The Lean `v4.34.1` proofs establish exact properties of the self-contained toy calculi in `lean/Toy/`, not mechanized soundness proofs of `rustc`, `ocamlopt`, `koka`, or `effekt`.

## Findings

### 1. The Two-Sided Linearity Collision Under Delimited Control

Basis: documentation (`10.1145/3632896`, `arXiv:2307.09383v2`) + derived + execution (`[kernel-checked proof]` `[toy model]`)

Let a delimited computation acquire a resource $r$ whose soundness contract requires consumption multiplicity $m \in \{1\}$ (strictly linear: session channel completion, `!Drop` DMA descriptor, lock release) or $m \le 1$ (affine: exclusive `&mut` borrow, uniquely owned heap buffer with destructor), perform a handled effect operation `op()` while $r$ is live, and consume $r$ after `op()` returns:

```text
let r = acquire() in
let x = perform op() in   -- delimited continuation k = λx. consume(r, x)
consume(r, x)
```

Syntactically, `r` appears linearly (used once along the lexical path). Operationally, however, `k` closes over `r`, so the actual dynamic consumption count of `r` equals the **resumption multiplicity** of `k` inside the enclosing handler:

| Handler behavior on `k` | Dynamic consumption count of `r` | Affine type (`≤ 1` use) | Linear type (`= 1` use) | Failure mode |
| --- | --- | --- | --- | --- |
| **1-shot (`continue k v`)** | $1$ | Sound | Sound | None |
| **$\ge 2$-shot (`continue k v₁; continue k v₂`)** | $\ge 2$ | **Unsound** | **Unsound** | Capability duplication, double-free, double-close, use-after-free, aliased `&mut` |
| **0-shot silent drop (ignore `k`)** | $0$ | Memory-safe only if storage is never reused / no drop-required invariant | **Unsound** | Linear resource leak, protocol deadlock, bypassed `finally`/RAII cleanup |
| **0-shot explicit unwind (`discontinue k e` / `final ctl`)** | $1$ if guarded by `finally`/drop shim; $0$ if unguarded | Sound (with deterministic unwind) | Sound **iff** every live linear resource has a matching unwind finalizer | Leak if unguarded; double-free if body also consumed manually |

This separation explains why **affine-only mechanisms** (dynamic one-shot checks, OxCaml `once`, Rust ownership) and **unwind-only mechanisms** (Koka `finally`, exception handlers) each solve only half of the collision, and why full linear soundness requires coordinating **both** the handler's shot count and the presence of live resources across suspension points.

---

### 2. Control-Flow Linearity, Affine Kind Systems, and Graded Coeffects

Basis: documentation (`10.1145/3632896`, `arXiv:2307.09383v2`, `10.1145/1926385.1926436`, `10.1145/2628136.2628160`, `10.1145/3209108.3209189`, `10.1145/3341714`) + derived

#### 2.1 Control-Flow Linearity ($F^\circ_{\text{eff}}$ and $Q^\circ_{\text{eff}}$, Tang et al. POPL 2024)

Tang, Hillerström, Lindley, and Morris (`10.1145/3632896`, `arXiv:2307.09383v2`) identify the missing static invariant as **control-flow linearity**, dual to value linearity:

- **Two orthogonal linearity dimensions:**
  - *Value linearity* classifies whether a value may be duplicated or discarded (`Unr` vs. `Lin`, with subkinding allowing unrestricted values in linear positions or linear-polymorphic abstraction).
  - *Control-flow linearity* classifies effect operations and effect rows by whether their handlers invoke the captured continuation linearly (exactly once) or unrestrictedly (`0` or $\ge 2$ times).
- **Continuation-capture soundness rule:** In $F^\circ_{\text{eff}}$ (a System F-style core calculus), whenever a subexpression performs an effect row $E$ while any linear binding is live in the surrounding evaluation context, $E$ must be **control-flow linear**. Equivalently, a handler clause for a control-flow-linear operation receives a **linear** resumption $k : A \multimap B$, so both duplicating $k$ ($\ge 2$-shot) and discarding $k$ (0-shot) are statically ill-typed. Conversely, an unrestricted (`Unr`) operation (exceptions, backtracking) is permitted whenever no linear variables span the operation's evaluation context; its continuation cannot capture linear resources.
- **Metatheory:** $F^\circ_{\text{eff}}$ is equipped with a **linearity-aware operational semantics** that explicitly tracks linear value usage during reduction. Tang et al. prove **Progress**, **Preservation (Subject Reduction)**, and **linear value integrity** (no linear value is ever duplicated or discarded during evaluation). Applying this design to the Links programming language eliminated a long-standing soundness bug where linear session channels could be duplicated or dropped by multi-shot/abortive effect handlers.
- **Annotation-free inference ($Q^\circ_{\text{eff}}$):** Because explicit System F linearity annotations hinder higher-order polymorphism, $Q^\circ_{\text{eff}}$ embeds both value linearity and control-flow linearity into **qualified types** (predicates constraining linearity variables and effect rows). $Q^\circ_{\text{eff}}$ supports full type inference with zero programmer annotations, linearity polymorphism, and linearity dependencies between type variables (e.g., typing a polymorphic container or higher-order combinator as linear iff its element or callback is linear).

#### 2.2 Practical Affine Types (Alms, Tov & Pucella POPL 2011)

Tov and Pucella (`10.1145/1926385.1926436`) formalize **Alms**, an ML-style affine language with two mechanisms directly relevant to capability soundness:
- **Kind-indexed subkinding (`A` vs. `U`):** Types have kinds classifying them as *affine* (`A`, usable at most once) or *unlimited* (`U`, freely duplicable), with subkinding `U ≤ A`. Function arrows carry kind qualifiers so a closure capturing an affine capability is itself affine (at-most-once invocation), preventing $\ge 2$-shot duplication via closure invocation—a direct precursor to OxCaml's `unique`/`once` interaction.
- **Abstract affine sealing via module signatures:** ML signature ascription can seal an unlimited internal representation behind an opaque affine abstract type, enforcing single-use capability protocols at module boundaries.
- **Metatheory and limit:** Alms proves syntactic type soundness and principal kinding. However, because Alms is **affine rather than linear**, dropping a capability (0-shot discard) is always well-typed; Alms prevents capability duplication ($\ge 2$-shot) but relies on runtime finalizers/GC rather than static linearity to reclaim dropped resources.

#### 2.3 Graded Coeffects and Quantitative Type Theory (Petricek et al. 2014; Atkey 2018; Orchard et al. 2019)

Graded coeffect and quantitative type systems unify linearity, affinity, and bounded reuse over an ordered semiring $(R, +, 0, \cdot, 1, \le)$:
- **Structural coeffects (Petricek, Orchard & Mycroft, ICFP 2014, `10.1145/2628136.2628160`):** Typing judgments $\Gamma @ \mathbf{r} \vdash e : \tau$ attach a coeffect vector to variables, using sequential composition ($\circledast$, unit `use`), parallel sharing ($\oplus$, unit `ign`), and sub-coeffecting ($\le$). Under the $\{0, 1, \omega\}$ semiring, grading a handler clause's resumption parameter $k$ directly encodes shot multiplicity ($0$ = unused/abort, $1$ = linear/one-shot, $\omega$ = multi-shot).
- **Quantitative Type Theory (Atkey, LICS 2018, `10.1145/3209108.3209189`):** Separates $0$-use (erased, type-level/proof-only) bindings from $1$-use (linear runtime) and $\omega$-use (unrestricted) bindings in dependent type theory, establishing that semiring-graded contexts scale cleanly to dependent specifications.
- **Granule (Orchard, Liepelt & Eades III, ICFP 2019, `10.1145/3341714`):** Combines graded necessity modalities $\Box_r A$ (coeffects, tracking resource consumption) with graded possibility/effect modalities (tracking side effects) in a single type checker.

**Derived synthesis:** Relative to $F^\circ_{\text{eff}}$, semiring grading exposes an important refinement needed for systems languages: a pure 3-element grade $\{0, 1, \omega\}$ treats 0-shot abort as "unused" (`0`), which cannot distinguish **silent drop** (leaking a live linear resource) from **structured unwind** (invoking `discontinue` / `final ctl` once to run `finally` destructors). Modeling unwind-safe abort requires either splitting grade `0` into `0_drop` vs. `0_unwind` (as in our Lean toy model's `abortDiscontinue` grade) or encoding unwinding itself as a linear consumption of the continuation through an exceptional entry point.

---

### 3. Koka: Operation Sorts, Deep Finalization, Linear Effects, and Perceus RC Reuse

Basis: documentation (`10.1145/3009837.3009872`, `MSR-TR-2018-10`, `10.1145/3453483.3454032`, Koka Book) + derived

Koka's handler design (Leijen, POPL 2017; `MSR-TR-2018-10`, 2018) separates control-flow discipline into four static **operation sorts** and two runtime resource primitives:

| Koka construct | Resumption behavior | Prevents $\ge 2$-shot duplication? | Prevents 0-shot cleanup skip? | Mechanism |
| --- | --- | --- | --- | --- |
| `val` / `fun` (tail-resumptive) | Implicitly resumes exact 1 time in tail position | **Yes (static)** | **Yes (static)** | No continuation captured; runs in place |
| `linear effect` | Restricts all operations in the effect to tail-resumptive (`val`/`fun`) | **Yes (static)** | **Yes (static)** | Koka Book §3.4.12 restricts operations of a `linear effect` to tail-resumptive form (compiler parser-level enforcement is documented in `algebraic-effects-handlers-coeffects-and-capability-tracking`) |
| `final ctl` | Never resumes normally (0-shot) | **Yes (static)** | **Yes (runtime unwind)** | Final yield unwinds stack frames and runs every enclosing `finally` |
| `ctl` (general control) | Arbitrary (0, 1, or $\ge 2$ resumptions) | **No** | **Yes (runtime unwind)** | Unresumed `ctl` clauses automatically trigger finalization of the captured resumption, running enclosing `finally` handlers |
| `raw ctl` | Arbitrary, bypassing automatic protection | **No** | **No (opt-out)** | Exposes raw `resume` and explicit `finalize` |

**Deep finalization (`finally`) and multi-shot re-entry (`initially`):**
- In `MSR-TR-2018-10`, Leijen formalizes **deep finalization** so that `finally(fin, action)` executes `fin` both on normal exit and when an inner `final ctl` or unresumed `ctl` aborts past the scope—ensuring nested handlers unwind cleanly in LIFO order.
- For multi-shot resumptions, Koka provides `initially(init, action)` to run initialization logic on entry and again whenever a continuation is resumed more than once. Koka Book §3.4.11 illustrates a reference-counted `with-file` idiom in which `initially` increments a counter `count` on each resumption and `finally` closes the file handle only when `count == 1`, achieving single close even under multi-shot `ctl`. Crucially, however, Koka does **not statically forbid** multi-shot `ctl` over external linear resources: using `finally` alone double-closes on multi-shot resumption, and maintaining the reference-counted `initially`/`finally` idiom remains an unchecked programmer obligation.

**Interaction with Perceus reference counting and reuse (Reinking, Xie, de Moura & Leijen, PLDI 2021, `10.1145/3453483.3454032`):**
- Perceus inserts precise, garbage-free `dup`/`drop` operations and compiles functional updates to in-place memory reuse (`reuse` tokens) whenever a runtime uniqueness check confirms reference count $= 1$.
- **Derived interaction with multi-shot `ctl` (`derived`; the Perceus PLDI 2021 paper does not itself analyze multi-shot continuations):** Because a captured continuation closure is a reference-counted heap structure, a **1-shot** resumption observes reference count 1 and preserves in-place reuse, whereas on a **$\ge 2$-shot** resumption the shared continuation closure carries reference count $> 1$, causing Perceus's dynamic uniqueness checks to retain/duplicate captured heap values and **disable in-place reuse**, falling back to non-destructive allocation.
- **Crucial soundness boundary (`derived`):** Perceus guarantees **heap memory safety** (no heap double-free or use-after-free) under arbitrary multi-shot `ctl` because RC tracks pointer multiplicity dynamically at runtime. However, Perceus does *not* statically enforce **linear capability safety** for external/side-effecting resources (file descriptors, locks, session protocols), because duplicating a handle value with RC $= 2$ still permits two independent `close(fd)` calls unless guarded manually (for example via the `initially`/`finally` counter idiom above).

---

### 4. Effekt: Second-Class Lexical Capabilities, Boxes, and Lifetime Safety

Basis: documentation (`10.1145/3428194`, `10.1145/3527320`) + derived

Effekt (Brachthäuser, Schuster & Ostermann, OOPSLA 2020; Brachthäuser, Schuster, Lee & Boruch-Gruszecki, OOPSLA1 2022) replaces row-polymorphic dynamic effect dispatch with **lexically scoped second-class capabilities**:

- **Second-class block discipline (OOPSLA 2020):** Functions and effect handlers are treated as second-class blocks passed downward as contextual capabilities. Because second-class blocks cannot be returned from their defining scope or stored in heap cells, a capability can never outlive the dynamic extent of the handler that binds it. Higher-order functions automatically obtain lightweight effect polymorphism without effect-row variables.
- **Crossing the boundary via `Box` (OOPSLA1 2022):** When a block must become first-class (returned or stored in data structures), Effekt's System C wraps it in a `Box` whose type tracks its **capture set** (the lexical capabilities/regions it closes over). Unboxed/returned values are checked so no captured capability escapes its binding handler or region scope.
- **Orthogonality of lexical lifetime safety and continuation linearity (`derived`):**
  - Effekt's second-class and `Box` disciplines completely eliminate **use-after-handler-exit** (dangling capability invocation) and **accidental dynamic capture** (effect tunneling).
  - They do **not**, however, restrict **resumption multiplicity**: Effekt's delimited control primitives (`Reset`/`Shift`/`Resume`) support multi-shot resumption (copying shared stack segments on shared resume) and 0-shot abort. Therefore, if a computation holds an external linear capability across a `Shift`, lexical capability scoping alone prevents neither $\ge 2$-shot duplication nor 0-shot drop-skipping—confirming that **escape safety (locality/capture checking)** and **resumption linearity (shot-count grading)** are distinct, orthogonal soundness axes.

---

### 5. OCaml 5 and OxCaml: Dynamic One-Shot Fibers, `discontinue`, Separation Logic, and Modal Modes

Basis: normative (OCaml 5.3 Manual) + documentation (`10.1145/3453483.3454039`, `10.1145/3434314`, `10.1145/3674642`, OxCaml Mode System docs) + derived

#### 5.1 OCaml 5 Dynamic One-Shot Enforcement and the Unchecked `discontinue` Obligation

In mainline OCaml 5 (Sivaramakrishnan et al., PLDI 2021; OCaml 5.3 Reference Manual, Section 24):
- **At-most-once ($\le 1$) is enforced dynamically:** Resuming a continuation via `Effect.Deep.continue` or `Effect.Deep.discontinue` (or their `Effect.Shallow` / `_with_backtrace` counterparts) destructively nulls out the continuation's fiber pointer; any subsequent attempt raises `Effect.Continuation_already_resumed`. This statically eliminates stack copying and dynamically rules out $\ge 2$-shot duplication of resources held inside suspended frames.
- **At-least-once ($\ge 1$) is NOT enforced:** The OCaml 5.3 manual explicitly states the discipline *"every captured continuation must be resumed either with a `continue` or `discontinue` exactly once"* and warns that dropping a continuation without calling `discontinue` silently skips all `try ... with` and `Fun.protect` cleanup blocks inside the suspended fiber (0-shot drop-skipping), leaking both the fiber stack and any held resources (such as open output channels). Calling `Effect.Deep.discontinue k exn` injects `exn` at the `perform` site, unwinding the suspended fiber so `Fun.protect` finalizers execute deterministically.
- **Program-logic verification (de Vilhena & Pottier, POPL 2021, `10.1145/3434314`):** Building on Iris separation logic, de Vilhena and Pottier formalize a separation logic for effect handlers that is explicitly **restricted to one-shot continuations**, enabling protocols to transfer exclusive (linear/affine) ownership across `perform` and `resume` boundaries. Extending the logic to multi-shot continuations (where captured assertions would need to be persistent/duplicable) is left as **future work** (sketched only in §8 of the paper, not formalized).

#### 5.2 OxCaml Modal Memory Management and Effect Modes (Lorenzen et al., ICFP 2024; OxCaml Docs)

Lorenzen, White, Dolan, Eisenberg, and Lindley (*Oxidizing OCaml with Modal Memory Management*, ICFP 2024, `10.1145/3674642`) and the OxCaml compiler documentation extend OCaml with backwards-compatible, fully inferred **modal axes** separating *past* modes (what already happened to a value) from *future* modes (what may still happen to it):

| OxCaml Mode Axis | Kind | Ordering (least $\to$ greatest) | Role in capability & continuation soundness |
| --- | --- | --- | --- |
| **Locality** | Future | `global` $\le$ `local` | Prevents stack-allocated or region-bound values from escaping their lexical scope (analogous to Effekt/Scala capture locality) |
| **Uniqueness** | Past | `unique` $\le$ `aliased` | Tracks exclusive single-reference ownership; consuming a `unique` argument statically prevents use-after-free and double-free |
| **Linearity (Affinity)** | Future | `many` $\le$ `once` | Tracks closure invocation multiplicity: any closure capturing a `unique` value is forced to mode `once`, statically ruling out $\ge 2$-shot invocation |
| **Yielding** | Future | `unyielding` $\le$ `yielding` | Tracks whether a function may perform OCaml 5 effects handled in its parent stack (`global` defaults to `unyielding`; `local` defaults to `yielding`) |

Key soundness properties and boundaries of OxCaml's modal approach:
1. **Static $\ge 2$-shot prevention via `unique` + `once`:** A closure that closes over a `unique` resource receives mode `once` (e.g., `val delay_free : t @ unique -> (unit -> unit) @ once`), so calling it twice is a **compile-time error** rather than a runtime `Continuation_already_resumed` exception.
2. **Mode crossing and type abstraction:** Primitive register-passed values (such as `int`) **mode-cross** locality and uniqueness by default. OxCaml's documentation explicitly notes that unboxed OS handles (such as an `int` file descriptor) must be wrapped in an **abstract type** to inhibit mode crossing so they cannot escape a `local` scope or silently duplicate across `unique`/`aliased`.
3. **Affine, not strictly linear:** OxCaml's `once` mode enforces **at-most-once** (affinity), not **at-least-once** (strict linearity): discarding an unused `unique` value or `once` closure (0-shot drop-skipping) remains well-typed, so mandatory resource release on abort still requires structured scoping or unwinding (`discontinue` / `Fun.protect`).
4. **Effect-stack interaction (`yielding`):** Separating `unyielding` from `yielding` functions prevents stack-allocated `local` frames from being unexpectedly suspended across parent-stack effect handlers unless explicitly permitted.

---

### 6. Rust `Pin<P>`, `Future::poll`, Affine `mem::forget`, and the Drop-Before-Storage-Reuse Guarantee

Basis: normative (RFC 2349, RFC 1066, `std::pin` documentation `std 1.100.0` / `0ef1bc386059596dada8fb65b50425aab2ea637a`) + derived + execution (`[kernel-checked proof]` `[toy model]`)

Rust implements delimited suspension without stackful fiber switching by compiling `async fn` / coroutine blocks into **stackless state-machine structs** polled via:

```rust
pub trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

Evaluating Rust's model through the delimited-continuation lens exposes three sharp invariants:

1. **Static $\ge 2$-shot prevention via affine ownership (`&mut`):** Unlike multi-shot effect continuations, a Rust `Future` frame is an ordinary affine value. Polling requires exclusive mutable access (`Pin<&mut Self>`), and compiler-generated `async` futures do not implement `Copy` or `Clone`, statically preventing $\ge 2$-shot duplication of any live local variables or borrows held across an `.await` suspension point.
2. **Explicit 0-shot drop-skipping is memory-safe (RFC 1066 — Affine, Not Linear):** RFC 1066 (*Alter the signature of `std::mem::forget` to remove `unsafe`*, 2015) established that safe Rust can already skip destructors via `Rc`/`Arc` reference cycles, making Rust fundamentally **affine** rather than linear. Thus:
   - *Async cancellation* (dropping a suspended `Future` before `Poll::Ready`) is a **0-shot abort with deterministic unwinding**: Rust runs the generated state machine's `Drop` shim for every live field in the current suspended variant.
   - *Leaking a `Future`* (`std::mem::forget(Box::pin(fut))`) is a **0-shot abort without running `Drop`**: safe code can legally skip every destructor inside the suspended coroutine. Therefore, Rust unsafe abstractions (unlike $F^\circ_{\text{eff}}$ linear types) **cannot rely on `Drop` always executing** for soundness (the original `thread::scoped` failure).
3. **Reconciling self-referential continuations with affine leaking via `Pin<P>` and the Drop Guarantee (RFC 2349, stabilized in Rust 1.33.0; `std::pin`):**
   - Because Rust values are trivially byte-wise movable (`memcpy` without pointer fixup), moving a suspended `async` state machine containing an interior pointer (`&self.buf`) to a new address immediately creates a dangling pointer.
   - `Pin<Ptr>` (`!Unpin` pointees) enforces **two coupled invariants**:
     1. *Address stability:* Once pinned, the pointee cannot be moved out of its memory location via safe code.
     2. *The Drop guarantee (drop-before-storage-reuse):* The backing memory of a pinned `!Unpin` value **must remain valid and cannot be deallocated, overwritten, or reused until `Drop::drop` runs to completion**.
   - **Why `mem::forget` is sound under `Pin` while `ManuallyDrop` projection is unsound:** Calling `mem::forget` on `Pin<Box<T>>` skips `Drop`, but the heap allocation is permanently leaked and **never reused or invalidated**, so internal self-pointers and intrusive list links never dangle. By contrast, projecting `Pin<&mut T>` inside `Pin<Box<ManuallyDrop<T>>>` and then dropping the outer `Box` deallocates and reuses `T`'s memory *without* running `T::drop`, violating the Drop guarantee and causing immediate undefined behavior (`std::pin` Drop guarantee section).
   - **Structural pinning contract:** For any compound struct exposing a projection `Pin<&mut Struct> -> Pin<&mut Field>`, the author must uphold three requirements: (a) *consistency* (never also project `&mut Field` for a structurally-pinned `!Unpin` field), (b) *structural `Unpin`* (the struct may implement `Unpin` only if all structurally-pinned fields are `Unpin`), and (c) *pinned destruction* (`Drop::drop(&mut self)` must treat `self` as `Pin<&mut Self>`, which also forbids `#[repr(packed)]` because Rust moves packed fields out of unaligned storage during drop).

---

### 7. Comparative Soundness Matrix

Basis: derived synthesis from Sections 2–6.

| Mechanism / System | Enforcement locus | Blocks $\ge 2$-shot duplication? | Blocks 0-shot drop-skipping? | Escape / address-stability guarantee | Key residual obligation / limit |
| --- | --- | --- | --- | --- | --- |
| **$F^\circ_{\text{eff}}$ / $Q^\circ_{\text{eff}}$** (Tang et al., POPL '24) | Static (type/qualified inference) | **Yes** (forbids `Unr` ops across live linear vars) | **Yes** (`Lin` continuation must be invoked once) | N/A (value/control-flow linearity) | Disallows 0-shot abort across live linear values unless linearized or finalized |
| **Alms** (Tov & Pucella, POPL '11) | Static (affine kinds + module sealing) | **Yes** (affine closures usable $\le 1$) | **No** (affine discard allowed) | N/A | Relies on GC/finalizers for abandoned resources |
| **Graded Coeffects / QTT / Granule** (2014–2019) | Static (semiring grades) | **Yes** (grade `1` or affine `≤ 1`) | **Yes** (exact grade `1`; requires unwind split for `0`) | Region/graded modalities | Requires separating `0_unwind` from `0_drop` for abortive handlers |
| **Koka** (`fun`/`ctl`/`final ctl`, `finally`, Perceus) | Hybrid (static sorts + runtime RC & unwind) | **Only for `fun`/`linear effect`** (`ctl` allows $\ge 2$-shot) | **Yes** (deep finalization on `final ctl` and unresumed `ctl`; opt-out via `raw ctl`) | Perceus RC keeps heap memory safe (`derived`) | No static ban on multi-shot `ctl` across external linear handles; safe multi-shot cleanup (e.g., ref-counted `initially`/`finally` in Book §3.4.11) is a programmer obligation |
| **Effekt** (2nd-class capabilities + `Box`) | Static (scope & capture sets) | **No** (multi-shot `resume` supported) | **No** (0-shot abort supported) | **Yes** (no handler/region escape) | Orthogonal to shot-count linearity |
| **OCaml 5** (`Effect.Deep`) | Dynamic (runtime fiber check) | **Yes** (runtime `Continuation_already_resumed`) | **No** (dropped fibers silently leak) | No static effect typing | Programmer must ensure every continuation hits `continue` or `discontinue` |
| **OxCaml** (`local`/`unique`/`once`/`yielding`) | Static (modal type system) | **Yes** (`unique` captures force `once` closure) | **No** (`once` is affine, not linear) | **Yes** (`local` prevents escape; `yielding` tracks effectful parent stack) | Mode-crossing types (e.g., `int` FDs) require abstract wrappers; 0-shot leaks allowed |
| **Rust `Pin<P>` + `Future::poll`** (RFC 2349/1066) | Static (`&mut` + `Pin`) + `unsafe` contract | **Yes** (affine `&mut` poll, no cloning) | **Conditional**: drop required *before storage reuse*; `mem::forget` leak allowed | **Yes** (pinned address stability + structural pinning) | Linear `!Drop` protocols cannot rely on `Drop` always running; `unsafe` pin projections must uphold Drop guarantee |

---

### 8. Mechanized Lean `v4.34.1` Toy Model (`lean/`)

Basis: execution (`[kernel-checked proof]` `[toy model]`, Lean `v4.34.1`, zero `sorry`, at most `[propext]`). **Model–system relation: none proved.**

The package includes a Mathlib-free Lean 4 (`v4.34.1`) mechanization under `lean/Toy/` with two self-contained modules:

1. **`Toy/LinearEffects.lean`** models a delimited-control computation AST (`acquire`, `consume`, `perform`, `withFinally`, `branch`) evaluated under handler clauses (`dropK`, `continueOnce`, `discontinueOnce`, `continueTwice`, `branch`) and an operation grade (`lin`, `abortDiscontinue`, `unr`):
   - **Part (a) — 2-shot duplication (`two_shot_duplicates_linear_capability`):** Executing a syntactically value-linear body `acquire (perform (consume pure))` under `continueTwice` terminates with `consumes = 2` and `faultDoubleConsume = true`.
   - **Part (b) — 0-shot drop-skipping (`zero_shot_abort_skips_linear_cleanup`, `zero_shot_drop_bypasses_finally`):** Executing the same body under `dropK` terminates with `acquired = true` and `consumes = 0`; crucially, even wrapping the suspension point in `withFinally (consume pure) (perform pure)` still yields `consumes = 0` under silent `dropK`, mechanizing why OCaml's dropped continuations (and Rust's `mem::forget`) bypass enclosing cleanup blocks.
   - **Part (c) — Exact single-use soundness (`typed_eval_sound`, `wellTypedProgram_exact_single_use`):** Defining a phase-indexed control-flow-linear typing judgment `Typed g phIn hasCleanup c phOut` (which forbids `.unr` operations while the capability is `.live`, requires `hasCleanup = true` for `.abortDiscontinue` while `.live`, forbids manual `consume` while `hasCleanup = true`, and pairs `ClauseTyped` to require `continueOnce` for `.lin` and `discontinueOnce` for `.abortDiscontinue`) proves inductively that **every** well-typed program terminates with `acquired = true ∧ consumes = 1 ∧ faultDoubleConsume = false`. Auxiliary theorems prove static rejection of both counterexamples (`twoShotProgram_rejected`, `zeroShotDropProgram_rejected`) and well-typedness of 1-shot linear, `abortDiscontinue` + `withFinally`, and post-consumption 2-shot unrestricted programs.

2. **`Toy/PinInvariant.lean`** models a stackless self-referential coroutine frame (`CoroFrame`) with `payloadOffset = 8`, states `unpolled | suspended (selfPtr : Nat) | completed`, and storage lifecycle `allocated | dropped | reused | leaked`:
   - **Part (d1) — Unpinned move counterexample (`unpinned_move_breaks_self_ref`):** For any suspended allocated coroutine satisfying `SelfRefValid` at `addr` and any `newAddr ≠ addr`, byte-wise relocation (`unpinnedMove`) falsifies `SelfRefValid`.
   - **Part (d2) — Drop-skip-before-reuse counterexample (`skip_drop_then_reuse_violates_drop_guarantee`):** Reusing storage of a pinned coroutine without running `Drop` first falsifies `DropBeforeReuseGuarantee`.
   - **Part (d3) — Affine `mem::forget` separation (`mem_forget_without_reuse_preserves_pin_invariants`):** Transitioning allocated storage to `.leaked` (never `.reused`) preserves `PinInvariant`.
   - **Part (d4) — Inductive `Pin` trace preservation (`pinned_trace_preserves_invariants`):** Any finite trace `ops : List PinOp` of `Pin`-conforming operations (`pinInPlace`, `poll`, `mutateFieldInPlace`, `runDrop`, `reuseAfterDrop`, `memForget`) starting from a fresh coroutine at `addr` preserves both `SelfRefValid` and `DropBeforeReuseGuarantee` and keeps `final.addr = addr`.
   - *Model-scope disclosure:* In `Toy/PinInvariant.lean`, `skip_drop_then_reuse_violates_drop_guarantee` (d2) is a direct unfolding of `DropBeforeReuseGuarantee`, and `pinned_trace_preserves_invariants` (d4) holds largely by construction because `PinOp` omits unsound storage-invalidation constructors and `stepPinOp` turns out-of-precondition steps into no-ops; these theorems witness internal consistency of the abstract `Pin` state-machine interface rather than deriving safety from low-level memory semantics.

## Boundaries

- **Model–system relation: none proved.** The Lean `v4.34.1` toy model (`lean/Toy/`) proves exact properties of its own finite ASTs and single-capability / single-frame state machines; it does **not** prove soundness of `rustc`, `ocamlopt`, `oxcaml`, `koka`, `effekt`, Links, or Alms, nor does it model aliasing, multi-capability environments, heap allocation, or Stacked/Tree Borrows.
- **Not examined:**
  - Live execution or compiler-source auditing of OxCaml's compiler implementation (`oxcaml/oxcaml`), Alms's prototype compiler, or Granule's solver; claims about them rest on published papers and official documentation.
  - Shallow handlers in OCaml 5 (`Effect.Shallow`) and Koka beyond noting that OCaml's `Effect.Shallow.continue_with` / `discontinue_with` enforce the same dynamic one-shot `Continuation_already_resumed` check.
  - Rust nightly `AsyncDrop` / linear-type proposals (`MustMove` / `?Leak` designs), which are not part of stabilized Rust `std::pin` / RFC 2349.
  - Multi-threaded / cross-domain continuation transfer in OCaml 5 and OxCaml's `portable`/`contended` axes (outside the single-thread linearity/effect seam).
- **Unknown:**
  - Whether future Koka versions will adopt a static control-flow-linearity discipline (like $Q^\circ_{\text{eff}}$) to statically forbid multi-shot `ctl` across external linear resources.
  - Whether OxCaml will extend its `yielding`/`once`/`unique` modes to statically track `Effect.Deep.discontinue` (at-least-once unwinding) for OCaml 5 continuations; the examined OxCaml mode documentation specifies `once` as affine (at-most-once) and does not document linear (at-least-once) continuation checking.
- **Known not to apply:**
  - Koka's Perceus reference counting guarantees heap memory safety only; it does **not** statically forbid multi-shot `ctl` across external linear capabilities (such as OS file descriptors), so avoiding double-close under multi-shot resumption relies on programmer-maintained runtime idioms such as the reference-counted `initially`/`finally` pattern in Koka Book §3.4.11.
  - Effekt's second-class capabilities and `Box` capture checking do **not** prevent $\ge 2$-shot duplication or 0-shot abandonment of linear capabilities across `Shift`/`Resume`.
  - Rust's `Pin` Drop guarantee does **not** make Rust a linear type system: safe `std::mem::forget` legally skips `Drop` whenever backing storage is never reused.
- **Unsupported:**
  - Mainline OCaml 5 does not support multi-shot continuations (second resumption always raises `Effect.Continuation_already_resumed`).
  - Rust `#[repr(packed)]` structs cannot soundly participate in structural pinning because dropping packed fields may move them.
- **Stronger conclusions avoided:** None of the production systems surveyed simultaneously offers unannotated static inference, unrestricted multi-shot handlers, zero-copy stackful fibers, and static prevention of both $\ge 2$-shot duplication and 0-shot linear drop-skipping. Adopting control-flow linearity ($Q^\circ_{\text{eff}}$) provides static soundness for strict linearity, but imposes the design trade-off of rejecting unfinalized 0-shot aborts (exceptions/cancellation) whenever a linear resource is live across the suspension point.

## Evidence

All primary literature, specifications, and documentation were verified on `2026-11-22`.

### Verified Primary Literature and Specifications

1. Wenhao Tang, Daniel Hillerström, Sam Lindley, and J. Garrett Morris. *Soundly Handling Linearity*. Proceedings of the ACM on Programming Languages (PACMPL), Vol. 8, Issue POPL, Article 54, 2024. DOI: `10.1145/3632896`; preprint `arXiv:2307.09383v2` (revised 2024-01-02).
2. Jesse A. Tov and Riccardo Pucella. *Practical Affine Types*. Proceedings of the 38th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2011), pp. 447–458. DOI: `10.1145/1926385.1926436`.
3. Tomas Petricek, Dominic Orchard, and Alan Mycroft. *Coeffects: A Calculus of Context-Dependent Computation*. Proceedings of the 19th ACM SIGPLAN International Conference on Functional Programming (ICFP 2014), pp. 123–135. DOI: `10.1145/2628136.2628160`.
4. Robert Atkey. *The Syntax and Semantics of Quantitative Type Theory*. Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2018), pp. 56–65. DOI: `10.1145/3209108.3209189`.
5. Dominic Orchard, Vilem-Benjamin Liepelt, and Harley Eades III. *Quantitative Program Reasoning with Graded Modal Types*. PACMPL, Vol. 3, Issue ICFP, 2019. DOI: `10.1145/3341714`.
6. Daan Leijen. *Type Directed Compilation of Row-Typed Algebraic Effects*. POPL 2017. DOI: `10.1145/3009837.3009872`.
7. Daan Leijen. *Algebraic Effect Handlers with Resources and Deep Finalization*. Microsoft Research Technical Report `MSR-TR-2018-10`, April 2018. URL: `https://www.microsoft.com/en-us/research/publication/algebraic-effect-handlers-resources-deep-finalization/`.
8. Alex Reinking, Ningning Xie, Leonardo de Moura, and Daan Leijen. *Perceus: Garbage Free Reference Counting with Reuse*. PLDI 2021. DOI: `10.1145/3453483.3454032`.
9. Jonathan Immanuel Brachthäuser, Philipp Schuster, and Klaus Ostermann. *Effects as Capabilities: Effect Handlers and Lightweight Effect Polymorphism*. PACMPL, Vol. 4, Issue OOPSLA, 2020. DOI: `10.1145/3428194`.
10. Jonathan Immanuel Brachthäuser, Philipp Schuster, Edward Lee, and Aleksander Boruch-Gruszecki. *Effects, Capabilities, and Boxes: From Scope-Based Reasoning to Type-Based Reasoning and Back*. PACMPL, Vol. 6, Issue OOPSLA1, 2022. DOI: `10.1145/3527320`.
11. KC Sivaramakrishnan, Stephen Dolan, Leo White, Tom Kelly, Sadiq Jaffer, and Anil Madhavapeddy. *Retrofitting Effect Handlers onto OCaml*. PLDI 2021, pp. 206–221. DOI: `10.1145/3453483.3454039`; `arXiv:2104.00250v1`.
12. Paulo Emílio de Vilhena and François Pottier. *A Separation Logic for Effect Handlers*. PACMPL, Vol. 5, Issue POPL, 2021. DOI: `10.1145/3434314`.
13. OCaml 5.3 Reference Manual, Chapter 12, Section 24 (*Effect handlers*: `Effect.Deep.continue`, `Effect.Deep.discontinue`, `Continuation_already_resumed`, linear continuation discipline). URL: `https://ocaml.org/manual/5.3/effects.html` (observed `2026-11-22`).
14. Anton Lorenzen, Leo White, Stephen Dolan, Richard A. Eisenberg, and Sam Lindley. *Oxidizing OCaml with Modal Memory Management*. PACMPL, Vol. 8, Issue ICFP, Article 253, August 2024. DOI: `10.1145/3674642`.
15. OxCaml Documentation: *Introduction to the Mode System* (`local`/`global`, `unique`/`aliased`, `once`/`many`, `yielding`/`unyielding`) and *Introduction to Uniqueness*. URLs: `https://oxcaml.org/documentation/modes/intro/` and `https://oxcaml.org/documentation/uniqueness/intro/` (observed `2026-11-22`).
16. Rust RFC 2349 (*Pin API*, start date 2018-02-19, `rust-lang/rfcs#2349`, stabilized in Rust 1.33.0). URL: `https://github.com/rust-lang/rfcs/blob/master/text/2349-pin.md`.
17. Rust RFC 1066 (*Alter the signature of `std::mem::forget` to remove `unsafe`*, start date 2015-04-15, `rust-lang/rfcs#1066`). URL: `https://github.com/rust-lang/rfcs/blob/master/text/1066-safe-mem-forget.md`.
18. Rust Standard Library Documentation, `std::pin` (`std 1.100.0`, `rust-lang/rust` commit `0ef1bc386059596dada8fb65b50425aab2ea637a`, 2026-11-09): sections *Drop guarantee*, *Implementing Drop for types with address-sensitive states*, and *Projections and Structural Pinning*. URL: `https://doc.rust-lang.org/std/pin/index.html` (observed `2026-11-22`).
19. Koka Language Book (§3.4.11 *Initially and Finally* — including the reference-counted `with-file` idiom — and §3.4.12 *Linear Effects*). URL: `https://koka-lang.github.io/koka/doc/book.html` (observed `2026-11-22`).

### Lean `v4.34.1` Kernel Audit (`[kernel-checked proof]` `[toy model]`)

Toolchain: `leanprover/lean4:v4.34.1` (revision `5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib-free, built and checked in a clean scratch copy of `lean/` on `2026-11-22`.

| Theorem | Module | Role | Axioms (`#print axioms`) |
| --- | --- | --- | --- |
| `Toy.LinearEffects.two_shot_duplicates_linear_capability` | `Toy/LinearEffects.lean` | (a) 2-shot double-consume counterexample (`consumes = 2`, fault) | none |
| `Toy.LinearEffects.zero_shot_abort_skips_linear_cleanup` | `Toy/LinearEffects.lean` | (b) 0-shot drop-skipping counterexample (`acquired = true`, `consumes = 0`) | none |
| `Toy.LinearEffects.zero_shot_drop_bypasses_finally` | `Toy/LinearEffects.lean` | (b) 0-shot silent `dropK` bypasses enclosing `withFinally` | none |
| `Toy.LinearEffects.typed_eval_sound` | `Toy/LinearEffects.lean` | (c) Inductive preservation for control-flow-linear + `discontinue`/`withFinally` typing | `[propext]` |
| `Toy.LinearEffects.wellTypedProgram_exact_single_use` | `Toy/LinearEffects.lean` | (c) Exact single-use soundness (`acquired = true ∧ consumes = 1 ∧ fault = false`) | `[propext]` |
| `Toy.LinearEffects.twoShotProgram_rejected` | `Toy/LinearEffects.lean` | (c) Static rejection of 2-shot counterexample | none |
| `Toy.LinearEffects.zeroShotDropProgram_rejected` | `Toy/LinearEffects.lean` | (c) Static rejection of 0-shot drop counterexample | none |
| `Toy.LinearEffects.oneShotLinearProgram_wellTyped` | `Toy/LinearEffects.lean` | (c) Witness: 1-shot linear handler well-typed | none |
| `Toy.LinearEffects.abortDiscontinueProgram_wellTyped` | `Toy/LinearEffects.lean` | (c) Witness: 0-shot `discontinue` + `withFinally` well-typed | none |
| `Toy.LinearEffects.twoShotAfterConsumeProgram_wellTyped` | `Toy/LinearEffects.lean` | (c) Witness: 2-shot unrestricted handler after consumption well-typed | none |
| `Toy.PinInvariant.unpinned_move_breaks_self_ref` | `Toy/PinInvariant.lean` | (d) Unpinned move breaks interior self-pointer validity | `[propext]` |
| `Toy.PinInvariant.skip_drop_then_reuse_violates_drop_guarantee` | `Toy/PinInvariant.lean` | (d) Storage reuse without `Drop` violates `Pin` Drop guarantee | none |
| `Toy.PinInvariant.mem_forget_without_reuse_preserves_pin_invariants` | `Toy/PinInvariant.lean` | (d) Affine `mem::forget` without storage reuse preserves `PinInvariant` | none |
| `Toy.PinInvariant.pinned_trace_preserves_invariants` | `Toy/PinInvariant.lean` | (d) Inductive preservation of `SelfRefValid`, `DropBeforeReuseGuarantee`, and `addr` | none |

Exact recorded `lake build && lake env lean Audit.lean` stdout (`2026-11-22`):

```text
Build completed successfully (5 jobs).
'Toy.LinearEffects.two_shot_duplicates_linear_capability' does not depend on any axioms
'Toy.LinearEffects.zero_shot_abort_skips_linear_cleanup' does not depend on any axioms
'Toy.LinearEffects.zero_shot_drop_bypasses_finally' does not depend on any axioms
'Toy.LinearEffects.typed_eval_sound' depends on axioms: [propext]
'Toy.LinearEffects.wellTypedProgram_exact_single_use' depends on axioms: [propext]
'Toy.LinearEffects.twoShotProgram_rejected' does not depend on any axioms
'Toy.LinearEffects.zeroShotDropProgram_rejected' does not depend on any axioms
'Toy.LinearEffects.oneShotLinearProgram_wellTyped' does not depend on any axioms
'Toy.LinearEffects.abortDiscontinueProgram_wellTyped' does not depend on any axioms
'Toy.LinearEffects.twoShotAfterConsumeProgram_wellTyped' does not depend on any axioms
'Toy.PinInvariant.unpinned_move_breaks_self_ref' depends on axioms: [propext]
'Toy.PinInvariant.skip_drop_then_reuse_violates_drop_guarantee' does not depend on any axioms
'Toy.PinInvariant.mem_forget_without_reuse_preserves_pin_invariants' does not depend on any axioms
'Toy.PinInvariant.pinned_trace_preserves_invariants' does not depend on any axioms
```

## Revalidation

1. **Lean `v4.34.1` toy model rebuild and axiom audit:** Copy `lean/` to a scratch directory (to keep `.lake/` build artifacts out of the corpus tree) and run:
   ```sh
   rm -rf /tmp/reval_linearity_effects_lean && cp -r lean /tmp/reval_linearity_effects_lean && cd /tmp/reval_linearity_effects_lean && lake build && lake env lean Audit.lean
   ```
   Confirm zero errors, zero `sorry`, and that every theorem in `Audit.lean` reports only standard Lean axioms (or no axioms).
2. **Rust `std::pin` Drop guarantee and structural pinning rules:** Re-fetch `https://doc.rust-lang.org/std/pin/index.html` and check the *Drop guarantee* and *Projections and Structural Pinning* sections for any relaxation or change (e.g., stabilization of `AsyncDrop` or `Pin` ergonomics).
3. **OxCaml modal axes for effects and linearity:** Re-fetch `https://oxcaml.org/documentation/modes/intro/` and `https://oxcaml.org/documentation/uniqueness/intro/` to verify whether `once` remains affine (at-most-once) or gains a strict linear (at-least-once) axis and whether `yielding` changes interaction rules with `Effect.Deep.discontinue`.
4. **OCaml 5 effect handler discipline:** Check the latest OCaml Reference Manual *Effect handlers* chapter (`https://ocaml.org/manual/latest/effects.html`) to verify whether continuations remain dynamically one-shot (`Continuation_already_resumed`) and whether `discontinue` remains an unchecked programmer obligation.
5. **Koka multi-shot resource safety:** Check the Koka Language Book / tour resource section (`https://koka-lang.github.io/koka/doc/book.html`) to see whether Koka introduces static control-flow linearity to reject multi-shot `ctl` across linear resources.
