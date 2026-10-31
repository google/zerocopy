<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Real-World Verification, Synthesis, and Certifying Compilation Tools Across Databases, Storage, Distributed Systems, Networking, Cloud Infrastructure, Authorization, Build Systems, and Domain-Specific Compilers

## Summary

Anneal's trusted refinement core (`trusted/lean/Trusted/Refinement.lean` and
`trusted/lean/Trusted/StepResult.lean` at
`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`, together with the
hardened boundary extensions mechanized in
`google/zerocopy@df55c524a051d59e7dd35564f282b30d29133392`) isolates four
orthogonal verification primitives:

1. **Defined-vs.-UB Partial Behavior Spine (`Language`, `Partial`, `SemObs`):**
   `Partial B` constructively lifts outcome predicates `Out → Prop` with
   `defined : Prop` and `val : defined → B` (`Partial.ub` as the top element
   $\top$ where `defined = False`), paired with an observational spine
   `obs : Out → SemObs` that separates semantic outcomes from concrete
   representation details.
2. **Bidirectional Representation Coupling and Pass Polarity
   (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`, `Abstracts`):**
   `Compiles L_src L_tgt π_c s t` (`L_tgt.sem t ≤ π_c (L_src.sem s)`) shrinks
   nondeterminism and preserves definedness forward, while
   `Abstracts L_v L_src π_v v s` (`L_src.sem s ≤ π_v (L_v.sem v)`) reflects
   UB-freedom backward from an abstract verifier model `v` to a concrete
   artifact `s`. `PartialBehaviorCodec` enforces query retraction
   (`decodeQuery_encodeQuery`), partial outcome bijection (`decode_encode_out`,
   `encode_of_decode_some`), and spine preservation (`obs_decodeOut`), rejecting
   degenerate morphisms (`π_top`, `π_chaosPure`, `π_stepZero`).
3. **Anti-Vacuity, Variable-Step Progress, and Pre-Call Boundary Framing
   (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`,
   `StepResult.externalCall`):**
   `InhabitedPre` and `ProductiveOn` rule out vacuous preconditions and
   synthetic abort/drop/reject cheats; `EventualBehaviorOf` collapses variable
   $1 \to k$ operational steps without `Classical.choice` or coinduction while
   enforcing all-prefix intermediate safety (`ReachesPrefix`); and
   `StepResult.externalCall (boundaryInv : Bool) (next : State → Obs → Prop)`
   enforces decidable call-site invariants before yielding to demonic
   environmental nondeterminism.
4. **Scoped, Non-Exploding TCB Waiver Envelopes (`VerificationResultOn`,
   `ScopedVerificationResult`, `TrustPolicy`):**
   Positive per-obligation waiver masking (`ob.id ∈ waived ∨ ob.prop`) combined
   with universal `TCBModel` quantification prevents a single unverified rule,
   external solver axiom, or boundary bug in a work-in-progress component from
   exploding into a vacuous proof (`False.elim`) of sibling obligations.

Across **86+ real-world formal verification, synthesis, and certifying
compilation tools** spanning **10 non-ISA systems domains**—(1) SQL/Datalog
query equivalence and incremental view maintenance, (2) crash-consistent storage
engines, (3) distributed consensus and transactions, (4) SDN/P4 data planes and
BGP routing, (5) cloud Infrastructure-as-Code and Kubernetes reconciliation
controllers, (6) authorization engines (`Cedar`, `Zanzibar`, `OPA`) and
differential privacy, (7) hermetic build systems and incremental computation,
(8) ML/tensor/polyhedral compilers and GPU kernel verifiers, (9) streaming
watermarks and verified lexer/regex/parser compilers, and (10) binary wire
schemas, bi-directional lenses, and durable execution workflows—every domain
independently rediscovered domain-specific fragments of these four primitives.
Where real-world tools rely on unverified SMT encodings, whole-system Coq/Dafny
monoliths, or partial-correctness checks vulnerable to degenerate "abort-all /
drop-all / deny-all / hold-watermark-forever" implementations, instantiating
Anneal's four primitives provides a uniform, kernel-checked foundation that
accepts untrusted external solvers and LLM-synthesized certificates in
`theory/` while keeping the domain TCB minimal.

## Applicability

This report applies to the subjects recorded in `REPORT.json`:

1. **Anneal trusted core and MIR-to-x86-64 compiler branches:**
   - `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (`trusted-core`:
     `trusted/lean/Trusted/Refinement.lean`,
     `trusted/lean/Trusted/StepResult.lean`,
     `theory/Anneal/Refinement.lean`, and `theory/Anneal/StepResult.lean`),
   - `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`:
     `trusted/lean/Trusted/X86Semantics.lean`,
     `theory/Anneal/Compiler/NaiveCodegen.lean`, and
     `theory/Anneal/Compiler/Peephole.lean`).
2. **Anneal trusted-boundary hardening corpus:**
   - `google/zerocopy@df55c524a051d59e7dd35564f282b30d29133392` (`reference`:
     `reports/anneal-behavior-codec-and-progress-refinement-2026/`,
     `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/`,
     and
     `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/`).
3. **Eighty-six external tools, specification languages, and industrial engines
   across ten domains**, evaluated as architectural comparison targets and
   candidate instantiations of Anneal's `trusted/` primitives. The relationship
   among these subjects is comparative and constructive: Anneal's Lean 4
   refinement primitives are interpreted as a unifying meta-framework for the
   specifications, intermediate representations, solver certificates, and TCB
   boundaries of the examined domain tools.

## Findings

### 0. Structural Cross-Walk of Anneal's Four Trusted Primitives

`Basis: source + execution + derived`

In `trusted/lean/Trusted/Refinement.lean` (lines 241–471 at
`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and `trusted/lean/Trusted/StepResult.lean`
(lines 58–198), coupled with the mechanized hardening modules in
`google/zerocopy@df55c524a051d59e7dd35564f282b30d29133392`, every verification
or compilation pipeline is governed by four orthogonal mechanisms:

- **Primitive 1 (`Language`, `Partial`, `SemObs`):**
  `Behavior Query Out := Query → Partial (Out → Prop)` separates whether an
  execution is well-defined (`defined : Prop`, where `defined = False` is
  `Partial.ub`) from what outcomes it may produce (`val : defined → Out → Prop`).
  Equipping `Language` with an observational projection `obs : Out → SemObs`
  ensures that concrete target states are compared along a canonical semantic
  spine.
- **Primitive 2 (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`,
  `Abstracts`):**
  `Compiles L_src L_tgt π_c s t` (`L_tgt.sem t ≤ π_c (L_src.sem s)`) and
  `Abstracts L_v L_src π_v v s` (`L_src.sem s ≤ π_v (L_v.sem v)`) compose
  transitively via `Preorder.le_trans` (`pass_trans`, `Compiles.comp`,
  `Abstracts.comp` in `theory/Anneal/Refinement.lean:185-223`). Constraining
  `π` to be induced by a `PartialBehaviorCodec L₁ L₂` (`encodeQuery`,
  `decodeQuery`, `encodeOut`, `decodeOut : L₂.Out → Option L₁.Out`, with
  `decodeQuery_encodeQuery`, `decode_encode_out`, `encode_of_decode_some`, and
  `obs_decodeOut`) prevents morphism degeneracy while rejecting invalid target
  encodings (`decodeOut o₂ = none`).
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`,
  `StepResult.externalCall`):**
  `InhabitedPre pre` (`∃ q, pre q`) prevents vacuous domain constraints;
  `ProductiveOn pre p` forces at least one valid outcome (`decodeOut o₂ = some o₁`)
  on every query in `pre`; `EventualBehaviorOf` (`support/BehaviorCodecExpressiveness.lean`
  at `df55c524a051`) existentially quantifies finite step budgets `steps : Nat`
  inside `Out` while preserving all-prefix safety
  (`eventual_wellFormed_iff_prefix_wellFormed`); and
  `StepResult.externalCall (boundaryInv : Bool) (next : State → Obs → Prop)`
  (`support/StructuralExternalCallAndCanaries.lean:148-236`) steps immediately
  to `.failed` if `boundaryInv = false` before branching demonically over
  `next`.
- **Primitive 4 (`VerificationResultOn`, `ScopedVerificationResult`,
  `TrustPolicy`):**
  `ScopedVerificationResult` (`support/ProofGatedCompilationAndTrustPolicy.lean`
  at `df55c524a051`) checks `AllHold (waived.map policy.isAllowed)` and
  evaluates each obligation `ob` positively as `ob.id ∈ waived ∨ ob.prop` under
  universal `TCBModel` quantification, preventing antecedent `False.elim`
  explosion.

---

### 1. Domain 1: Relational, Graph, and Datalog Query Equivalence and Incremental View Maintenance (SQL / Substrait / DBSP)

`Basis: documentation + source + derived`

#### 1.1 Domain Problem Space and Tool Families

Relational, graph, and Datalog query engines transform declarative queries
through hundreds of algebraic rewrite rules, subquery decorrelation passes
(Neumann-Kemper unnesting), predicate pushdowns, join reorderings, and
incremental view maintenance (IVM) differentiation passes. Three semantic
hazards dominate industrial query optimizers:

1. **Three-valued Kleene `NULL` logic (`TRUE`, `FALSE`, `UNKNOWN`):** Pushing a
   filter past an `OUTER JOIN` or rewriting `x NOT IN (SELECT y ...)` into an
   anti-join alters results whenever `y` contains `NULL`.
2. **Bag (multiset) vs. set multiplicity:** Pushing `DISTINCT`, commuting
   projections with joins, or applying magic-set rewrites without tracking
   tuple multiplicities ($\text{Tuple} \to \mathbb{N}$ or $\mathbb{Z}$-sets)
   duplicates or drops rows.
3. **Evaluation-order traps and non-monotone IVM drift:** Pushing an arithmetic
   expression `100 / x > 5` or `CAST(s AS INT)` below a guard `WHERE x <> 0`
   triggers runtime division-by-zero traps on dead tuples; in streaming IVM,
   incorrectly differentiating non-monotone operators (`EXCEPT`, `GROUP BY`
   having empty groups, recursive Datalog negation) causes incremental state to
   drift from $Q(I + \Delta I)$.

#### 1.2 Exhaustive Tool Deep-Dives (15 Core Tools + Adjacent Systems)

1. **`Cosette` (`uwdb/Cosette`, Chu et al., CIDR / SIGMOD 2017, DOI
   `10.1145/3035918.3056447`) and `HoTTSQL` (`uwdb/HoTTSQL`, POPL 2017, DOI
   `10.1145/3009837.3009848`):**
   - *(1) Goals & Users:* Automated prover and bounded counterexample finder for
     SQL query equivalence used by database researchers and compiler writers.
   - *(2) History & Lineage:* Developed at the University of Washington by
     Shumo Chu, Konstantin Weitz, Alvin Cheung, and Dan Suciu.
   - *(3) Design Philosophy & Tradeoffs:* Dual-engine architecture combining bounded
     symbolic execution in Rosette/Z3 (for fast counterexample generation over
     small relation bounds) with mechanized $K$-relation semiring proofs in Coq
     (`HoTTSQL`, using Homotopy Type Theory univalence to identify isomorphic
     tuple schemas).
   - *(4) Ecosystem Comparison:* Unlike SMT-only tools (`EQUITAS`, `SPES`, `Qex`),
     `HoTTSQL`/`Cosette` produces unbounded machine-checked proofs in Coq for
     conjunctive queries and unions, but struggles to automate correlated
     three-valued `NULL` semantics and complex aggregations without manual
     tactics.
   - *(5) Formal Theory & TCB:* Semiring $K$-relations ($R : \text{Tuple} \to K$,
     where $K = \mathbb{N}$ models bag semantics and $K = \mathbb{B}$ models set
     semantics). The proof track trusts the Coq kernel plus the unverified SQL
     parser translating SQL strings into Coq ASTs; the Rosette track trusts
     Racket, Rosette, and Z3 up to a finite tuple bound.

2. **`UDP` (Unified Decision Procedure / U-Expressions, Chu et al., VLDB 2018,
   DOI `10.14778/3236187.3236200`):**
   - *(1) Goals & Users:* Decide equivalence of SQL queries mixing set and bag
     semantics, integrity constraints (primary/foreign keys), and materialized
     views.
   - *(2) History & Lineage:* Direct successor to `HoTTSQL` at UW, extending
     $K$-relations with explicit summation $\sum_{t} e(t)$ and squash `‖e‖`
     (set-projection) operators called **U-expressions**.
   - *(3) Design Philosophy & Tradeoffs:* Normalizes two queries into canonical
     U-expressions and checks isomorphism of bound tuple variables via SMT
     (Lean 3 / Coq / Z3).
   - *(4) Ecosystem Comparison:* Strictly generalizes `Cosette` to integrity
     constraints and mixed set/bag queries; adopted as the theoretical core of
     `WeTune`.
   - *(5) Formal Theory & TCB:* Commutative semiring with idempotent squash
     operator; mechanized core metatheory in Coq/Lean 3, with an SMT solver in
     the decision loop for variable-bijection search.

3. **`EQUITAS` (`georgia-tech-db/equitas`, Zhou et al., SIGMOD 2019, DOI
   `10.1145/3299869.3319869`) and `SPES` (`georgia-tech-db/spes`, Zhou et al.,
   ICDE 2022, DOI `10.1109/ICDE53745.2022.00201`):**
   - *(1) Goals & Users:* Symbolic push-button SQL equivalence verifiers built
     at Georgia Tech (Qi Zhou, Joy Arulraj, Shamkant Navathe, William Harris)
     for auditing industrial query optimizers (Apache Calcite, PostgreSQL,
     MySQL).
   - *(2) History & Lineage:* `EQUITAS` (2019) modeled SQL under set semantics
     with 3-valued `NULL`s via first-order SMT constraints; `SPES` (2022)
     extended symbolic representation to **bag semantics** by encoding
     algebraic queries into canonical Symbolic Query Pair (`SQP`) normal forms
     and checking the existence of a bijective identity mapping between output
     tuple multisets in Z3.
   - *(3) Design Philosophy & Tradeoffs:* Trades foundational proof-assistant
     certificates for 100% push-button Z3 automation over 3-valued `NULL`s,
     outer joins, and aggregations.
   - *(4) Ecosystem Comparison:* Faster and broader on `NULL`/outer-join corner
     cases than `Cosette`, but unverified: a bug in `SPES`'s Java normalization
     rules or Z3 encoding silently yields false positives.
   - *(5) Formal Theory & TCB:* Entire Java symbolic normalizer, Calcite SQL
     parser, and Z3 SMT solver sit inside the TCB.

4. **`Qex` (Symbolic SQL Query Explorer, Veanes et al., LPAR 2010, DOI
   `10.1007/978-3-642-17511-4_24`):**
   - *(1) Goals & Users:* Microsoft Research tool for symbolic execution and
     test-input generation of parameterized `.NET`/T-SQL queries.
   - *(2) History & Lineage:* Built by Margus Veanes, Nikolaj Bjørner, and
     Nikolai Tillmann using the Z3 theory of lists, bags, and bitvectors.
   - *(3) Design Philosophy & Tradeoffs:* Bounded symbolic table instantiation
     for finding concrete database instances $D$ where $Q_1(D) \ne Q_2(D)$ or
     where $Q(D)$ satisfies coverage targets.
   - *(4) Ecosystem Comparison:* Predecessor to `Cosette`'s Rosette backend;
     bounded falsifier rather than an unbounded equivalence prover.
   - *(5) Formal Theory & TCB:* Z3 SMT solver and `.NET` T-SQL translator.

5. **`WeTune` (`we-tune/WeTune`, Wang et al., SIGMOD 2022, DOI
   `10.1145/3514221.3526125`) and `SlabCity` (Dong et al., SIGMOD 2023, DOI
   `10.1145/3589297`):**
   - *(1) Goals & Users:* Automated rule synthesis (`WeTune`) and rule-free
     whole-query dataflow synthesis (`SlabCity`) for discovering missing
     optimizations in PostgreSQL, SQL Server, MySQL, and Calcite.
   - *(2) History & Lineage:* Developed at SJTU / Alibaba / UMich (`WeTune`)
     and CUHK (`SlabCity`). `WeTune` enumerates algebraic plan templates up to a
     small size bound and invokes a `UDP`-based U-expression SMT prover to
     discover 200+ verified rewrite rules; `SlabCity` bypasses local rewrite
     rules entirely by synthesizing equivalent whole-query dataflows via
     bounded counterexample-guided inductive synthesis (CEGIS) and verifying
     candidates with an SMT solver.
   - *(3) Design Philosophy & Tradeoffs:* Shifts human effort from authoring
     optimizer rules to specifying semantics; however, both rely on uncertified
     SMT encodings for rule admission.
   - *(4) Ecosystem Comparison:* Directly addresses the "rule coverage gap" in
     hand-written optimizers (`CockroachDB optgen`, `Apache Calcite`).
   - *(5) Formal Theory & TCB:* U-expression / FOL SMT encoding + Z3 solver.

6. **`DataCert` (`datacert/datacert`, Benzaken, Contejean, Stefanesco, ESOP
   2014 / CPP 2017) and `QCert` (`querycert/qcert`, Auerbach et al., SIGMOD
   2017, DOI `10.1145/3035918.3056101`):**
   - *(1) Goals & Users:* Foundational Coq-verified relational database engines
     (`DataCert`) and nested-relational / JSON / OQL / SQL query compilers
     (`QCert`, IBM Research & INRIA).
   - *(2) History & Lineage:* `DataCert` mechanized relational algebra, bag
     semantics, `NULL`s, and SQL-to-algebra compilation in Coq; `QCert` built a
     20-tier verified compiler pipeline (NRA$^e$, NNRC, Cloudant MapReduce,
     Spark RDDs) in Coq extracted to OCaml.
   - *(3) Design Philosophy & Tradeoffs:* Full CompCert-style verified
     compilation (`∀ D, eval_target (compile Q) D = eval_source Q D`) inside
     Coq. High assurance, but writing new optimization passes requires manual
     Coq proofs over the compiler implementation rather than external e-graph
     certificate checking.
   - *(4) Ecosystem Comparison:* Gold standard for foundational TCB minimization
     in query compilation prior to Lean 4 certificate checking.
   - *(5) Formal Theory & TCB:* Nested Relational Calculus (NRC) and
     Nested Relational Algebra with Environments (NRA$^e$); TCB is the Coq
     kernel and OCaml extraction.

7. **`DBSP` and `Feldera` (`feldera/feldera`, Budiu et al., PVLDB 16(6) 2023,
   DOI `10.14778/3587136.3587140`) and `Materialize` (`MaterializeInc/materialize`):**
   - *(1) Goals & Users:* Real-time Incremental View Maintenance (IVM) engines
     that compile arbitrary SQL (including recursive CTEs, outer joins, nested
     aggregations, and window functions) into streaming incremental dataflow
     circuits.
   - *(2) History & Lineage:* `Materialize` (founded by Frank McSherry and Arjun
     Narayan) pioneered commercial SQL IVM over `Differential Dataflow`; `DBSP`
     (created by Mihai Budiu, Frank McSherry, Leonid Ryzhyk, and Val Tannen at
     VMware Research / Feldera) distilled IVM into a clean algebraic calculus
     over streams of $\mathbb{Z}$-sets (abelian groups of tuples with integer
     weights $w \in \mathbb{Z}$, where $w > 0$ represents insertions and $w < 0$
     represents deletions) with delay operator $z^{-1}$, differentiation
     $\mathcal{D}(s)[t] = s[t] - s[t-1]$, integration
     $\mathcal{I}(s)[t] = \sum_{i \le t} s[i]$, and incrementalization
     $Q^\Delta = \mathcal{D} \circ Q \circ \mathcal{I}$.
   - *(3) Design Philosophy & Tradeoffs:* Every relational operator is reduced to
     primitive bilinear, linear, and stateful stream operators over commutative
     groups. Feldera uses `Apache Calcite` to parse/optimize SQL and compiles it
     to a Rust `dbsp` circuit.
   - *(4) Ecosystem Comparison:* Unlike ad-hoc IVM triggers, `DBSP` has a
     complete compositional mathematical theory (mechanized in Lean 4 /
     Isabelle prototypes by the DBSP authors), though Feldera's production
     Calcite-to-Rust compiler is not proof-carrying per query.
   - *(5) Formal Theory & TCB:* Commutative $\mathbb{Z}$-modules, stream derivative/integral
     bijection ($\mathcal{D}(\mathcal{I}(s)) = s$), and bilinearity of joins
     ($(a \bowtie b)^\Delta = a^\Delta \bowtie b^\Delta + z^{-1}(a) \bowtie b^\Delta + a^\Delta \bowtie z^{-1}(b)$).

8. **Industrial & Educational Optimizer Infrastructures: `CockroachDB optgen`
   (`cockroachdb/cockroach`, Taft et al., SIGMOD 2020), `Apache Calcite`
   (`apache/calcite`, Begoli et al., SIGMOD 2018), `RisingLight`
   (`risinglightdb/risinglight`, e-graph `egg` optimizer), `Soufflé`
   (`souffle-lang/souffle`, Jordan et al., CAV 2016), plus `Spark Catalyst` and
   `DuckDB`:**
   - *(1) Goals & Users:* Production query planning, cost-based Volcano/Cascades
     search, equality saturation (`RisingLight` with `egg`), and Datalog-to-C++
     semi-naive compilation (`Soufflé`).
   - *(2) Design Philosophy & Tradeoffs:* `optgen` compiles declarative
     pattern-match/replace DSL files into Go optimizer code; `Calcite` provides
     Java `RelNode` Volcano/Hep planners; `RisingLight` uses Rust `egg` equality
     saturation; `Soufflé` compiles Datalog via Magic Sets and semi-naive
     evaluation ($\Delta R_{i+1} = F(R_i, \Delta R_i) \setminus R_i$) into
     parallel C++ B-tree/Brie loops. None of these production optimizers verify
     rule soundness mechanically, leading to recurring Kleene-3VL, `OUTER JOIN`,
     and guard-pushdown bugs.

#### 1.3 Mapping Domain 1 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_Rel.Prog`: SQL AST, Substrait plan, or stratified Datalog program;
    `L_Phys.Prog`: vectorized physical plan or DBSP $\mathbb{Z}$-set circuit.
  - `Query`: Database catalog instance $D$ (or stream of $\mathbb{Z}$-set deltas
    $[\Delta D_0, \dots, \Delta D_T]$) plus session parameters.
  - `SemObs` (`obs : Out → SemObs`): Canonical multiset (`Tuple → Int`) or
    ordered sequence of output rows paired with completion status
    (`.committed rows` vs. `.aborted err`).
  - `Partial.ub` (`defined = False`): Out-of-bounds physical tuple-slot access,
    unstratified Datalog negation oscillation, or **evaluation-order traps**
    (division by zero `1 / 0` or invalid `CAST` introduced by pushing a filter
    below its guard). Because `Compiles` requires
    `(L_Rel.sem Q D).defined → (L_Phys.sem P D).defined`, any rewrite rule (in
    `optgen`, `Calcite`, or `WeTune`) that pushes an unguarded `1 / x` below
    `WHERE x <> 0` flips `defined` from `True` to `False` on databases
    containing `x = 0` and is immediately rejected by Lean!
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `PartialBehaviorCodec L_Rel L_Phys`: `encodeQuery` / `decodeQuery` relates
    logical relations to physical Arrow columnar batches or B-tree pages;
    `decodeOut` reconstructs the logical multiset and returns `none` if Arrow
    validity bitmaps or sort orders are violated. For `DBSP`/`Feldera`,
    `encodeQuery` differentiates a sequence of database snapshots into
    $\mathbb{Z}$-set deltas $\mathcal{D}(D)$, and `decodeOut` integrates the
    output delta stream $\mathcal{I}(\Delta O)$, turning the DBSP fundamental
    theorem $\mathcal{I} \circ Q^\Delta \circ \mathcal{D} = Q$ directly into
    `Compiles L_Rel L_DBSP dbspCodec Q Q_delta`!
  - `Abstracts`: Certifies partition pruning and zone-map / MinMax / Bloom
    filtering (`Abstracts L_ZoneMap L_Phys codec ZoneSummary ScanPlan`), proving
    that pruned Parquet row groups contain zero matching tuples.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `InhabitedPre SchemaInv` proves that table `CHECK` and foreign-key
    constraints are mutually satisfiable; `ProductiveOn SchemaInv P_phys` blocks
    the degenerate optimizer cheat of compiling complex joins to
    `return .aborted .outOfMemory`.
  - `EventualBehaviorOf` bridges 1-step relational algebra evaluation with
    $O(N \log N)$ physical sort-merge or semi-naive Datalog fixpoint iterations.
  - `StepResult.externalCall` models Wasm/Python scalar UDFs and Foreign Data
    Wrappers, checking buffer alignment and transaction snapshot locks in
    `boundaryInv`.
- **`VerificationResult` and `TrustPolicy`:**
  - An external `egglog`/`WeTune`/`Calcite` optimizer emits an $N$-step rewrite
    trace. Each step $i$ becomes an obligation `ob_i : Compiles ... plan_i plan_{i+1}`
    in `ScopedVerificationResult`. If 148 standard relational rules are proved
    in Lean over Kleene-3VL multisets and 2 vendor GIS rules (`ST_Intersects`)
    are unproved, `waived := [.rule "ST_Intersects"]` audits the exact waiver
    without tainting the remaining 148 steps.

---

### 2. Domain 2: Crash-Consistent Storage Engines, LSM/B+-Trees, and Write-Ahead Logging

`Basis: documentation + source + derived`

#### 2.1 Domain Problem Space and Tool Families

Storage engines (`RocksDB`, `SplinterDB`, `SQLite` WAL, `WiredTiger`, `Fxfs`)
maintain durable state across asynchronous block devices (`io_uring`, NVMe)
where power loss can occur at any instruction boundary. Unflushed volatile page
caches evaporate, in-flight NVMe writes without `FUA`/`Flush` barriers reorder
or tear, and background LSM compactions or B+-tree node splits must never
resurrect deleted keys (tombstone garbage-collection bugs) or violate the
Write-Ahead Logging (WAL) invariant (`flushedLSN >= pageLSN`).

#### 2.2 Exhaustive Tool Deep-Dives (8 Core Tools + Adjacent Systems)

1. **`FSCQ` (`mit-pdos/fscq`, Chen et al., SOSP 2015, DOI
   `10.1145/2815400.2815402`) and `DFSCQ` (Chen et al., SOSP 2017, DOI
   `10.1145/3132747.3132776`):**
   - *(1) Goals & Users:* First file systems with machine-checked Coq proofs of
     crash safety under arbitrary power failures and crashes during recovery.
   - *(2) History & Lineage:* Built at MIT PDOS by Haogang Chen, Daniel Ziegler,
     Tej Chajed, Adam Chlipala, Frans Kaashoek, and Nickolai Zeldovich.
     Introduced **Crash Hoare Logic (CHL)**, which augments Hoare triples with a
     dedicated `crash_cond` predicate and models asynchronous disk writeback via
     lists of historical block values (`disk : Addr → val × list val`). `DFSCQ`
     added tree-structured `fdatasync` metadata-prefix specifications.
   - *(3) Design Philosophy & Tradeoffs:* Complete interactive verification in
     Coq extracted to Haskell (`FUSE`). High proof burden (~10$\times$ code-to-proof
     ratio) and sequential single-threaded execution model.
   - *(4) Ecosystem Comparison:* Laid the foundation for `Perennial` (concurrent
     crash safety) and `Yggdrasil` (SMT-automated crash refinement).
   - *(5) Formal Theory & TCB:* Crash Hoare Logic in Coq; TCB is the Coq kernel,
     Haskell GHC runtime, FUSE bindings, and disk-model axioms.

2. **`Perennial` (`mit-pdos/perennial`, Chajed et al., SOSP 2019, DOI
   `10.1145/3341301.3359632`), `GoJournal` (OSDI 2021), and `DaisyNFS`
   (`mit-pdos/daisy-nfsd`, Chajed et al., OSDI 2022):**
   - *(1) Goals & Users:* Verify high-performance **concurrent**, crash-safe
     storage systems written in Go (`Goose` subset) and Dafny.
   - *(2) History & Lineage:* Developed at MIT PDOS by Tej Chajed, Joseph
     Tassarotti, Frans Kaashoek, and Nickolai Zeldovich on top of the **Iris**
     higher-order concurrent separation logic in Coq. `DaisyNFS` (OSDI 2022)
     achieved a major architectural breakthrough: it verified the concurrent
     write-ahead journaling transaction manager (`GoTxn`/`GoJournal`) once in
     Perennial/Coq, proved that `GoTxn` exposes an atomic sequential interface to
     callers, and verified the upper NFSv3 file-system operations using
     push-button SMT automation in **Dafny**!
   - *(3) Design Philosophy & Tradeoffs:* Combines foundational concurrent crash
     separation logic (for the subtle lock/WAL kernel) with automated SMT
     verification (for high-level file-system operations).
   - *(4) Ecosystem Comparison:* Directly inspires Anneal's separation between
     foundational `trusted/` operational primitives and automated/external proof
     discharge in `theory/`.
   - *(5) Formal Theory & TCB:* Iris step-indexed crash separation logic (`wpc`
     weakest preconditions with crash modalities) + `Goose` Go-to-Coq translator
     + Dafny/Boogie/Z3 for `DaisyNFS`'s upper layer.

3. **`Yggdrasil` (`uwplse/yggdrasil`, Sigurbjarnarson et al., OSDI 2016,
   `https://www.usenix.org/conference/osdi16/technical-sessions/presentation/sigurbjarnarson`):**
   - *(1) Goals & Users:* "Push-button" Z3-based verification of crash-consistent
     file systems (`Yxv6`, `Yaffs`, `LFSCK`) in Python/C without manual Coq
     proofs.
   - *(2) History & Lineage:* Created at UW by Helgi Sigurbjarnarson, James
     Bornholt, Emina Torlak, and Xi Wang.
   - *(3) Design Philosophy & Tradeoffs:* Introduces **Crash Refinement**: an
     implementation $I$ crash-refines a specification $S$ if for every operation
     and every subset of unflushed disk writes, the set of possible post-crash
     states of $I$ is a subset of $S$'s post-crash states. Restricts Loops to
     bounded unrolling so Rosette/Z3 can decide refinement automatically.
   - *(4) Ecosystem Comparison:* Orders of magnitude lower proof effort than
     `FSCQ`, at the cost of restricting implementation structures to finitary
     symbolic paths and trusting Python/Rosette/Z3.
   - *(5) Formal Theory & TCB:* Set-inclusion crash refinement ($I \sqsubseteq_{\text{crash}} S$);
     TCB includes Python symbolic interpreter, LLVM backend, and Z3.

4. **`VeriBetrKV` (`secure-foundations/veribetrkv-osdi2020`, Hance et al., OSDI
   2020, `https://www.usenix.org/conference/osdi20/presentation/hance`):**
   - *(1) Goals & Users:* High-performance, crash-safe $B^\epsilon$-tree
     key-value store verified in Dafny (and later ported to Linear Dafny /
     Verus) that outperforms unverified `RocksDB` on write-heavy workloads.
   - *(2) History & Lineage:* Built by Travis Hance, Andrea Lattuada, Chris
     Hawblitzel, Jon Howell, Rob Johnson, and Bryan Parno (CMU, VMware Research,
     MSR).
   - *(3) Design Philosophy & Tradeoffs:* Organizes verification as a layered
     refinement stack of state machines (`MapSpec` $\to$ `Betree` $\to$
     `PagedBetree` $\to$ `PivotBetree` $\to$ concrete cache/disk implementation
     with linear memory management).
   - *(4) Ecosystem Comparison:* Demonstrates that multi-layer state-machine
     refinement scales to complex write-optimized $B^\epsilon$-tree compaction
     and journal replay.
   - *(5) Formal Theory & TCB:* TLA-style state-machine refinement checked via
     Dafny/Boogie/Z3 and compiled to C++.

5. **`Cogent` and `BilbyFS` (`NICTA/cogent`, Amani et al., ASPLOS 2016, DOI
   `10.1145/2872362.2872404`):**
   - *(1) Goals & Users:* Co-generate efficient C code and Isabelle/HOL
     equational specifications for Linux file systems (`BilbyFS` raw flash file
     system, `ext2`).
   - *(2) History & Lineage:* Developed at Data61 / UNSW Sydney (Sidney Amani,
     Alex Hixon, Zilin Chen, Christine Rizkallah, Toby Murray, Gerwin Klein).
   - *(3) Design Philosophy & Tradeoffs:* Restricted uniqueness/linear type
     system without recursion or garbage collection; the compiler emits an
     Isabelle/HOL refinement certificate proving the generated C refines the
     pure functional Cogent semantics.
   - *(4) Ecosystem Comparison:* Like Anneal, `Cogent` uses **certifying
     compilation** (generating a per-program theorem in Isabelle/HOL) rather
     than verifying the compiler once and for all.
   - *(5) Formal Theory & TCB:* Linear type system + AutoCorres C-to-Isabelle
     parser + Isabelle/HOL kernel.

6. **`Flashix` (Schellhorn, Pfähler, Bodenmüller, Reif et al., IEEE TSE 2020 /
   ABZ, Univ. Augsburg):**
   - *(1) Goals & Users:* Mechanically verified POSIX-compliant flash file
     system (wear leveling, erase-block garbage collection, UBIFS-style index
     wandering trees, and crash recovery) in the **KIV** interactive theorem
     prover.
   - *(3) Design Philosophy & Tradeoffs:* Tower of 11 Abstract State Machine
     (ASM) refinement levels from POSIX VFS down to raw NAND flash pages.
   - *(5) Formal Theory & TCB:* ASM crash refinement in KIV; Scala/C code
     generator in TCB.

7. **`Atmosphere` (`mars-research/atmosphere`, Chen et al., SOSP 2023, DOI
   `10.1145/3600006.3613148`) and Industrial `SplinterDB` (`vmware/splinterdb`,
   Conway et al., USENIX ATC 2020) / `RocksDB` (`facebook/rocksdb`):**
   - *(1) Goals & Users:* `Atmosphere` is a Rust microkernel and storage/memory
     isolation substrate verified in **Verus** using linear ghost permissions;
     `SplinterDB` (VMware $B^\epsilon$-tree) and `RocksDB` (Meta LSM-tree) are
     the dominant unverified C/C++ NVMe storage engines whose compaction,
     snapshot-watermark tombstone retention, and WAL recovery invariants are key
     targets for formal verification.

#### 2.3 Mapping Domain 2 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_KV`: Atomic crash-consistent KV specification maintaining
    `(volatileMap, durableMap)` (`sync()` copies `volatileMap` to `durableMap`;
    `crash()` resets `volatileMap := durableMap`).
  - `L_Storage`: Concrete LSM-tree / $B^\epsilon$-tree (`RocksDB`/`SplinterDB`/
    `VeriBetrKV`) with memtables, SSTables, WAL, `MANIFEST`, and `recover()`.
  - `Partial.ub` (`defined = False`): Silent data corruption on `get(k)`
    (returning unverified bit-rotted bytes without raising `ChecksumError`),
    losing a key whose `sync()` returned `Ok`, or **tombstone resurrection**
    (compaction dropping `(k, seq, DEL)` while an older SSTable level $L_i$
    still holds `(k, seq', VAL)`).
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `PartialBehaviorCodec L_KV L_Storage`: `decodeOut` runs the recovery/read
    abstraction function and validates all SSTable CRC32c/xxHash checksums,
    B+-tree key ordering, and `MANIFEST` version chains, returning `none` if any
    on-disk representation invariant is violated. `Compiles L_KV L_Storage`
    directly expresses `Yggdrasil` / `VeriBetrKV` crash refinement!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Zero-change Crash Modality via `StepResult.externalCall`:** Every block
    device submission (`io_uring_enter`, NVMe `Write`/`Flush`) is a
    `StepResult.externalCall boundaryInv branches` where:
    - `boundaryInv` enforces the **Write-Ahead Logging rule**
      (`flushedLSN >= dirtyPage.pageLSN` before writing any dirty B+-tree page);
      violating WAL steps immediately to `.failed` (`Partial.ub`)!
    - `branches` demonically selects any crash subset of unflushed in-flight
      sector writes, capturing `FSCQ`/`Perennial`'s asynchronous disk crash
      semantics with **zero modifications** to `Trusted/StepResult.lean`!
  - `EventualBehaviorOf` absorbs variable $1 \to k$ background LSM compaction
    and B+-tree split steps, while `ProductiveOn` prevents `recover()` from
    trivially returning `Err(CorruptDisk)` on every crash image.
- **`VerificationResult` and `TrustPolicy`:**
  - Isolates cryptographic/checksum assumptions (`.waive "crc32c_collision_free"`,
    `.waive "zstd_block_codec"`) in `TrustPolicy` while machine-checking WAL
    ordering, snapshot watermark tombstone retention, and crash recovery
    idempotence.

---

### 3. Domain 3: Distributed Consensus, Transactions, and Replicated State Machines

`Basis: documentation + source + derived`

#### 3.1 Domain Problem Space and Tool Families

Distributed state machines and transactional databases (`Raft`, `Multi-Paxos`,
`Spanner` TrueTime + 2PL, `FoundationDB`, `CockroachDB`, `Calvin`, `Riak` CRDTs)
execute concurrent client operations over asynchronous networks subject to
packet loss, reordering, duplication, network partitions, node crash-recovery,
and bounded clock uncertainty $[t - \epsilon, t + \epsilon]$. Correctness
requires linearizability, strict serializability (external consistency), causal
consistency, or strong eventual consistency (SEC) without degenerating into a
system that aborts every transaction or stalls forever after Global
Stabilization Time (GST).

#### 3.2 Exhaustive Tool Deep-Dives (10 Core Tools)

1. **`Verdi` (`uwplse/verdi`, Wilcox et al., PLDI 2015, DOI
   `10.1145/2737924.2737958`) and `Verdi Raft` (`uwplse/verdi-raft`, Woos et al.,
   CPP 2016, DOI `10.1145/2854065.2854081`):**
   - *(1) Goals & Users:* Coq framework for implementing and verifying
     distributed systems (`Verdi Raft`: 50,000 lines of Coq proving
     `StateMachineSafety` and linearizability of Raft, extracted to OCaml).
   - *(2) History & Lineage:* Built at UW PLSE by James R. Wilcox, Doug Woos,
     Pavel Panchekha, Zachary Tatlock, Xi Wang, Michael D. Ernst, and Thomas
     Anderson.
   - *(3) Design Philosophy & Tradeoffs:* Introduces **Verified System
     Transformers (VSTs)**: an application is verified under an idealized single
     fault model, and compositional Coq transformers compile it to handle
     packet duplication, reordering, or crash recovery. Proves safety
     (linearizability via ghost history variables) but not liveness.
   - *(4) Ecosystem Comparison:* Contrast with `IronFleet` (which proves both
     safety and liveness in Dafny/Z3) and `Ivy` (which restricts invariants to
     decidable EPR).
   - *(5) Formal Theory & TCB:* Small-step network semantics in Coq + 90
     coupled inductive invariants for Raft; TCB is the Coq kernel, OCaml
     extraction, and the `vard` network shim.

2. **`IronFleet` (`microsoft/Ironclad`, Hawblitzel et al., SOSP 2015, DOI
   `10.1145/2815400.2815428`):**
   - *(1) Goals & Users:* Proves **both safety and liveness** of practical
     distributed protocol implementations (`IronRSL` Multi-Paxos replicated
     state machine and `IronKV` sharded key-value store) in Dafny.
   - *(2) History & Lineage:* Microsoft Research (Chris Hawblitzel, Jon Howell,
     Manos Kapritsos, Jacob R. Lorch, Bryan Parno, Michael L. Roberts, Srinath
     Setty, Brian Zill).
   - *(3) Design Philosophy & Tradeoffs:* Combines TLA-style state-machine
     refinement (`AbstractService` $\sqsubseteq$ `ProtocolLayer` $\sqsubseteq$
     `ConcreteImplementation`, using reduction/mover arguments to commute local
     steps between network I/O boundaries) with embedded Temporal Logic of
     Actions in Dafny for eventual leader election and progress after GST.
   - *(4) Ecosystem Comparison:* First distributed verification framework to
     machine-check liveness of a runnable Paxos implementation, directly
     motivating `Anvil`'s temporal logic in Verus.
   - *(5) Formal Theory & TCB:* Lipton reduction + TLA refinement in Dafny; TCB
     is Dafny, Boogie, Z3, the `.NET`/C# compiler, and UDP socket bindings.

3. **`Ivy` (`kenmcmil/ivy` / `microsoft/ivy`, Padon et al., PLDI 2016, DOI
   `10.1145/2908080.2908118`; Taube et al., PLDI 2018):**
   - *(1) Goals & Users:* Interactive inductive invariant discovery and
     decidable verification for distributed protocols (`Paxos`, `Raft`, ` two-phase
     commit`, `QUIC` network stack specification).
   - *(2) History & Lineage:* Created by Kenneth L. McMillan and Oded Padon
     (MSR / Tel Aviv / Stanford / VMware).
   - *(3) Design Philosophy & Tradeoffs:* Restricts protocol transition
     relations and inductive invariants to the **Effectively Propositional (EPR)**
     / Bernays-Schönfinkel-Ramsey fragment ($\exists^* \forall^*$ relational
     first-order logic without function cycles), where Z3 is a **complete
     decision procedure** (avoiding SMT quantifier-instantiation divergence /
     "matching loops" and yielding finite counterexample models whenever an
     inductive invariant is too weak).
   - *(4) Ecosystem Comparison:* Solves the #1 usability bottleneck of Dafny/Z3
     in `IronFleet` (flaky quantifier triggers), and supports compositional
     assume-guarantee decomposition (`Modularity for Decidability`, PLDI 2018).
   - *(5) Formal Theory & TCB:* EPR decidable logic + liveness-to-safety
     reductions (`Padon et al., POPL 2018`); TCB is the Ivy Python/C++
     compiler and Z3.

4. **`Aneris` (`logsem/aneris`, Krogh-Jespersen et al., ESOP 2020, DOI
   `10.1007/978-3-030-44914-8_14`) and `Chapar` (`mit-pdos/chapar`, Lesani,
   Bell, Chlipala, POPL 2016, DOI `10.1145/2837614.2837622`):**
   - *(1) Goals & Users:* Coq frameworks for modular distributed separation
     logic (`Aneris`, built on Iris at Aarhus/MPI-SWS) and causally consistent
     replicated key-value stores (`Chapar`, MIT).
   - *(3) Design Philosophy & Tradeoffs:* `Aneris` introduces node-local heaps
     paired with socket/network protocols inside higher-order Iris ghost state,
     allowing verification of node-local concurrency + network message passing
     in one logic. `Chapar` defines an operational Characterization of Causal
     Consistency (`CausalSpec`) and proves that concrete vector-clock /
     dependency-tracking KV algorithms refine `CausalSpec`.
   - *(5) Formal Theory & TCB:* Iris step-indexed separation logic in Coq
     (`Aneris`); labeled transition system (LTS) simulation in Coq (`Chapar`).

5. **`VeriFx` (`kevin-dp/VeriFx`, De Porre et al., ECOOP 2021 / OOPSLA 2023)
   and `Isabelle CRDT` (`Archive of Formal Proofs: CRDT`, Gomes, Kleppmann,
   Mulligan, Beresford, PACMPL / OOPSLA 2017, DOI `10.1145/3133933`):**
   - *(1) Goals & Users:* Verify Conflict-Free Replicated Data Types (CRDTs:
     `RGA` collaborative text editing, `OR-Set`, `LWW-Element-Set`) and
     Operational Transformation (OT) for Strong Eventual Consistency (SEC).
   - *(3) Design Philosophy & Tradeoffs:* Gomes et al. (OOPSLA 2017) mechanized
     a network model with causal delivery in Isabelle/HOL and proved that
     concurrent op-based CRDT effectors commute (`x ∘ y = y ∘ x` under concurrent
     causal histories); `VeriFx` compiles a Scala-like functional OOP language
     to Z3 to automatically check join-semilattice laws (associativity,
     commutativity, idempotence) and op-commutativity.
   - *(5) Formal Theory & TCB:* Isabelle/HOL kernel (`Isabelle CRDT`); Scala
     compiler + Z3 (`VeriFx`).

6. **`TLA+` and `TLAPS` (`tlaplus/tlapm`, Lamport, Cousineau, Doligez et al.,
   FM 2012, DOI `10.1007/978-3-642-32759-9_14`; Newcombe et al., CACM 2015
   "How Amazon Web Services Uses Formal Methods"):**
   - *(1) Goals & Users:* Industry standard specification language (`TLA+`),
     explicit-state model checker (`TLC`), symbolic SMT model checker (`Apalache`),
     and hierarchical proof system (`TLAPS`) used at AWS (DynamoDB, S3, EBS),
     Microsoft Azure (Cosmos DB), and MongoDB.
   - *(3) Design Philosophy & Tradeoffs:* Specifies systems as $Init \land \square [Next]_vars \land Liveness$,
     proving refinement via stuttering-insensitive refinement mappings
     ($Impl \implies Spec$). `TLAPS` dispatches proof obligations to Zenon,
     Z3, CVC4, and Isabelle/Pure, but models only the abstract algorithm,
     leaving an unverified gap between `TLA+` and production Rust/Go/C++ code.

7. **Deterministic Simulation & Black-Box History Checkers: `FoundationDB
   Simulation` (`apple/foundationdb`, Zhou et al., SIGMOD 2021, DOI
   `10.1145/3448016.3457559`) and `Jepsen` / `Elle` (`jepsen-io/jepsen`,
   `jepsen-io/elle`, Kingsbury & Alvaro, PVLDB 14(3) 2020, DOI
   `10.14778/3430915.3430918`):**
   - *(1) Goals & Users:* Industrial bug-finding for distributed databases.
   - *(3) Design Philosophy & Tradeoffs:* `FoundationDB` compiles its C++ actor
     code (`Flow`) against a deterministic single-threaded simulator (`sim2`)
     that deterministically permutes network partitions, disk stalls, clock
     skew, and machine reboots over billions of simulated CPU hours. `Jepsen`
     injects real network partitions/SIGKILL faults into live clusters and feeds
     the recorded client history into `Elle`, which reconstructs Adya
     read-write (`rw`), write-write (`ww`), and write-read (`wr`) dependency
     graphs to detect cycles violating Strict Serializability, Snapshot
     Isolation, or Read Committed in polynomial time (avoiding the
     NP-completeness of general `Knossos` Wing-Gong linearizability checking).

#### 3.3 Mapping Domain 3 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_Serial`: Atomic single-node sequential transaction state machine.
  - `L_TLA`: Abstract distributed protocol state machine (`Raft`/`Paxos`/`SSI`).
  - `L_Dist`: Concrete replica event handlers (`on_rpc`, `on_timer`, `on_client`).
  - `SemObs` (`obs : Out → SemObs`): External client transaction history $H$
    (invocations, commit/abort outcomes, read values, and real-time timestamps)
    with internal heartbeats, `Prepare`/`Promise` messages, and lock tables
    erased.
  - `Partial.ub` (`defined = False`): Split-brain commit (`ElectionSafety` /
    `StateMachineSafety` violation), Adya cycle / write skew under `SERIALIZABLE`
    (`Elle` cycle), stale read violating TrueTime external consistency, or
    non-convergent CRDT replica state.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - Two-tier refinement via `Abstracts` + `Compiles` (`verify_through_passes` in
    `theory/Anneal/Refinement.lean:243-253`):
    1. `Abstracts L_TLA L_Dist nodeCodec ProtocolModel ConcreteReplica` lifts
       concrete Rust/C++ handlers to an `Ivy`/`TLA+` protocol specification.
    2. `Compiles L_Serial L_TLA histCodec SerialSpec ProtocolModel` proves via
       inductive invariants and linearization/prophecy witnesses that every
       protocol execution refines a serial history!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Abort-All Transactions" Goodhart Trap:** Any transaction
    manager that returns `.Aborted` on 100% of requests vacuously satisfies
    Strict Serializability and `Elle` cycle-freedom! Under Anneal's
    `ProductiveOn ContentionFreeAfterGSTPre ReplicaImpl`, the implementation is
    mathematically forced to produce a `.Committed` outcome whenever a quorum is
    healthy after GST and transactions do not contend.
  - `EventualBehaviorOf` natively models `TLA+` stuttering refinement: 1 serial
    step in `L_Serial` corresponds to $k$ asynchronous message-passing steps
    (2PC `Prepare` $\to$ Paxos `Accept` $\to$ TrueTime `CommitWait` $\to$
    `Apply`) in `L_Dist`.
  - `StepResult.externalCall` models network RPC transmissions and TrueTime
    `TT.now()` hardware clock reads, with `boundaryInv` enforcing Spanner's
    **Commit Wait Invariant** (`TT.now().earliest > commit_ts` before releasing
    locks or exposing writes) and Raft's **Persistent State before RPC** rule
    (`persistedTerm == currentTerm` before sending `RequestVoteResp` or
    `AppendEntriesResp`).
- **`VerificationResult` and `TrustPolicy`:**
  - Separates unconditional safety obligations (`.linearizability`,
    `.stateMachineSafety`) from conditional partial-synchrony liveness
    assumptions (`.gstBoundedDelay`) and BFT cryptographic assumptions
    (`.ed25519Unforgeable`).

---

### 4. Domain 4: Software-Defined Networking (SDN / P4 Data Planes) and BGP Control-Plane Verification

`Basis: documentation + source + derived`

#### 4.1 Domain Problem Space and Tool Families

Network infrastructure separates into three planes with distinct bug classes:
1. **Network Intent:** End-to-end reachability matrices, tenant slice isolation,
   waypoint chaining (e.g., traffic must traverse `Firewall` before `Backend`),
   and link-capacity / ECMP congestion bounds under $\le k$ link failures.
2. **Control Plane (`BGP`, `OSPF`, `ISIS`, `EVPN`):** Distributed policy
   filtering (`route-map`, `community`, `local_pref`, AS-path prepending) where
   policy interactions create **Griffin-Shepherd-Wilf Dispute Wheels**
   (permanent BGP route oscillation), BGP wedgies, or routing blackholes under
   single-link failures.
3. **Data Plane (`P4_16`, `eBPF/XDP`, `OpenFlow`, `Envoy`):** Packet header
   parsers, match-action tables (TCAM/SRAM), and tunnel encapsulation (`VXLAN`,
   `Geneve`, `SRv6`), where reading an unvalidated header (`hdr.ipv4` when
   `!hdr.ipv4.isValid()`) or miscompiling a match-action dependency corrupts or
   leaks packets in flight.

#### 4.2 Exhaustive Tool Deep-Dives (10 Core Tool Families / 14 Concrete Tools)

1. **`Batfish` (`batfish/batfish`, Fogel et al., NSDI 2015) and `Minesweeper`
   (`batfish/batfish`, Beckett et al., SIGCOMM 2017, DOI
   `10.1145/3098822.3098828`):**
   - *(1) Goals & Users:* Industry-standard multi-vendor router configuration
     analyzers (Cisco IOS, Juniper Junos, Arista EOS, AWS VPC) used by cloud and
     enterprise network engineers.
   - *(2) History & Lineage:* `Batfish` (UCLA / USC / Microsoft / Intentionet:
     Ari Fogel, Ratul Mahajan, Todd Millstein, George Varghese) parses vendor
     configs into control-plane Datalog (`LogicBlox`/`Soufflé`) to simulate one
     concrete fixed point and analyzes the resulting data plane using BDDs.
     `Minesweeper` (Princeton / MSR: Ryan Beckett, Aarti Gupta, Ratul Mahajan,
     David Walker) encodes the *entire stable routing problem* (BGP, OSPF,
     static routes, route redistribution, ACLs, and $k$-link failures) into a
     single combinatorial SMT formula in Z3 without simulating message-by-message
     convergence.
   - *(3) Design Philosophy & Tradeoffs:* `Batfish` is fast for concrete
     environment snapshots; `Minesweeper` verifies symbolic equivalence classes
     of external eBGP announcements and arbitrary $k$-link failure combinations,
     assuming BGP has a unique stable solution (or checking uniqueness via a
     2-copy SMT encoding).
   - *(5) Formal Theory & TCB:* Stable Routing Problem (SRP) SMT encoding +
     Java vendor config parsers + Z3.

2. **`Bagpipe` (`uwplse/bagpipe`, Weitz et al., OOPSLA 2016, DOI
   `10.1145/2983990.2984012`):**
   - *(1) Goals & Users:* Mechanically verifies that ISP BGP router
     configurations satisfy declarative routing policies (such as **Gao-Rexford**
     valley-free routing: never export routes learned from a peer or provider to
     another peer or provider).
   - *(2) History & Lineage:* Built at UW PLSE by Konstantin Weitz, Doug Woos,
     Emina Torlak, Michael D. Ernst, Arvind Krishnamurthy, and Zachary Tatlock.
   - *(3) Design Philosophy & Tradeoffs:* Formalizes RFC 4271 BGP semantics in
     **Coq** and proves that if a per-router export/import policy check holds on
     all single-hop announcements, then every reachable multi-hop network state
     satisfies the policy—reducing a distributed infinite-trace Coq theorem to a
     finite, decidable SMT check in Rosette/Z3!
   - *(5) Formal Theory & TCB:* Coq-verified inductive reduction from
     distributed BGP traces to local router checks + Rosette/Z3 solver.

3. **`NetKAT` (`frenetic-lang/netkat` / `google/netkat`, Anderson et al., POPL
   2014, DOI `10.1145/2535838.2535862`) and `KATch` (Moeller et al., PLDI 2024,
   DOI `10.1145/3656436`):**
   - *(1) Goals & Users:* Algebraic specification and PSPACE-complete
     decidable equivalence checking of SDN packet-forwarding and topology graphs
     (checking reachability, slicing isolation, loop freedom, and compiler
     correctness).
   - *(2) History & Lineage:* Created at Cornell and Princeton by Carolyn Jane
     Anderson, Nate Foster, Arjun Guha, Jean-Baptiste Jeannin, Dexter Kozen,
     Cole Schlesinger, and David Walker; `KATch` (PLDI 2024) introduced
     symbolic Brzozowski derivatives with Binary Decision Diagrams (SPPs:
     Symbolic Packet Programs) for orders-of-magnitude faster equivalence
     decision.
   - *(3) Design Philosophy & Tradeoffs:* Models switches as functions on packet
     histories using **Kleene Algebra with Tests (KAT)** plus packet field
     modification `f ← n` and `dup` history-recording operators. Sound and
     complete axiomatization mechanized in Coq.
   - *(5) Formal Theory & TCB:* Coalgebraic Brzozowski automata derivatives over
     Kleene Algebra with Tests; Coq metatheory.

4. **P4 Verification & Formal Semantics Suite: `p4v` (Liu et al., SIGCOMM 2018,
   DOI `10.1145/3230543.3230582`), `Vera` (Stoenescu et al., SIGCOMM 2018, DOI
   `10.1145/3230543.3230548`), `Petr4` (`cornell-netlab/petr4`, Doenges et al.,
   POPL 2021, DOI `10.1145/3434301`), `Poulet4` (`verified-network-toolchain/poulet4`,
   Coq P4 semantics), and `Gauntlet` (`p4gauntlet/gauntlet`, Ruffy et al., OSDI
   2020):**
   - *(1) Goals & Users:* Verify P4 programmable switch programs (`p4v`, `Vera`),
     mechanize the normative `P4_16` language standard (`Petr4`, `Poulet4`), and
     validate production P4 compilers (`p4c`, Barefoot Tofino) via translation
     validation (`Gauntlet`).
   - *(3) Design Philosophy & Tradeoffs:* `p4v` (Barefoot/Cornell/SRI) translates
     P4 + control-plane interface assumptions into Guarded Command Language
     (GCL) and verifies safety via Z3; `Vera` (UPB/Broadcom) uses SymNet
     symbolic execution to catch invalid header accesses, parser loops, and
     arithmetic overflows; `Petr4` & `Poulet4` mechanize big-step and small-step
     operational semantics and type soundness of `P4_16` in OCaml and Coq;
     `Gauntlet` (NYU) translates `p4c` IR passes into Z3 SMT queries and uncovered
     90+ bugs (including 25 silent miscompilations!) in `p4c` and Tofino.

5. **Real-Time Data-Plane Equivalence & Control-Plane Abstract Interpretation:
   `Header Space Analysis (HSA)` (Kazemian et al., NSDI 2012), `VeriFlow`
   (Khurshid et al., NSDI 2013), `APKeep` (`XJTU-NetVerify/apkeep`, Zhang et al.,
   NSDI 2020), and `NV` (`NetworkVerification/nv`, Giannarakis et al., PLDI 2020)
   / `ShapeShifter` (Beckett et al., PLDI 2019) / `Timepiece` (Tang et al.,
   PLDI 2023):**
   - *(3) Design Philosophy & Tradeoffs:* `HSA` treats headers as points in
     $\{0,1\}^L$; `VeriFlow` slices prefixes into trie equivalence classes;
     `APKeep` maintains a minimal partition of **Atomic Predicates** (BDDs)
     across ACLs and NATs for sub-millisecond incremental verification. On the
     control plane, `NV` models routing protocols as SRP algebraic attributes in
     OCaml, `ShapeShifter` applies **abstract interpretation** (Galois
     connections over route attributes) to verify BGP convergence/reachability,
     and `Timepiece` uses modular assume-guarantee temporal interfaces to verify
     2,000-node data-center BGP fabrics.

#### 4.3 Mapping Domain 4 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_Intent`: End-to-end reachability/waypoint/isolation matrix (`NetKAT`
    specification).
  - `L_BGP` / `L_P4`: Distributed BGP router configs or compiled `P4_16` switch
    pipeline (`Poulet4` / `Petr4` semantics).
  - `SemObs` (`obs : Out → SemObs`): Egress `(zone, payload, waypoints)` or
    `.dropped` (stripping transit MPLS/VXLAN/SRv6 tunnel headers).
  - `Partial.ub` (`defined = False`): Forwarding loops (TTL exhaustion),
    tenant isolation violations, P4 invalid header reads/writes
    (`!hdr.ipv4.isValid()`), or BGP Dispute Wheel oscillation.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `Compiles L_P4_MidEnd L_P4_BackEnd p4Codec ir_before ir_after` turns
    `Gauntlet`'s unverified Z3 translation validation into a kernel-checked Lean
    refinement proof over `Poulet4`-style semantics!
  - `Abstracts L_AtomicPred L_P4 apCodec BDDPartition SwitchPipeline` formalizes
    `APKeep`'s Atomic Predicate equivalence-class partitioning and
    `ShapeShifter`'s Galois-connection abstract interpretation directly as an
    Anneal `Abstracts` pass!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Drop-All Firewall" Goodhart Loophole:** A firewall compiler
    that emits `DROP ALL` trivially satisfies every negative tenant-isolation
    invariant. Under Anneal, `ProductiveOn AuthorizedTrafficPre CompiledTables`
    (paired with `obs_decodeOut` preserving `.forwarded`) forces legitimate
    production traffic to be delivered!
  - `EventualBehaviorOf` models BGP asynchronous message convergence: because
    `EventualBehaviorOf` requires a finite termination step count `steps : Nat`
    for every valid failure scenario $|F| \le k$, any BGP Dispute Wheel
    (route oscillation) fails `EventualBehaviorOf` automatically!
  - `StepResult.externalCall` models eBGP peer announcements and stateful L7
    middleboxes, checking RPKI Route Origin Validation and bogon filters in
    `boundaryInv`.
- **`VerificationResult` and `TrustPolicy`:**
  - Certifies LP-synthesized Traffic Engineering WCMP weights outside the TCB
    while scoping hardware TCAM parity assumptions in `TrustPolicy`.

---

### 5. Domain 5: Cloud Infrastructure-as-Code (IaC) and Kubernetes Reconciliation Loops

`Basis: documentation + source + derived`

#### 5.1 Domain Problem Space and Tool Families

Cloud orchestration operates through (a) **Declarative-to-DAG Planners**
(`Terraform`, `OpenTofu`, `Pulumi`, `CloudFormation`) that synthesize partially
ordered `Create`/`Update`/`Destroy` plans from state diffs, and (b)
**Event-Driven Kubernetes Reconciliation Controllers** (Operators, `ArgoCD`,
`Crossplane`) executing continuous `reconcile(ctx, req)` loops over `etcd`.
Controllers fail when **Time-of-Check-to-Time-of-Use (TOCTOU) stale reads** from
local informer caches, partial API failures, misordered `finalizers`, or
competing controllers cause orphan resource leaks, rolling-update availability
blackouts, or infinite reconciliation oscillation.

#### 5.2 Exhaustive Tool Deep-Dives (6 Core Tool Families / 8 Concrete Tools)

1. **`Anvil` (`anvil-verifier/anvil`, Sun et al., USENIX OSDI 2024 Best Paper,
   `https://www.usenix.org/conference/osdi24/presentation/sun`):**
   - *(1) Goals & Users:* Formal verification framework for building production
     Kubernetes controllers (ZooKeeper, RabbitMQ, FluentBit operators) in Rust
     with machine-checked **liveness and safety** proofs.
   - *(2) History & Lineage:* Developed at UIUC, VMware Research, CMU, and UW
     (Xudong Sun, Wenjie Ma, Jiawei Tyler Gu, Zicheng Ma, Tej Chajed, Jon Howell,
     Andrea Lattuada, Oded Padon, Lalith Suresh, Adriana Szekeres, Tianyin Xu)
     on top of **Verus** (`verus-lang/verus`).
   - *(3) Design Philosophy & Tradeoffs:* Formulates **Eventually Stable
     Reconciliation (ESR)**: $\square (\text{DesiredStateStable}(spec) \land
     \text{FairFailureFreeSuffix} \implies \lozenge \square \text{Matches}(state, spec))$.
     Handles arbitrary crash restarts, network retries, and stale views in the
     controller runtime (`deps_hack` / `kube-rs` shim).
   - *(4) Ecosystem Comparison:* Directly supersedes testing-only tools (`Sieve`)
     by proving absence of stale-read TOCTOU bugs and liveness stalls across all
     interleavings.
   - *(5) Formal Theory & TCB:* Embeds TLA+ temporal logic (`always`,
     `eventually`, `leads_to` with WF1/SF1 rules) inside Verus/Z3; TCB is Verus,
     Z3, the `kube-apiserver` cluster model, and `kube-rs` shim.

2. **`Sieve` (`sieve-project/sieve`, Sun et al., OSDI 2022,
   `https://www.usenix.org/conference/osdi22/presentation/sun`):**
   - *(1) Goals & Users:* Automated black-box/grey-box reliability testing tool
     for Kubernetes controllers written in Go (`operator-sdk` / `controller-runtime`).
   - *(3) Design Philosophy & Tradeoffs:* Instruments `client-go` informer
     caches and API calls to inject **time-travel (stale-read) perturbations**,
     controller crash-restarts after side-effecting API calls, and reordered
     watch events, checking whether the final cluster state differs from a
     reference unperturbed run (Differential Observability). Discovered 46
     serious bugs across 10 popular K8s operators (Cassandra, CockroachDB,
     Percona XtraDB, RabbitMQ).
   - *(5) Formal Theory & TCB:* Dynamic trace perturbation and differential
     state-equivalence testing (no formal proof).

3. **`K8s-TLA+` (Kubernetes Controller / Scheduler / Informer TLA+ Specifications,
   `kubernetes-sigs`, AWS/RedHat/ByteDance formal models):**
   - *(1) Goals & Users:* Model checking Kubernetes informer reflector/delta-FIFO
     pipelines, lease election, and custom operators using `TLC` and `Apalache`.
   - *(3) Design Philosophy & Tradeoffs:* Finds high-level protocol races in
     design documents but leaves the Go/Rust controller implementation unverified.

4. **Policy-as-Code & IaC Static Analyzers: `Terraform Sentinel` (HashiCorp),
   `Conftest` (`open-policy-agent/conftest`, Rego), and `Checkov`
   (`bridgecrewio/checkov`, Python graph-based IaC analyzer):**
   - *(1) Goals & Users:* Shift-left CI/CD policy gating for `terraform plan`
     JSON outputs, Kubernetes manifests, Helm charts, and CloudFormation
     templates.
   - *(3) Design Philosophy & Tradeoffs:* `Conftest` runs OPA `Rego` assertions
     over structured YAML/JSON configs; `Checkov` builds a resource dependency
     graph across Terraform modules to evaluate 1,000+ security compliance rules
     (e.g., S3 encryption, IAM wildcard restrictions). Both inspect **static
     target snapshots** only—they do not model the **intermediate transition
     states** of executing the `terraform apply` DAG (such as a 20-second outage
     when a Security Group or Target Group is destroyed before its replacement
     is attached).

5. **`Tiros` (Backes et al., CAV 2019, DOI `10.1007/978-3-030-25543-5_14`, AWS
   Automated Reasoning Group):**
   - *(1) Goals & Users:* Production symbolic reachability engine powering
     **Amazon Inspector Classic / AWS Network Access Analyzer** across millions
     of customer VPCs.
   - *(3) Design Philosophy & Tradeoffs:* Encodes AWS VPC routing tables,
     Security Groups (stateful), Network ACLs (stateless), Internet Gateways,
     NAT Gateways, Transit Gateways, and VPC Peering into Datalog (`Soufflé`)
     and SMT (`Z3`/`CVC4`/`MonoSAT`) to prove whether any packet can reach an
     EC2 instance from the public internet without sending probe packets.

6. **`Rehearsal` (`plasma-umass/rehearsal`, Shambaugh, Weiss, Guha, PLDI 2016,
   DOI `10.1145/2908080.2908122`):**
   - *(1) Goals & Users:* Verification tool for **Puppet** declarative server
     configuration manifests.
   - *(3) Design Philosophy & Tradeoffs:* Compiles Puppet resource graphs and
     POSIX file/package/service operations into a decidable, loop-free
     filesystem state-transformation semantics checked with Z3. Proves two key
     properties: **Determinism** (every valid topological execution order of the
     underspecified Puppet dependency DAG yields the exact same machine state)
     and **Idempotence** (running the manifest a second time is a no-op).

#### 5.3 Mapping Domain 5 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_Decl`: Declarative desired cluster/cloud specification + continuous
    availability envelope (e.g., `activeHealthyPods >= PDB_minAvailable` and
    `neverPubliclyExposed(RDS)`).
  - `L_Ctrl`: Concrete Kubernetes operator `reconcile` step function (`Anvil`)
    or Terraform/Puppet DAG execution plan (`Rehearsal`).
  - `Partial.ub` (`defined = False`):
    - **Intermediate Rollout Outage / Transient Security Exposure:** Destroying
      old pods or security rules before replacements pass readiness checks at
      any intermediate step $0 \le i \le n$.
    - **Orphan Resource Leak / Data Loss:** Deleting a `PersistentVolumeClaim`
      before draining state, or failing to register a `finalizer` before
      provisioning an external cloud resource.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `Compiles L_Decl L_Ctrl k8sCodec DesiredRolloutSpec ReconcileFn` captures
    both `Anvil`'s ESR property and `Rehearsal`'s DAG determinism (since
    demonic choice in `L_Ctrl` ranges over all topological schedules of the
    Terraform/Puppet DAG, and `Compiles` requires *every* schedule to refine the
    deterministic target state!).
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **All-Prefix Intermediate Availability + Eventual ESR in One Primitive:**
    Look at how `EventualBehaviorOf` in Anneal (`BehaviorOf` in
    `Trusted/StepResult.lean:176-187` combined with `EventualOut` in
    `support/BehaviorCodecExpressiveness.lean`) works:
    1. `defined` quantifies over **all finite prefixes** (`∀ n tr out,
       ReachesPrefix M.step p n init tr out → out.isSafe`), automatically
       enforcing **zero-downtime rolling updates** (no availability drop or
       transient security gap at any intermediate step $0 \le i \le n$)!
    2. `val` requires termination in a quiescent state matching `DesiredSpec`
       after $k$ reconcile ticks (`EventualOut.terminated`), proving `Anvil`'s
       **Eventually Stable Reconciliation (ESR)** without needing a separate
       temporal logic DSL in `trusted/lean/`!
    3. `ProductiveOn` blocks a controller that trivially avoids unsafe mutations
       by returning `RequeueAfter(∞)`.
  - `StepResult.externalCall` models `kube-apiserver` / Cloud SDK mutations,
    where `boundaryInv` enforces optimistic concurrency (`resourceVersion`
    precondition present) and `finalizer` attachment before provisioning
    external resources, while `branches` demonically models `409 Conflict`
    responses and `Sieve`-style stale informer cache reads!
- **`VerificationResult` and `TrustPolicy`:**
  - Waives external cloud control-plane propagation bounds
    (`.waive "aws_iam_eventual_consistency"`) while strictly proving controller
    idempotence, finalizer safety, and multi-controller non-oscillation.

---

### 6. Domain 6: Fine-Grained Authorization (`Cedar` / `Zanzibar` / `OPA`) and Differential Privacy Engines

`Basis: documentation + source + derived`

#### 6.1 Domain Problem Space and Tool Families

Authorization and privacy engines gate every data access:
1. **Attribute-Based & Relationship-Based Access Control (`Cedar`, `Zanzibar`/
   `SpiceDB`/`OpenFGA`, `OPA` Rego, AWS IAM):** Evaluate `(principal, action,
   resource, context)` against policy sets (`permit`/`forbid`) and relation
   graphs (`doc:readme#viewer@group:eng#member`). When listing or searching
   millions of records, engines use **Partial Evaluation** (residual policy
   compilation) to compile a policy into a SQL `WHERE` clause or vector-index
   filter; any mismatch between the residual filter and reference evaluation
   causes **unauthorized data leakage** or **silent over-filtering**.
2. **Differential Privacy (`OpenDP`, `Chorus`, `Fuzz`/`DFuzz`/`LightDP`,
   `CertiPriv`/`EasyCrypt apRHL`):** Bound the maximum change in a query's
   output when one user's data is added or removed (**global sensitivity**
   $\Delta f$), add calibrated Laplace/Gaussian noise, and enforce privacy
   budget accounting ($\sum \epsilon_i \le \epsilon_{\text{max}}$).

#### 6.2 Exhaustive Tool Deep-Dives (9 Core Tool Families / 13 Concrete Tools)

1. **`Cedar` and `cedar-spec` (`cedar-policy/cedar`, `cedar-policy/cedar-spec`,
   Cutler et al., OOPSLA 2024, DOI `10.1145/3649835`):**
   - *(1) Goals & Users:* Open-source authorization policy language powering
     **Amazon Verified Permissions** and **AWS IAM Identity Center**, designed
     from day one using **verification-guided development in Lean 4**!
   - *(2) History & Lineage:* Built by AWS Automated Reasoning Group (Craig
     Disselkoen, Aaron Eline, Shaobo He, Kyle Headley, Michael Hicks, Kesha
     Hietala, Emina Torlak, et al.).
   - *(3) Design Philosophy & Tradeoffs:* `cedar-spec` models Cedar's evaluator,
     validator (typechecker), symbolic compiler (for SMT equivalence/subsumption
     queries via `cvc5`), and partial evaluator in **Lean 4**. Proves in Lean 4:
     - **Default-Deny & `forbid`-Overrides-`permit` Safety:** A request is
       allowed iff at least one `permit` matches and zero `forbid` rules match.
     - **Policy Slicing Soundness:** Evaluating a request over a manifest-sliced
       subset of policies equals evaluating over the full policy set.
     - **Validator Type Soundness:** If the Cedar validator accepts a policy set
       under a schema, evaluation never fails with type errors (modulo explicit
       entity-dereference/extension traps).
     - **Differential Testing Bridge:** Because Cedar's production runtime is
       written in Rust (`cedar-policy`) while the proofs live in Lean 4
       (`cedar-spec`), AWS bridges the gap using millions of cargo-fuzz / DRT
       (Differential Random Testing) runs between the extracted Lean 4 reference
       evaluator and the Rust crate!
   - *(4) Ecosystem Comparison:* Closest real-world industrial cousin to Anneal
     in the Lean 4 ecosystem—and highlights the exact gap Anneal closes: Cedar
     relies on differential fuzzing between Lean 4 `cedar-spec` and Rust
     `cedar-policy`, whereas Anneal directly captures and verifies the Rust MIR
     of `cedar-policy` inside Lean 4!
   - *(5) Formal Theory & TCB:* Lean 4 kernel (`cedar-spec`) + unverified Rust
     re-implementation gap (mitigated by DRT) + `cvc5` for SMT analysis queries.

2. **`Zelkova` (Backes et al., FMCAD 2018, DOI `10.23919/FMCAD.2018.8603013`,
   AWS) and `Margrave` (Fisler, Krishnamurthi, Meyerovich, Tschantz, ICSE 2005,
   DOI `10.1145/1062455.1062502`):**
   - *(1) Goals & Users:* Policy equivalence, change-impact, and public-exposure
     analyzers for AWS IAM policies (`Zelkova`, powering **AWS IAM Access
     Analyzer** and S3 Block Public Access) and XACML access-control policies
     (`Margrave`, Brown Univ. / WPI).
   - *(3) Design Philosophy & Tradeoffs:* `Zelkova` translates AWS IAM JSON
     policies (including `Allow`, `Deny`, `NotAction`, `NotResource`, regex
     wildcards `*`/`?`, and condition keys) into SMT bitvector/string/regex
     formulas solved by `Z3`, `CVC4`, and a custom regex solver (`Z3-str3`).
     `Margrave` compiles XACML policies into Multi-Terminal Binary Decision
     Diagrams (MTBDDs) to compute exact change-impact diffs ($P_1$ vs. $P_2$)
     and query completeness.

3. **`Zanzibar` (Pang et al., USENIX ATC 2019, Google), `SpiceDB`
   (`authzed/spicedb`), and `OpenFGA` (`openfga/openfga`, CNCF):**
   - *(1) Goals & Users:* Planet-scale Relationship-Based Access Control (ReBAC)
     systems evaluating graph reachability over relation tuples
     (`object#relation@user_or_userset`) with union, intersection, and exclusion
     set rewrites plus ABAC `caveats`.
   - *(3) Design Philosophy & Tradeoffs:* `Zanzibar` achieves sub-10ms latency
     and **external consistency** (preventing the **"New Enemy Problem"**, where
     a user removed from an ACL reads newly updated content via a stale cache)
     using **Spanner TrueTime Zookies** (opaque consistency tokens bounding
     staleness) and the **Leopard Indexing System** (denormalized transitive
     group-to-group reachability bitmaps updated incrementally). `SpiceDB` and
     `OpenFGA` implement Zanzibar in Go over CockroachDB/Spanner/Postgres.

4. **`Open Policy Agent (OPA)` (`open-policy-agent/opa`, CNCF):**
   - *(1) Goals & Users:* General-purpose cloud-native policy engine evaluating
     declarative **Rego** (Datalog derivative over hierarchical JSON documents).
   - *(3) Design Philosophy & Tradeoffs:* Supports **OPA Partial Evaluation**
     (`opa compile`), which specializes a Rego policy with known `input.user`
     context into residual simplified Rego ASTs that are translated into SQL
     `WHERE` clauses or Elasticsearch filters for data-layer enforcement.

5. **Differential Privacy Verification & Runtime Engines: `OpenDP`
   (`opendp/opendp`, Gaboardi, Hay, Vadhan, Harvard), `Chorus`
   (`uvm-plaid/chorus`, Johnson, Near, Hellerstein, Song,PVLDB / EuroSys 2020),
   `Fuzz` (Reed & Pierce, ICFP 2010), `DFuzz` (Gaboardi et al., POPL 2013),
   `LightDP` (Zhang & Kifer, POPL 2017) / `Fuzzi` (POPL 2019), and `CertiPriv` /
   `EasyCrypt apRHL` (`EasyCrypt/easycrypt`, Barthe et al., POPL 2012, DOI
   `10.1145/2103656.2103670`):**
   - *(3) Design Philosophy & Tradeoffs:*
     - `OpenDP` structures DP pipelines in Rust as composable
       `Transformation`s (with stability map $d_{\text{out}} \le c \cdot d_{\text{in}}$)
       chained into `Measurement`s (with privacy map $\epsilon$) via manual
       LaTeX proof documents audited by a review board.
     - `Chorus` rewrites SQL queries (via `Apache Calcite`) to enforce clipping,
       join-sensitivity bounding, and noise injection on existing databases.
     - `Fuzz` & `DFuzz` use linear indexed type systems ($!_k \tau$) to track
       $k$-sensitivity of functions statically; `LightDP` uses relational shadow
       execution types to reduce adaptive DP verification (e.g., Sparse Vector
       Technique) to off-the-shelf safety assertions; `CertiPriv` (Coq) and
       `EasyCrypt` mechanize **Approximate Probabilistic Relational Hoare Logic
       (apRHL)** ($\vdash c_1 \sim_{\epsilon, \delta} c_2 : P \implies Q$) using
       probabilistic liftings/couplings.

#### 6.3 Mapping Domain 6 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_AuthSpec`: Reference `Cedar` (`cedar-spec`) or `Zanzibar` graph
    reachability evaluator, or reference post-filtered query
    `Filter(CheckAuth(u), Scan(T))`.
  - `L_CompiledAuth`: Rust `cedar-policy` MIR implementation, OPA partially
    evaluated SQL `WHERE` filter, or Zanzibar `Leopard` bitmap index.
  - `SemObs` (`obs : Out → SemObs`): Exact `Allow`/`Deny` boolean decision (or
    authorized row set) + mandatory security audit records.
  - `Partial.ub` (`defined = False`): Privilege escalation / unauthorized data
    leakage (`Allow` when `forbid` matches), evaluation traps, or **"New Enemy"
    causality violation** (evaluating ACLs at timestamp $t_{\text{acl}} <
    t_{\text{content}}$).
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - **Bridging `cedar-spec` (Lean 4) and `cedar-policy` (Rust) Without Fuzzing:**
    Instead of relying on differential random testing between `cedar-spec` and
    the Rust `cedar-policy` crate, Anneal's `anneal-rustc-capture` extracts the
    Rust MIR of `cedar-policy` and proves
    `Compiles L_CedarSpec L_Mir cedarCodec SpecEval MirEval` directly in the
    Lean 4 kernel!
  - **Certified Residual SQL Compilation (`OPA` / `Cedar` Partial Evaluation):**
    `Compiles L_PostFilter L_PushedSQL sqlCodec (Filter(Policy, Table)) ResidualSQL`
    proves that the pushed-down SQL `WHERE` clause returns the **exact same**
    rows as row-by-row policy evaluation.
  - **Differential Privacy Sensitivity & `OpenDP` Transformation Proofs via
    `Abstracts`:** `Abstracts L_Sensitivity L_SQL sensCodec BoundSpec SQLQuery`
    certifies relational query sensitivity $\Delta f$, and instantiating
    `Language` over 2-safety neighboring database pairs $(D_1, D_2)$ checks
    `LightDP`/`apRHL` coupling witnesses deterministically in Lean!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Deny-Everything" Security Goodhart Trap:** A policy compiler
    that compiles every residual query to `WHERE FALSE` (or returns `Deny` on
    all requests) commits zero unauthorized data leaks! Because Anneal's
    `PartialBehaviorCodec` enforces `obs_decodeOut` (`Allow ↔ Allow` and
    `Deny ↔ Deny`) and `ProductiveOn` requires a valid decision on every query,
    silent over-denial is refuted. Furthermore, `InhabitedPre (fun q =>
    eval p q = .Allow)` detects shadowed/dead `permit` rules during policy
    refactoring (`Margrave`/`Zelkova`).
  - `StepResult.externalCall` gates DP output release on `boundaryInv :=
    (remainingBudget >= queryEpsilon && sensitivityVerified)`.
- **`VerificationResult` and `TrustPolicy`:**
  - Enforces zero waivers on `forbid` rules and DP privacy-budget accounting
    while explicitly logging any hardware CSPRNG assumptions.

---

### 7. Domain 7: Hermetic Build Systems, Fine-Grained Incremental Computation, and Package Resolvers

`Basis: documentation + source + derived`

#### 7.1 Domain Problem Space and Tool Families

Build systems (`Bazel`, `Buck2`, `Nix`, `Shake`) and fine-grained incremental
computation engines (`Salsa` in `rust-analyzer`, `Adapton`) refine a clean,
from-scratch topological build (`L_CleanBuild`) using persistent memoization
caches, content-addressed Merkle digests (CAS), dynamic dependency discovery
(monadic build rules), and **Early Cutoff** (skipping downstream actions when a
recomputed dependency produces the same output hash). Bugs in dependency
tracking or sandbox mount isolation cause **stale build artifacts** (where an
incremental build diverges from a clean build) or **remote cache poisoning**.

#### 7.2 Exhaustive Tool Deep-Dives (7 Core Tool Families)

1. **`Build Systems à la Carte` (`snowleopard/build`, Mokhov, Mitchell, Peyton
   Jones, ICFP 2018, DOI `10.1145/3236774`; JFP 2020, DOI
   `10.1017/S0956796820000088`):**
   - *(1) Goals & Users:* Unifying executable taxonomy and formal correctness
     definition for build systems (`Make`, `Ninja`, `Shake`, `Bazel`, `Buck`,
     `Excel`, `Nix`) in Haskell.
   - *(2) History & Lineage:* Created by Andrey Mokhov (Newcastle / Jane Street),
     Neil Mitchell (Shake / Meta `Buck2`), and Simon Peyton Jones (MSR).
   - *(3) Design Philosophy & Tradeoffs:* Factorizes any build system into two
     orthogonal choices: a **Scheduler** (`Topological`, `Restarting`,
     `Suspending`) and a **Rebuilder** (`DirtyBit`, `VerifyingTraces`,
     `ConstructiveTraces` / Content-Addressed Early Cutoff), parameterized by the
     **Task Abstraction** (`Applicative` static dependencies vs. `Monad` dynamic
     dependencies). Defines **Build Correctness (From-Scratch Consistency)**:
     after building target $k$ from initial store $S_0$ with warm cache, the
     resulting store $S'$ agrees on $k$ and all its transitive dependencies with
     recomputing every task purely from scratch on the current input files.
   - *(4) Ecosystem Comparison:* Directly shaped the architecture of Meta's
     `Buck2` and Jane Street's `Jenga`.
   - *(5) Formal Theory & TCB:* Functional Haskell semantics (`Tasks Monad k v`);
     mechanized Coq/Isabelle adaptations exist for subsets, while the original
     paper provides pen-and-paper + property-tested proofs.

2. **`Pluto` (`pluto-build/pluto`, Erdweg, Lichter, Weiel, OOPSLA 2015, DOI
   `10.1145/2814270.2814277`):**
   - *(1) Goals & Users:* Incremental build system in Java supporting **dynamic
     dependencies**, **cyclic task dependencies** (via fixed-point iteration or
     cycle-handler plugins, e.g., $\text{LaTeX} \leftrightarrows \text{BibTeX}$),
     and fine-grained custom stamps (early cutoff).
   - *(5) Formal Theory & TCB:* Operational semantics with mechanized
     soundness/minimality proofs of dynamic dependency graph rebuilding.

3. **`Salsa` (`salsa-rs/salsa`, Matsakis et al., Rust incremental query
   framework powering `rust-analyzer`, `ruff`/`red-knot`, and `fe`):**
   - *(1) Goals & Users:* Demand-driven, fine-grained incremental computation in
     Rust with automatic dependency tracking, durability tiers, and Early Cutoff.
   - *(3) Design Philosophy & Tradeoffs:* Implements the **Red-Green Algorithm**
     (originally developed for `rustc`'s incremental query engine): each
     memoized query stores `(value, verified_at_revision, changed_at_revision,
     dependencies)`. When verifying whether query $Q$ is still valid at revision
     $R$, Salsa walks $Q$'s recorded inputs in execution order; if an input $I_1$
     is re-evaluated at $R$ and its output `PartialEq` equals its previous value
     (`changed_at < Q.verified_at`), $I_1$ is marked **Green** (Early Cutoff!),
     preventing $Q$ from re-executing and avoiding evaluating later dynamic
     branches $I_2$ that might depend on $I_1$!

4. **`Buck2` and `DICE` (`facebook/buck2`, Mitchell et al., Meta 2023):**
   - *(1) Goals & Users:* High-performance polyglot hermetic build system in
     Rust replacing `Buck1`, powered by the **DICE** (Deterministic Incremental
     Computation Engine) crate (`buck2/shed/dice`).
   - *(3) Design Philosophy & Tradeoffs:* Unifies configuration loading,
     Starlark evaluation, `Bxl` (Buck Extension Language) dynamic build graphs,
     and action execution inside a single monadic DICE dependency graph with
     content-addressed Early Cutoff and Remote Execution (`REAPI`) integration.

5. **`Adapton` (`adapton/adapton.rust`, Hammer, Phang, Hicks, Foster, PLDI 2014,
   DOI `10.1145/2594291.2594324`; Nominal Adapton OOPSLA 2015; Fungi 2018):**
   - *(1) Goals & Users:* Demand-driven Self-Adjusting Computation (SAC) with
     first-class **programmer-controlled cache names** (solving the "anonymous
     allocation hash-shift" problem when inserting an element at the head of a
     list invalidates all subsequent memoization nodes).
   - *(4) Ecosystem Comparison:* Already documented in the `reference` corpus
     (`adapton-names-identity-freshness-2014-2018`).

6. **`Bazel Skyframe` (`bazelbuild/bazel`) and `Remote Execution API (REAPI)`
   (`bazelbuild/remote-apis`):**
   - *(1) Goals & Users:* Google's open-source hermetic build system (`Skyframe`
     asynchronous restarting parallel evaluation framework over `SkyKey` $\to$
     `SkyValue`) and content-addressed remote execution protocol (`Action`,
     `Command`, `Directory` Merkle trees in CAS, `ActionCache`).

7. **`PubGrub` (`pubgrub-rs/pubgrub`, Weizenbaum 2018, Dart `pub`, Astral `uv`,
   `cargo` next-gen resolver):**
   - *(1) Goals & Users:* Conflict-Driven Clause Learning (CDCL) version and
     feature dependency solver that Either produces a valid locked dependency
     graph (`Cargo.lock` / `uv.lock`) or derives a minimal, human-readable
     **incompatibility proof tree** explaining why no version assignment exists.

#### 7.3 Mapping Domain 7 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_CleanBuild`: Pure, memoization-free topological evaluation from scratch
    (`Mokhov et al.` specification).
  - `L_IncBuild`: Stateful incremental engine (`Salsa` Red-Green, `Buck2 DICE`,
    or `Bazel Skyframe` with `ActionCache`).
  - `Query`: Sequence of workspace source edits $[W_0, W_1, \dots, W_m]$ +
    target key $k$.
  - `SemObs` (`obs : Out → SemObs`): Output artifact SHA-256 / byte payload at
    each revision $W_i$ (ignoring cache hit/miss counters).
  - `Partial.ub` (`defined = False`):
    - **Sandbox Escape / Undeclared Dependency Read:** Reading a host file or
      env var not committed to the `ActionKey` Merkle digest.
    - **Stale Artifact / Cache Poisoning:** Returning an incremental build result
      at $W_i$ that differs from `L_CleanBuild` on $W_i$.
    - **Dynamic Cycle Unsoundness:** Accepting a dependency cycle without raising
      `.CycleDetected`.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `Compiles L_CleanBuild L_IncBuild buildCodec CleanBuild DICE_or_Salsa`
    mechanizes **From-Scratch Consistency** across multi-step edit traces!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Invalidate-Everything (`bazel clean`)" Degeneracy Trap:**
    An incremental engine that clears its entire cache on every edit trivially
    satisfies From-Scratch Consistency (`Compiles L_CleanBuild L_IncBuild`)!
    Anneal's `CertifiedOptimizationPass` (mechanized in
    `anneal-behavior-codec-and-progress-refinement-2026`,
    `support/AntiDegeneracyAndCallbackFraming.lean`) directly enforces strict
    dynamic step reduction on incremental edit benchmarks, proving that Early
    Cutoff and Green-node reuse genuinely skip downstream recomputations!
  - `EventualBehaviorOf` makes the $O(|G|) \to O(1)$ step collapse on an Early
    Cutoff cache hit completely transparent.
  - `StepResult.externalCall` models spawning a `linux-sandbox` / `REAPI` action
    worker, where `boundaryInv` checks `sandboxMountedPaths ⊆ actionKeyHashedInputs`
    before executing the compiler subprocess!
- **`VerificationResult` and `TrustPolicy`:**
  - Certifies `PubGrub` resolution witnesses and conflict derivation trees in
    Lean (turning an untrusted SAT/CDCL solver into a proof-producing resolver)
    while scoping `.waive "sha256_collision_resistance"` in `TrustPolicy`.

---

### 8. Domain 8: ML, Tensor, and Polyhedral Compilers, GPU Kernel Verifiers, and Distributed SPMD Sharding

`Basis: documentation + source + derived`

#### 8.1 Domain Problem Space and Tool Families

Modern AI/HPC compilers (`XLA`, `MLIR` Affine/Linalg, `Halide`, `Triton`, `TVM`,
`Exo`, `Mirage`) transform pure mathematical tensor graphs through:
1. **Polyhedral & Schedule Transformations:** Tiling, fusion, loop skewing,
   sliding-window storage folding, and software pipelining, where an off-by-one
   bound or violated loop-carried dependence (`RAW`/`WAR`/`WAW`) silently reads
   stale SRAM or faults out of bounds.
2. **GPU Kernel Lowering:** Mapping blocked tiles across threads/warps with
   XOR-swizzled shared memory (`smem`), async `TMA` copies, and `mbarrier` /
   `__syncthreads()` synchronization, risking intra-warp data races and
   thread-divergent barrier deadlocks.
3. **Distributed SPMD Tensor Sharding (`XLA GSPMD`, `PartIR`, `Shardy`):**
   Partitioning single-device tensor graphs across multi-dimensional device
   meshes and inserting collective operations (`AllReduce`, `ReduceScatter`,
   `AllGather`, `AllToAll`), where a missing collective silently corrupts
   multi-million-dollar training runs.

#### 8.2 Exhaustive Tool Deep-Dives (8 Core Tool Families / 13 Concrete Tools)

1. **`MLIR-TV` (`llvm/mlir-tv`, Bang et al., CAV 2022 / LLVM Dev, Alive2-style
   SMT translation validation for MLIR `arith`/`linalg`/`tensor`/`memref`
   dialects) and `VeriHLO` / `Alive2` (`AliveToolkit/alive2`, Lopes et al.,
   PLDI 2021, DOI `10.1145/3453483.3454030`):**
   - *(1) Goals & Users:* Automated SMT translation validation catching
     miscompilations in LLVM (`Alive2`) and MLIR/StableHLO (`MLIR-TV`,
     `VeriHLO`) passes.
   - *(3) Design Philosophy & Tradeoffs:* Encodes source and target IR
     semantics (including `poison` and `undef` / UB refinement) into Z3
     bitvector/array/FP queries for bounded loop unrollings and concrete small
     tensor shapes. Finds dozens of compiler bugs, but cannot verify parametric
     $N \times M \times K$ tensor shapes or unbounded polyhedral loops without
     timeout, and trusts the C++ Z3 encoder.

2. **`Halide` (`halide/Halide`, Ragan-Kelley et al., PLDI 2013) and
   `verified-halide` (`halide/Halide` formal verification / Clément & Cohen,
   OOPSLA 2022, DOI `10.1145/3563321`; Kortekaas et al., VerCors Halide):**
   - *(1) Goals & Users:* Decouples pure functional image/tensor **algorithms**
     (`f(x, y) = ...`) from **schedules** (`split`, `reorder`, `tile`,
     `vectorize`, `compute_at`, `store_at`).
   - *(3) Design Philosophy & Tradeoffs:* Clément & Cohen (OOPSLA 2022) and the
     Coq/VerCors Halide verification projects prove that Halide's schedule-lowering
     passes preserve functional equivalence and buffer bounds by checking
     Presburger arithmetic producer-consumer coverage conditions (`∀ consumer
     read, box_provided ⊇ box_required`) and absence of out-of-bounds memory
     accesses.

3. **`Exo` (`exo-lang/exo`, Ikarashi et al., PLDI 2022, DOI
   `10.1145/3519939.3523446`; `Exo 2` ASPLOS 2025; `Exo-GPU`):**
   - *(1) Goals & Users:* User-Schedulable Language (USL) based on
     **Exocompilation** for writing high-performance matrix/tensor kernels
     targeting AVX-512, ARM Neon, Apple AMX, Gemmini, and NVIDIA Tensor Cores.
   - *(3) Design Philosophy & Tradeoffs:* Moves the hardware backend and
     scheduling policies *out* of the compiler into user-defined libraries,
     while keeping a small **effect-analysis and Presburger SMT equivalence
     checker** inside the compiler's TCB! Every primitive scheduling rewrite
     (` divide_loop`, `reorder_loops`, `stage_mem`, `replace` with hardware
     intrinsic instruction spec) is checked by verifying that read/write/reduce
     effects and integer index expressions are preserved under Z3 Presburger
     arithmetic.
   - *(4) Ecosystem Comparison:* Shares Anneal's philosophy of keeping the
     core soundness checker small while allowing arbitrary external scheduling
     strategies.

4. **Distributed Tensor Sharding Compilers: `XLA GSPMD` (Xu et al., arXiv
   `2105.04663`, Google), `PartIR` (Alabed et al., Google DeepMind, MLIR loop-based
   incremental partitioner), and `Shardy` (`openxla/shardy`, OpenXLA 2024–2026):**
   - *(1) Goals & Users:* Partition single-device `StableHLO` / JAX / PyTorch
     models across thousands of TPUs/GPUs using mesh-axis sharding annotations
     and automatic collective insertion.
   - *(2) History & Lineage:* `GSPMD` propagated sharding specs across XLA HLO
     graphs heuristically; `PartIR` modeled sharding as formal rewrite steps over
     explicit `spmd` tile loops and collectives in MLIR; **`Shardy` (`sdy`
     dialect in `openxla/shardy`)** unified the `GSPMD` and `PartIR` teams into
     Google/OpenXLA's canonical MLIR tensor partitioning system.

5. **Polyhedral Compilers & Farkas-Lemma Certifiers: `Polly` (`llvm/llvm-project/polly`,
   Grosser et al., 2012), `isl` (Integer Set Library, Verdoolaege, ICMS 2010),
   and `Pluto`Polyhedral (Bondhugula et al., PLDI 2008):**
   - *(3) Design Philosophy & Tradeoffs:* Represent loop iteration domains
     $\mathcal{D}_S$, memory access relations $\mathcal{A}_S$, and schedules
     $\theta_S(\vec{i})$ as Presburger sets and relations in `isl`. Legality of
     an affine schedule transformation requires that for every dependence pair
     $(\vec{i}, \vec{j}) \in \mathcal{R}_{\text{dep}}$,
     $\theta_T(\vec{j}) - \theta_S(\vec{i}) \ge 0$. By the **Affine Form of
     Farkas' Lemma** (Schrijver / Feautrier), $\psi(\vec{x}) \ge 0$ holds on a
     non-empty polyhedron $A\vec{x} + \vec{b} \ge \vec{0}$ iff $\psi(\vec{x}) \equiv
     \lambda_0 + \vec{\lambda}^T (A\vec{x} + \vec{b})$ for some non-negative
     Farkas multipliers $\lambda_k \ge 0$! Checking a Farkas multiplier
     certificate $\vec{\lambda} \ge 0$ requires only **elementary polynomial
     ring identity checking (`ring` / `omega` in Lean)** without trusting `isl`
     or an ILP solver!

6. **GPU Concurrency & Data-Race Verifiers: `GPUVerify` (`imperial/gpuverify`,
   Betts et al., OOPSLA 2012, DOI `10.1145/2384616.2384625`) and `Faial`
   (`umb-svl/faial`, Cogumbreiro et al., CAV 2021, DOI
   `10.1007/978-3-030-81685-8_19`):**
   - *(1) Goals & Users:* Verify CUDA and OpenCL GPU kernels for absence of
     intra-block shared-memory data races, inter-block global-memory data races,
     and **barrier divergence** (threads in the same warp/block taking different
     branches across `__syncthreads()`).
   - *(3) Design Philosophy & Tradeoffs:* `GPUVerify` reduces $N$-thread SIMD
     lockstep execution to a **2-thread arbitrary-pair product program** verified
     in Boogie/Z3; `Faial` introduces **Memory Access Protocols (MAPs)** that
     decouple barrier-aligned access phases into parallel, loop-invariant-free
     SMT checks, achieving exponential speedups over `GPUVerify` on real CUDA
     kernels.

7. **Equality-Saturation & Multi-Level Tensor Superoptimizers: `Tensat`
   (`uwplse/tensat`, Yang et al., MLSys 2021) and `Mirage`
   (`mirage-project/mirage`, Wu et al., OSDI 2025, arXiv `2405.05751`):**
   - *(3) Design Philosophy & Tradeoffs:* `Tensat` uses `egg` equality saturation
     with ILP extraction to optimize tensor graphs; `Mirage` (CMU) superoptimizes
     custom GPU kernels across three hierarchy levels (kernel graph, threadblock
     graph, thread graph) using **$\mu\text{Graphs}$** and checks equivalence
     via **probabilistic algebraic fingerprinting over finite fields $\mathbb{F}_p$**
     (Schwartz-Zippel lemma), discovering fused FlashAttention/Lora kernels that
     outperform Triton and cuBLAS.

#### 8.3 Mapping Domain 8 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - `L_Tensor`: Single-device mathematical `StableHLO` / `Halide` / `MLIR Linalg`
    semantics parameterized by symbolic dimension variables `(B S H D : Nat)`.
  - `L_SPMD` / `L_Kernel`: `Shardy`/`PartIR` multi-device SPMD program or
    scheduled `Exo`/`Halide`/CUDA kernel.
  - `Partial.ub` (`defined = False`): Out-of-bounds SRAM/HBM tile indexing,
    shared-memory data races or barrier divergence (`GPUVerify`/`Faial`), or
    collective shape/participation mismatch across mesh devices.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - **SPMD Sharding Is an Exact `PartialBehaviorCodec`:**
    In `Shardy` / `PartIR` / `GSPMD`:
    - `encodeQuery`: Partitions a global input tensor $T \in \mathbb{R}^{B \times D}$
      into per-device shard buffers $\{T_p\}_{p \in \text{Mesh}}$ according to the
      `sdy.sharding` annotation.
    - `decodeOut`: Reconstructs the global output tensor from the per-device
      shard buffers $\{O_p\}_{p \in \text{Mesh}}$, and **returns `none` if
      replicated shards on different devices disagree** (e.g., when a compiler
      pass forgets to insert an `AllReduce` after a partial-sum reduction along
      a contracted axis)!
    - `decode_encode_out` and `encode_of_decode_some` enforce that the sharding
      layout is a lossless partial bijection, and `Compiles L_Tensor L_SPMD
      shardingCodec SingleDeviceProg ShardedProg` certifies the entire SPMD
      partitioner!
  - **Farkas-Lemma Polyhedral Certifier via `Abstracts`:**
    `Polly`/`isl` runs outside the TCB and emits non-negative Farkas multipliers
    $\vec{\lambda} \ge 0$ witnessing loop-dependence causality. Lean checks the
    linear combination identity via `ring`/`omega` inside `theory/`, discharging
    `Abstracts L_Polyhedra L_Kernel` and `Compiles L_Tensor L_Kernel` with zero
    solver trust!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - `EventualBehaviorOf` collapses $O((M/T_M)(N/T_N)(K/T_K))$ tiled inner loop
    iterations and ring-collective steps into a 1-step tensor operation while
    checking `GPUVerify`/`Faial` barrier/race safety at every prefix step.
  - `StepResult.externalCall` models opaque vendor microkernels (`cuBLAS`,
    `wgmma`, TPU MXU) with `boundaryInv` enforcing 128-byte pointer alignment,
    leading-dimension stride divisibility, and SRAM residency.
- **`VerificationResult` and `TrustPolicy`:**
  - Turns `Mirage`'s probabilistic $\mathbb{F}_p$ fingerprint equivalence check
    or floating-point reassociation (`(a + b) + c` vs. `a + (b + c)` in
    tree-reduction `AllReduce`) into an explicit, auditable `TrustPolicy` item
    (`.waive "fp_associativity_in_allreduce"` or `.waive "schwartz_zippel_fp"`),
    or requires exact algebraic proof when `waived = []`.

---

### 9. Domain 9: Reactive Streaming Watermarks and Verified Lexer, Regex, and Parser Compilers

`Basis: documentation + source + derived`

#### 9.1 Domain Problem Space and Tool Families

This domain bridges two closely related finite-transducer and progress-tracking
Verification problems:
1. **Out-of-Order Streaming Engines & Watermarks (`Timely Dataflow`,
   `StreamBox`, `Apache Flink` ABS):** Events arrive out of order with logical
   event-time timestamps $t_e$, punctuated by watermarks $W(t)$ ("no future
   record has $t_e < W(t)$") and asynchronous checkpoint barriers (`Chandy-Lamport`
   ABS). Advancing a watermark prematurely drops valid in-flight events; holding
   a watermark at $-\infty$ forever stalls all window emissions and leaks memory.
2. **Verified Lexer, Regular-Expression, and Parser Compilers (`Coqlex`,
   `VeriLex`, `Ausaf-Dyckhoff-Urban` POSIX Regex, `lean-regex`, `CoStar`,
   `TRX`):** Compile declarative regular expressions and context-free / PEG
   grammars into high-speed DFA/VM/ALL(*) state machines while proving
   soundness, completeness, longest-match POSIX disambiguation, and absence of
   catastrophic backtracking (ReDoS) or left-recursion non-termination.

#### 9.2 Exhaustive Tool Deep-Dives (9 Core Tools)

1. **`Timely Dataflow` (`TimelyDataflow/timely-dataflow`, Murray, McSherry,
   Isaacs, Isard, Barham, Abadi, SOSP 2013, DOI `10.1145/2517349.2522738`;
   Abadi, McSherry, Plotkin, FossACS 2015):**
   - *(1) Goals & Users:* Low-latency cyclic dataflow runtime in Rust powering
     `Differential Dataflow` and `Materialize`.
   - *(2) History & Lineage:* Created at Microsoft Research Silicon Valley
     (`Naiad`) by Derek Murray, Frank McSherry, et al.; formalized by Martín
     Abadi, Frank McSherry, and Gordon Plotkin (2015).
   - *(3) Design Philosophy & Tradeoffs:* Tracks distributed progress across
     nested loop scopes using partially ordered **Pointstamps**
     `(location, timestamp) ∈ Location × Time` and **Capabilities** (an operator
     at `loc₁` holding capability `t₁` may emit messages at `(loc₂, t₂)` iff
     `(loc₁, t₁) ≤ (loc₂, t₂)` in the causal path-summary preorder). Workers
     maintain the minimal **Antichain Frontier** of active pointstamps; when no
     pointstamp in the frontier precedes `(loc, t)`, the runtime delivers a
     notification that timestamp `t` at `loc` is complete.
   - *(5) Formal Theory & TCB:* Partially ordered multiset transition semantics
     and antichain safety proof (Abadi-McSherry-Plotkin).

2. **`StreamBox` (`elijahr/StreamBox`, Miao et al., USENIX ATC 2017) and
   `Apache Flink ABS` (Asynchronous Barrier Snapshotting, Carbone et al.,
   arXiv `1506.08603` / VLDB 2017):**
   - *(1) Goals & Users:* High-throughput out-of-order stream engines.
   - *(3) Design Philosophy & Tradeoffs:* `StreamBox` decouples physical record
     containers (`Bundles`) from logical watermark punctuations so multi-core
     workers process out-of-order bundles lock-free while tracking the minimum
     in-flight event timestamp across upstream operators. `Flink ABS` adapts
     the **Chandy-Lamport distributed snapshot algorithm** to DAG stream
     pipelines by injecting `CheckpointBarrier(n)` markers into data streams,
     aligning barriers at multi-input operators (or buffering in-flight channel
     records in Unaligned Checkpoints), and committing external sinks via Two-Phase
     Commit (`TwoPhaseCommitSinkFunction`) to guarantee **exactly-once** state
     consistency across worker crashes.

3. **`Coqlex` (`Coqlex/coqlex`, Hills, Malik, et al., 2021–2023, arXiv
   `2301.10479`) and `VeriLex` (Egolf, Lasser, Casinghino, Coq verified lexer):**
   - *(1) Goals & Users:* Verified replacements for `ocamllex`/`flex` in Coq,
     closing the unverified lexer front-end gap in CompCert-style compilers.
   - *(3) Design Philosophy & Tradeoffs:* Prove in Coq that the generated
     longest-match, first-rule-priority tokenizer refines the declarative
     list-of-regexes specification using Brzozowski derivatives and fuel-bounded
     maximal munch.

4. **Verified Brzozowski/Thompson Regular-Expression Matchers:
   `Ausaf-Dyckhoff-Urban POSIX Lexing` (`Archive of Formal Proofs: Posix-Lexing`,
   Ausaf, Dyckhoff, Urban, ITP 2016, DOI `10.1007/978-3-319-43144-4_5`) and
   `lean-regex` (`pandaman64/lean-regex`, Sugiura, Lean 4 verified VM/DFA regex
   engine, 2024–2026):**
   - *(1) Goals & Users:* Formally verified regular-expression matching with
     submatch capture groups (`POSIX` longest-match / Perl greedy disambiguation)
     and linear-time $O(|s|)$ execution (immune to ReDoS catastrophic
     backtracking).
   - *(3) Design Philosophy & Tradeoffs:* Ausaf, Dyckhoff, and Urban mechanized
     Sulzmann-Lu bit-coded Brzozowski derivatives in Isabelle/HOL to prove exact
     POSIX longest-match submatch extraction. `lean-regex` (written in **Lean 4**)
     compiles regular expressions into a PikeVM / Thompson NFA virtual machine
     and proves inside the Lean 4 kernel that the VM matcher is sound and
     complete with respect to the inductive `Regex.Matches` semantics!

5. **`CoStar` (`slasser/CoStar`, Lasser, Casinghino, Fisher, Roux, PLDI 2021,
   DOI `10.1145/3453483.3454053`) and `TRX` (Koprowski & Binsztok, LMCS 2011,
   DOI `10.2168/LMCS-7(2:18)2011`):**
   - *(1) Goals & Users:* Formally verified parser engines in Coq.
   - *(3) Design Philosophy & Tradeoffs:* `CoStar` verifies Parr-Harwell's
     **$\text{ALL}(*)$** adaptive LL(*) parsing algorithm (the algorithm behind
     ANTLR4) in Coq, proving soundness, completeness, and termination on all
     non-left-recursive CFGs via DFA prediction over augmented transition
     networks (ATNs). `TRX` formalizes **Parsing Expression Grammars (PEGs)**
     (Ford, POPL 2004) in Coq and enforces termination on every grammar using a
     static structural **well-foundedness check (`wf_peg`: no nullable loop bodies
     and no unconsumed left recursion)** discharged over the product order on
     `(remaining_input_length, expression_height)`.

#### 9.3 Mapping Domain 9 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - *Streaming:* `L_IdealBatch` (sorted event-time window specification) vs.
    `L_Stream` (`Timely Dataflow` / `Flink ABS` out-of-order + barrier runtime).
  - *Lexing/Parsing:* `L_Grammar` (inductive `Regex.Matches` / POSIX maximal
    munch / CFG derivation tree) vs. `L_Automaton` (`lean-regex` PikeVM,
    `CoStar` ALL(*) ATN simulator, or `TRX` PEG interpreter).
  - `Partial.ub` (`defined = False`):
    - **Premature Watermark Advancement:** Firing/GC'ing a window at timestamp
      $t$ while an upstream operator or channel still holds a capability
      $t' \le t$ (`Timely Dataflow` frontier invariant violation).
    - **Duplicate/Lost State on Checkpoint Recovery:** Violating `Flink ABS`
      exactly-once barrier alignment.
    - **Grammar Left-Recursion / ReDoS Divergence:** Executing an ill-founded
      PEG (`¬ wf_peg`) or backtracking exponential regex traps.
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - `Compiles L_IdealBatch L_Stream streamCodec IdealWindowQuery FlinkOrTimely`
    proves that out-of-order buffering + watermark emission + Chandy-Lamport
    checkpoint recovery produces the **exact same** output window aggregates as
    a failure-free sorted batch run!
  - `Abstracts L_Antichain L_Stream frontierCodec PointstampSummary TimelyGraph`
    models `Timely Dataflow`'s distributed antichain frontier tracking as an
    abstract interpretation over in-flight capabilities.
  - `Compiles L_Grammar L_Automaton parseCodec GrammarSpec PikeVM_or_ALLStar`
    embeds `lean-regex` and `CoStar` directly into Anneal's compiler hierarchy.
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Hold-Watermark-at-$-\infty$-Forever" Goodhart Loophole:**
    A streaming engine that never advances its watermark ($W(t) = -\infty$)
    never prematurely fires a window—satisfying watermark safety vacuously by
    emitting zero outputs! In Anneal, `ProductiveOn BoundedOutOfOrderPre
    StreamPipeline` + `EventualBehaviorOf` forces the engine to advance
    watermarks, drain capabilities, and emit closed window results in finite
    steps for every bounded-lateness input prefix.
  - `StepResult.externalCall` models external `TwoPhaseCommitSink` commits in
    `Flink ABS`, where `boundaryInv` verifies that **every** parallel subtask
    has acknowledged `CheckpointBarrier(n)` before the sink commits externally!
- **`VerificationResult` and `TrustPolicy`:**
  - Scopes external Kafka partition watermark-monotonicity assumptions in
    `TrustPolicy` while machine-checking internal antichain progress and
    Chandy-Lamport barrier recovery.

---

### 10. Domain 10: Wire-Format Schemas, Bi-Directional Lenses, and Durable Execution Workflows

`Basis: documentation + source + derived`

#### 10.1 Domain Problem Space and Tool Families

Distributed services upgrade rolling-style across heterogeneous versions:
1. **Binary Wire Parsers & Zero-Copy Serializers (`EverParse`/`3D`, `Narcissus`,
   `Vest`, `zerocopy`, `Cap'n Proto`, `FlatBuffers`, `rkyv`):** Parse untrusted
   network byte slices into typed domain structures without buffer overreads,
   integer overflows, alignment faults, non-canonical wire encodings (malleability),
   or unknown-field truncation during proxy read-modify-write pass-through.
2. **Bi-Directional Schema Lenses (`Cambria`, `Boomerang`, `Buf`):** Translate
   API payloads across schema versions ($V_1 \leftrightarrows V_2$) while
   preserving round-trip lens laws (`GetPut`, `PutGet`, `PutPut`).
3. **Durable Execution Workflows (`Temporal`, `Restate`, `P Language`):**
   Execute long-running sagas and workflows by persisting an append-only event
   history log and replaying the workflow code from the beginning on worker
   recovery. Any **non-deterministic replay divergence** (where replayed code
   issues a command sequence incompatible with the recorded history log) causes
   a fatal `NonDeterministicWorkflowError` stall in production.

#### 10.2 Exhaustive Tool Deep-Dives (7 Core Tool Families / 11 Concrete Tools)

1. **`EverParse` and `3D` (`project-everest/everparse`, Ramananandro et al.,
   USENIX Security 2019; Swamy et al., OOPSLA 2022) and `LowParse`:**
   - *(1) Goals & Users:* Microsoft Research / Project Everest framework
     generating formally verified, zero-copy C and Rust binary message validators
     and parsers from `3D` (Dependent Data Descriptions) specifications, deployed
     inside the **Windows Kernel VirtualSwitch (`vmswitch.sys`)**, Hyper-V, TLS
     1.3 (`miTLS`), and DICE/TPM firmware.
   - *(3) Design Philosophy & Tradeoffs:* Compiles declarative C-like struct
     format specs with dependent field constraints (e.g., length fields, tag
     unions, bounds checks) into **F\*** / **Low\*** / **Pulse** validators that
     check wire validity in-place with zero heap allocations. Proves memory
     safety, arithmetic overflow freedom, parser injectivity, and **non-malleability**
     (canonical serialization: `∀ b₁ b₂, parse b₁ = some v ∧ parse b₂ = some v → b₁ = b₂`).

2. **`Narcissus` (`uwplse` / Delaware, Sorawit, et al., PACMPL / POPL 2019, DOI
   `10.1145/3290389`, MIT / Purdue / UPenn):**
   - *(1) Goals & Users:* Coq combinator framework (`Fiat` ecosystem) for
     automatically synthesizing correct-by-construction binary encoders and
     decoders for network protocols (DNS, TCP, Ethernet, ARP, Protobuf varints).
   - *(3) Design Philosophy & Tradeoffs:* Separates relational format
     specifications (`Format : Domain → ByteString → Prop`) from executable
     encoders and decoders, using Coq tactics to automatically derive a
     decoder `decode` and prove round-trip correctness (`encode m bs →
     decode bs = some m`).

3. **`Vest` (`secure-foundations/vest`, Cai, Bosamiya, et al., CMU / USENIX
   Security 2025) and Rust Zero-Copy Frameworks (`google/zerocopy`,
   `Cap'n Proto`, `FlatBuffers`, `rkyv`):**
   - *(1) Goals & Users:* `Vest` is a formally verified parser and serializer
     combinator library for **Rust** built in **Verus** (`verus-lang/verus`),
     providing panic-free, zero-copy slice parsing with machine-checked proofs
     of round-trip inversion (`parse(serialize(v)) == Ok(v)` and
     `serialize(parse(b)) == Ok(b)`—ruling out format malleability and parser
     differential bugs like CVE-2020-0601!). Connects directly to `zerocopy`
     (`TryFromBytes`, `IntoBytes`, `KnownLayout`) and archive validators like
     `rkyv::check_archived_root` and `FlatBuffers` vtable verifiers.

4. **`Cambria` (`inkandswitch/cambria-project`, Litt, Hardenberg, Orion, Ink &
   Switch 2020) and `Boomerang` (`boomerang-lang/boomerang`, Bohannon, Foster,
   Pierce, Pilkiewicz, Schmitt, POPL 2008, DOI `10.1145/1328438.1328487`):**
   - *(1) Goals & Users:* Bi-directional data lenses translating structured
     documents (`Cambria` for JSON/YAML API & local-first schema evolution) and
     strings (`Boomerang` regular string lenses at UPenn) across versions.
   - *(3) Design Philosophy & Tradeoffs:* `Boomerang` pioneered compositional
     lens combinators satisfying the **Well-Behaved Lens Laws**:
     - `GetPut`: `put s (get s) = s`
     - `PutGet`: `get (put s v) = v`
     - `PutPut`: `put (put s v₁) v₂ = put s v₂`
     `Cambria` applies **Symmetric / Edit Lenses** (Hofmann, Pierce, Wagner,
     POPL 2011) to JSON schemas using a **complement store** (cloud/unknown-field
     storage) so that when a $V_2$ document is downgraded to $V_1$, edited by a
     $V_1$ client, and upgraded back to $V_2$, all $V_2$-only fields survive
     intact!

5. **`Buf` (`bufbuild/buf`, Protobuf schema linter and `buf breaking` wire
   compatibility checker):**
   - *(1) Goals & Users:* Industry-standard CLI enforcing syntactic and wire-level
     backward/forward compatibility across `.proto` commits (`FILE`, `PACKAGE`,
     `WIRE`, and `WIRE_JSON` breaking-change categories).

6. **Durable Execution & Event-Driven State Machine Engines: `Temporal`
   (`temporalio/temporal`), `Restate` (`restatedev/restate`, Ewen et al.), and
   `P Language` (`p-org/P`, Desai, Gupta, Jackson, Qadeer, Rajamani, Zufferey,
   PLDI 2013, DOI `10.1145/2491956.2462184`, MSR / AWS):**
   - *(1) Goals & Users:* `Temporal` and `Restate` execute fault-tolerant
     microservices and workflows via deterministic event-journal replay; `P`
     is an asynchronous communicating state-machine DSL with integrated model
     checking and symbolic execution used by AWS (S3, Firecracker) and Microsoft
     (Windows USB 3.0 driver stack).
   - *(3) Design Philosophy & Tradeoffs:* In `Temporal` and `Restate`, when a
     worker crashes mid-workflow, a new worker replays the workflow function
     from the start against the persisted journal of completed side effects
     (`ActivityTaskCompleted`, `TimerFired`). If a code deployment changes the
     order of nondeterministic calls without a ` workflow.GetVersion` / patch
     gate, replay fails with a non-determinism error.

#### 10.3 Mapping Domain 10 onto Anneal's Four `trusted/` Primitives

- **`Language`, `Partial`, and `SemObs`:**
  - *Wire Formats & Lenses:* `L_Domain` (typed domain values + unknown-field
    complement) vs. `L_Wire` (serialized wire bytes / zero-copy buffer slices).
  - *Durable Workflows:* `L_IdealSaga` (crash-free sequential workflow execution)
    vs. `L_Replay` (`Temporal`/`Restate` journal-replay state machine across
    arbitrary crash-recovery boundaries and code upgrades $V_1 \to V_2$).
  - `Partial.ub` (`defined = False`):
    - **Parser Buffer Overread / Unaligned Zero-Copy Cast:** Reading past slice
      bounds or transmuting an invalid bit pattern (`zerocopy` / `Vest`).
    - **Unknown-Field Loss in Proxy Pass-Through:** A $V_1$ intermediary
      deserializing and re-serializing a $V_2$ message and dropping $V_2$ fields.
    - **Durable Replay Non-Determinism (`Temporal`/`Restate`):** Replaying
      workflow code against a committed journal prefix and emitting a command
      type or ID that mismatches the journal entry!
- **`BehaviorCodec`, `Compiles`, and `Abstracts`:**
  - **Anneal's `PartialBehaviorCodec` IS the Exact Mathematical Primitive of
    `EverParse`, `Narcissus`, `Vest`, and `Cambria`/`Boomerang`!**
    Compare the fields of `PartialBehaviorCodec L₁ L₂` (in
    `anneal-behavior-codec-and-progress-refinement-2026`,
    `support/BehaviorCodecExpressiveness.lean`) with `Vest`/`EverParse`/`Boomerang`:
    1. `encodeOut : L₁.Out → L₂.Out` is the **Serializer / `put`**.
    2. `decodeOut : L₂.Out → Option L₁.Out` is the **Partial Parser / Validator /
       `get`**.
    3. `decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁` is the
       **Round-Trip Deserialization / `GetPut` Law**!
    4. `encode_of_decode_some : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`
       is **`EverParse` & `Vest`'s Canonical Non-Malleability / `PutGet` Law**!
    5. `obs_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁`
       is **Cross-Version Semantic Projection Preservation (`Cambria` / `Buf`)**!
- **`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, and
  `StepResult.externalCall`:**
  - **Closing the "Reject-All-Messages (`return Err`)" Parser Goodhart Trap:**
    A parser that returns `None` (`Err(InvalidInput)`) on 100% of inputs
    trivially satisfies partial soundness (`decodeOut b = some v → Valid v`)!
    In Anneal, `ProductiveOn ValidSchemaV1Pre DeserializerV2` proves **Backward
    Wire Compatibility** (every valid $V_1$ wire message parses to `some` in
    $V_2$), and `ProductiveOn ValidSchemaV2Pre DeserializerV1` proves **Forward
    Wire Compatibility**!
  - **Certifying `Temporal`/`Restate` Replay Determinism via `StepResult.externalCall`:**
    Each durable side-effect (`ExecuteActivity`, `Sleep`, `GetVersion`) is a
    `StepResult.externalCall boundaryInv branches` where `boundaryInv` checks
    that during replay mode, the emitted command matches the next entry in the
    recorded workflow history log! Proving `Compiles L_WorkflowV1 L_WorkflowV2`
    over all recorded $V_1$ journal prefixes mathematically certifies that a
    live `Temporal`/`Restate` workflow upgrade will never throw
    `NonDeterministicWorkflowError`!
- **`VerificationResult` and `TrustPolicy`:**
  - Requires an explicit, auditable waiver (`waived := [.breakingFieldRemoval 4]`)
    whenever a team intentionally breaks wire compatibility or deprecates an old
    workflow version branch.

---

### 11. Cross-Domain Synthesis Matrix: Goodhart Failure Modes and Anneal Primitive Defenses

`Basis: derived`

The table below synthesizes how all 10 domains exhibit isomorphic "degenerate
implementation / Goodhart" failure modes when specifications are checked without
Anneal's four primitives, and how `Partial`, `PartialBehaviorCodec`,
`ProductiveOn`, `EventualBehaviorOf`, `StepResult.externalCall`, and
`ScopedVerificationResult` close each loophole uniformly:

| Domain & Representative Tools | Degenerate "Goodhart Cheat" Admitted by Naive Specifications | How Anneal's 4 `trusted/` Primitives Block the Cheat |
| :--- | :--- | :--- |
| **1. SQL / Datalog & IVM** (`Cosette`, `UDP`, `SPES`, `WeTune`, `QCert`, `DBSP`/`Feldera`, `Calcite`, `Soufflé`) | Compile complex joins to `.aborted .outOfMemory`, conflate set/bag multiplicities, or push `1/x` below `WHERE x <> 0` | `obs_decodeOut` locks in the multiset & Kleene-3VL spine; `ProductiveOn` forbids synthetic errors; `defined` rejects new evaluation-order traps |
| **2. Crash-Safe Storage** (`FSCQ`, `Perennial`/`DaisyNFS`, `Yggdrasil`, `VeriBetrKV`, `BilbyFS`, `Flashix`, `SplinterDB`) | Have `recover()` always return `Err(Corrupt)`, drop LSM tombstones early, or flush dirty B+-tree pages before WAL `fsync` | `StepResult.externalCall` enforces `flushedLSN >= pageLSN` in `boundaryInv` and branches demonically over crash subsets; `ProductiveOn` forces `recover()` to succeed |
| **3. Distributed Consensus & Txns** (`Verdi`, `IronFleet`, `Ivy`, `Aneris`, `Chapar`, `VeriFx`, `TLAPS`, `FoundationDB`, `Elle`) | Abort 100% of client transactions to be trivially "serializable", or never elect a leader after GST | `ProductiveOn ContentionFreeAfterGST` forces transactions to `.Committed`; `Abstracts` + `Compiles` proves refinement to serial execution |
| **4. SDN / P4 & BGP Networking** (`Batfish`, `Minesweeper`, `Bagpipe`, `NetKAT`, `p4v`, `Vera`, `Petr4`/`Poulet4`, `Gauntlet`, `APKeep`, `NV`/`ShapeShifter`) | Emit a `DROP ALL` firewall to satisfy tenant isolation, or leave BGP Dispute Wheels that oscillate forever | `obs_decodeOut` + `ProductiveOn AuthorizedPre` forces positive delivery of allowed traffic; `EventualBehaviorOf` rejects non-terminating BGP oscillations |
| **5. Cloud IaC & K8s Controllers** (`Anvil`, `Sieve`, `K8s-TLA+`, `Conftest`, `Checkov`, `Tiros`, `Rehearsal`) | Return `RequeueAfter(∞)` (never reconcile) or cause a 30s availability drop during a rolling update | `EventualBehaviorOf` enforces **all-prefix intermediate safety** (`ReachesPrefix` at every step $0 \le i \le n$) and **eventual convergence (ESR)** |
| **6. Authorization & Diff. Privacy** (`Cedar`/`cedar-spec`, `Zelkova`, `Margrave`, `Zanzibar`/`SpiceDB`, `OPA`, `OpenDP`, `Chorus`, `Fuzz`/`DFuzz`, `CertiPriv`) | Compile residual SQL filters to `WHERE FALSE` (deny all), or release DP aggregates without budget/sensitivity checks | `obs_decodeOut` preserves `Allow ↔ Allow` bijectively; `InhabitedPre` flags shadowed `permit` rules; `StepResult.externalCall` gates DP release on `budget >= ε` |
| **7. Build Systems & Incremental Comp.** (`Build Systems à la Carte`, `Pluto`, `Salsa`, `Buck2 DICE`, `Adapton`, `Skyframe`, `PubGrub`) | Mount undeclared host files into the sandbox, or invalidate 100% of the cache (`clean`) on every edit | `StepResult.externalCall` checks `sandboxMounts ⊆ hashedInputs`; `obs_decodeOut` proves From-Scratch Consistency; `CertifiedOptimizationPass` enforces Early Cutoff |
| **8. ML / Tensor / GPU Compilers** (`MLIR-TV`, `verified-halide`, `Exo`, `PartIR`/`GSPMD`/`Shardy`, `Polly`/`isl`, `GPUVerify`/`Faial`, `Tensat`/`Mirage`) | Forget an `AllReduce` across TPU shards, or mis-tile a GPU shared-memory loop with barrier divergence | Sharding `PartialBehaviorCodec` returns `decodeOut = none` if replicated shards disagree; `defined` rejects SRAM races and barrier divergence |
| **9. Streaming & Verified Parsing** (`Timely Dataflow`, `StreamBox`, `Flink ABS`, `Coqlex`, `VeriLex`, `lean-regex`, `CoStar`, `TRX`) | Hold watermarks at $-\infty$ forever so windows never fire with wrong data, or loop on left-recursive PEGs | `ProductiveOn` + `EventualBehaviorOf` forces watermark progress and window emission; `defined` enforces `TRX`/`CoStar` termination guards |
| **10. Wire Schemas, Lenses & Workflows** (`EverParse`, `Narcissus`, `Vest`, `Cambria`/`Boomerang`, `Buf`, `Temporal`/`Restate`, `P`) | Return `ParseError` on all wire bytes, drop unknown fields in proxies, or diverge on `Temporal` workflow replay | `PartialBehaviorCodec` laws directly encode `GetPut`/`PutGet`/non-malleability; `ProductiveOn` enforces parse totality; `externalCall` checks replay journal parity |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **SQLSolver (SIGMOD 2024), VeriEQL (OOPSLA 2024), Polygon (OOPSLA 2024),
  SeQLean (Lean 4 SQL), Mediator (PLDI 2018), and DBToaster / F-IVM:** Unbounded
  $\text{LIA}^*$ bag-equivalence provers, 3VL NULL/constraint SMT checkers, Lean
  4 relational algebra, and higher-order ring IVM compilers.
- **SFSCQ / DISKSEC (OSDI 2018), Argosy (`mit-pdos/argosy`, PLDI 2019), BesFS,
  Notary (SOSP 2019), and ALICE (OSDI 2014):** Compositional crash-safe storage
  recovery, storage non-interference, and persistence vulnerability explorers.
- **Grove (`mit-pdos/grove`, SOSP 2023), Trillium (`logsem/trillium`, POPL
  2021), Velisarios (ESOP 2018), Armada (`microsoft/armada`), and ByMC:**
  Perennial/Iris time-lease distributed separation logic, TLA trace refinement,
  Coq PBFT verification, and threshold automata model checking.
- **`bf4` (`verified-network-toolchain/bf4`, SIGCOMM 2020), Plankton/Hoyan
  (NSDI/SIGCOMM 2020), SecGuru/NoD (Azure), and Vigor/Klint (`vigor-nf/vigor`,
  SOSP 2019 / OSDI 2022):** Controller-guard synthesis for P4, packet
  equivalence-class BGP checking, and end-to-end verified C/binary network
  functions.
- **Welder (2024-2025) and Acto (`acto-project/acto`, SOSP 2023); Quacky, Duet,
  and ShadowDP/CheckDP; PIE (`metaborg/pie`), Jane Street `Incremental`, and
  Skip:** Compositional multi-controller Kubernetes verification, quantitative
  IAM/DP verifiers, and statically typed early-cutoff build pipelines.
- **TASO (SOSP 2019), PET (OSDI 2021), Glenside, CuTe Layout Algebra
  (`NVIDIA/cutlass`), Isabelle `Timely_Dataflow` (`isa-afp`), Flumina, BiGUL,
  and HasChor/Zooid:** Tensor superoptimizers, GPU `(Shape, Stride)` layout
  algebra, Isabelle/HOL Timely Dataflow progress proofs, Agda putback lenses
  (`BehaviorCodec`), and choreographic projection.

## Boundaries

The following scope boundaries and open questions govern the findings in this
report:

- **Mechanized domain instantiations (`not examined`):** While the core
  structural primitives (`Partial`, `PartialBehaviorCodec`, `Compiles`,
  `Abstracts`, `EventualBehaviorOf`, `CertifiedOptimizationPass`,
  `StepResult.externalCall`, and `ScopedVerificationResult`) are fully
  mechanized in Lean 4.34.1 across `joshlf/anneal@e6a0b2da5ec3` and
  `google/zerocopy@df55c524a051`, full domain object-language semantics for the
  86 external tools (such as a complete SQL-99 AST or `P4_16` parser inside
  Anneal's repository) were **not examined** as executable Lean 4 artifacts in
  this package.
- **Probabilistic and quantitative metrics in `Trusted/Refinement.lean`
  (`known not to apply` without `theory/` encoding):** `Trusted/Refinement.lean`
  defines `Behavior` over boolean-valued propositions (`Out → Prop`) and strict
  equality of observations (`L₂.obs o₂ = L₁.obs o₁`). Direct quantitative
  coupling metrics (such as $(\epsilon, \delta)$-differential privacy in
  `OpenDP`/`CertiPriv` or ULP floating-point error bounds in `XLA`/`Mirage`) are
  **known not to apply** as primitive fields of `Trusted.Language` unless
  encoded via a 2-safety product language $L^2$ carrying deterministic coupling
  or interval witnesses in `theory/`.
- **Infinite-trace fairness and liveness beyond finite horizons (`unsupported`
  in finite-prefix `ReachesPrefix` alone):** Both `BehaviorOf`
  (`Trusted/StepResult.lean:176`) and `EventualBehaviorOf`
  (`support/BehaviorCodecExpressiveness.lean`) intentionally avoid coinductive
  infinite traces and `Classical.choice` by quantifying over finite step budgets
  `steps : Nat`. Unbounded weak/strong fairness properties ($\square \lozenge A
  \implies \square \lozenge B$) over genuinely non-terminating executions that
  cannot be reduced to finite horizon or ranking-function bounds (`Padon et al.`
  liveness-to-safety or bounded watermark horizons $W_k$) are **unsupported** by
  `ReachesPrefix` without a ranking-function or horizon parameterization in
  `Query`.
- **Proprietary tool internals (`unknown`):** For closed-source industrial
  systems examined via published papers (`SlabCity`, `Zelkova`, `Tiros`,
  `Zanzibar`, `XLA PartIR`), internal implementation details beyond their
  published specifications and open-source counterparts (`Shardy`, `SpiceDB`,
  `cedar-spec`) remain **unknown**.

## Evidence

1. **Anneal Trusted Core and MIR-to-x86-64 Repositories (`source`):**
   - `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (`trusted-core`):
     - `trusted/lean/Trusted/Refinement.lean:208-471`: Definitions of `Preorder`,
       `Partial`, `Partial.pure`, `Partial.ub`, `instPreorderPartial`,
       `Monotone`, `Behavior`, `Language`, `Language.SpecOn`,
       `Language.WellFormedOn`, `Compiles`, `Abstracts`, `Compiler`,
       `Compiler.SoundOn`, `Compiler.Verified`, `TrustedAssumption`,
       `TrustPolicy`, and `VerificationResultOn`.
     - `trusted/lean/Trusted/StepResult.lean:58-198`: Definitions of
       `TerminationKind`, `StepResult`, `PrefixOutcome`, `PrefixOutcome.isSafe`,
       `ExecQuery`, `ExecOut`, `SmallStepMachine`, `ReachesPrefix`,
       `BehaviorOf`, and `SmallStepMachine.toLanguage`.
     - `theory/Anneal/Refinement.lean:50-286`: Proofs of `ub_top`, `ub_le_iff`,
       `le_specOn_iff`, `le_wellFormedOn_iff`, `pass_trans`, `Compiles.comp`,
       `Abstracts.comp`, `Compiler.SoundOn.verify`, and `verify_through_passes`.
     - `theory/Anneal/StepResult.lean:38-179`: Definitions of `TotalStep` and
       `InhabitedDemonic`, and proofs of `exists_reaches_prefix`,
       `non_vacuity_at_every_depth`, and `behaviorOf_le_specOn`.
   - `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`):
     - `trusted/lean/Trusted/X86Semantics.lean`,
       `theory/Anneal/Compiler/NaiveCodegen.lean`, and
       `theory/Anneal/Compiler/Peephole.lean`.
2. **Anneal Trusted-Boundary Hardening Corpus (`source` + `execution`):**
   - `google/zerocopy@df55c524a051d59e7dd35564f282b30d29133392` (`reference`):
     - `reports/anneal-behavior-codec-and-progress-refinement-2026/REPORT.md`
       and `support/BehaviorCodecExpressiveness.lean` (`PartialBehaviorCodec`,
       `EventualBehaviorOf`, `eventual_wellFormed_iff_prefix_wellFormed`,
       `CertifiedOptimizationPass`).
     - `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/REPORT.md`
       and `support/StructuralExternalCallAndCanaries.lean:148-236`
       (`StepResult.externalCall`, `CallerFramePreserved`,
       `open_world_callback_composition_sound`).
     - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/REPORT.md`
       and `support/ProofGatedCompilationAndTrustPolicy.lean` (`TCBModel`,
       `BoundaryCodec`, `ScopedVerificationResult`,
       `proof_gated_compilation_eliminates_ir_from_tcb`).
   - Existing `reference` corpus report on incremental computation:
     - `reports/adapton-names-identity-freshness-2014-2018/REPORT.md`.
3. **Primary Literature and Open-Source Coordinates Across All 10 Domains
   (`documentation` + `normative` + `source`, observed `2026-10-31`):**
   - **Domain 1:** `uwdb/Cosette` & `uwdb/HoTTSQL` (DOI `10.1145/3035918.3056447`,
     `10.1145/3009837.3009848`); `UDP` (DOI `10.14778/3236187.3236200`);
     `EQUITAS` (DOI `10.1145/3299869.3319869`); `SPES` (DOI
     `10.1109/ICDE53745.2022.00201`); `Qex` (DOI `10.1007/978-3-642-17511-4_24`);
     `we-tune/WeTune` (DOI `10.1145/3514221.3526125`); `SlabCity` (DOI
     `10.1145/3589297`); `datacert/datacert`; `querycert/qcert` (DOI
     `10.1145/3035918.3056101`); `feldera/feldera` (`DBSP`, DOI
     `10.14778/3587136.3587140`); `MaterializeInc/materialize`;
     `cockroachdb/cockroach` (`pkg/sql/opt/optgen`); `apache/calcite`;
     `risinglightdb/risinglight`; `souffle-lang/souffle`.
   - **Domain 2:** `mit-pdos/fscq` (DOI `10.1145/2815400.2815402`,
     `10.1145/3132747.3132776`); `mit-pdos/perennial` & `mit-pdos/daisy-nfsd`
     (DOI `10.1145/3341301.3359632`, OSDI 2022); `uwplse/yggdrasil` (OSDI 2016);
     `secure-foundations/veribetrkv-osdi2020` (OSDI 2020); `NICTA/cogent`
     (`BilbyFS`, DOI `10.1145/2872362.2872404`); `Flashix` (IEEE TSE 2020);
     `mars-research/atmosphere` (DOI `10.1145/3600006.3613148`);
     `vmware/splinterdb` (USENIX ATC 2020); `facebook/rocksdb`.
   - **Domain 3:** `uwplse/verdi` & `uwplse/verdi-raft` (DOI
     `10.1145/2737924.2737958`, `10.1145/2854065.2854081`);
     `microsoft/Ironclad` (`IronFleet`, DOI `10.1145/2815400.2815428`);
     `kenmcmil/ivy` (DOI `10.1145/2908080.2908118`); `logsem/aneris` (DOI
     `10.1007/978-3-030-44914-8_14`); `mit-pdos/chapar` (DOI
     `10.1145/2837614.2837622`); `kevin-dp/VeriFx`; `Isabelle AFP: CRDT` (DOI
     `10.1145/3133933`); `tlaplus/tlapm` (`TLAPS`, DOI
     `10.1007/978-3-642-32759-9_14`); `apple/foundationdb` (DOI
     `10.1145/3448016.3457559`); `jepsen-io/jepsen` & `jepsen-io/elle` (DOI
     `10.14778/3430915.3430918`).
   - **Domain 4:** `batfish/batfish` & `Minesweeper` (DOI
     `10.1145/3098822.3098828`); `uwplse/bagpipe` (DOI `10.1145/2983990.2984012`);
     `frenetic-lang/netkat` & `KATch` (DOI `10.1145/2535838.2535862`,
     `10.1145/3656436`); `p4v` (DOI `10.1145/3230543.3230582`); `Vera` (DOI
     `10.1145/3230543.3230548`); `cornell-netlab/petr4` (DOI `10.1145/3434301`);
     `verified-network-toolchain/poulet4`; `p4gauntlet/gauntlet` (OSDI 2020);
     `XJTU-NetVerify/apkeep` (NSDI 2020), `VeriFlow` (NSDI 2013), `HSA` (NSDI
     2012); `NetworkVerification/nv` (PLDI 2020), `ShapeShifter` (PLDI 2019),
     and `Timepiece` (PLDI 2023).
   - **Domain 5:** `anvil-verifier/anvil` (OSDI 2024); `sieve-project/sieve`
     (OSDI 2022); `K8s-TLA+`; `Terraform Sentinel`, `open-policy-agent/conftest`,
     `bridgecrewio/checkov`; `Tiros` (DOI `10.1007/978-3-030-25543-5_14`);
     `plasma-umass/rehearsal` (DOI `10.1145/2908080.2908122`).
   - **Domain 6:** `cedar-policy/cedar` & `cedar-policy/cedar-spec` (DOI
     `10.1145/3649835`); `Zelkova` (DOI `10.23919/FMCAD.2018.8603013`);
     `Margrave` (DOI `10.1145/1062455.1062502`); `Zanzibar` (USENIX ATC 2019),
     `authzed/spicedb`, `openfga/openfga`; `open-policy-agent/opa`;
     `opendp/opendp`; `uvm-plaid/chorus`; `Fuzz` (ICFP 2010), `DFuzz` (POPL
     2013), `LightDP` (POPL 2017); `CertiPriv` & `EasyCrypt/easycrypt` (DOI
     `10.1145/2103656.2103670`).
   - **Domain 7:** `snowleopard/build` (`Build Systems à la Carte`, DOI
     `10.1145/3236774`, `10.1017/S0956796820000088`); `pluto-build/pluto` (DOI
     `10.1145/2814270.2814277`); `salsa-rs/salsa`; `facebook/buck2` (`DICE`);
     `adapton/adapton.rust` (DOI `10.1145/2594291.2594324`);
     `bazelbuild/bazel` (`Skyframe`) & `bazelbuild/remote-apis` (`REAPI`);
     `pubgrub-rs/pubgrub`.
   - **Domain 8:** `llvm/mlir-tv` & `AliveToolkit/alive2` (DOI
     `10.1145/3453483.3454030`); `halide/Halide` & `verified-halide` (DOI
     `10.1145/3563321`); `exo-lang/exo` (DOI `10.1145/3519939.3523446`);
     `XLA GSPMD` (arXiv `2105.04663`), `PartIR`, & `openxla/shardy`;
     `llvm/llvm-project/polly` & `isl`; `imperial/gpuverify` (DOI
     `10.1145/2384616.2384625`) & `umb-svl/faial` (DOI
     `10.1007/978-3-030-81685-8_19`); `uwplse/tensat` (MLSys 2021) &
     `mirage-project/mirage` (OSDI 2025, arXiv `2405.05751`).
   - **Domain 9:** `TimelyDataflow/timely-dataflow` (DOI
     `10.1145/2517349.2522738`); `StreamBox` (USENIX ATC 2017); `Flink ABS`
     (arXiv `1506.08603`); `Coqlex/coqlex` (arXiv `2301.10479`) & `VeriLex`;
     `Isabelle AFP: Posix-Lexing` (DOI `10.1007/978-3-319-43144-4_5`) &
     `pandaman64/lean-regex`; `slasser/CoStar` (DOI `10.1145/3453483.3454053`)
     & `TRX` (DOI `10.2168/LMCS-7(2:18)2011`).
   - **Domain 10:** `project-everest/everparse` (USENIX Security 2019);
     `Narcissus` (DOI `10.1145/3290389`); `secure-foundations/vest` (USENIX
     Security 2025) & `google/zerocopy`; `inkandswitch/cambria-project` &
     `boomerang-lang/boomerang` (DOI `10.1145/1328438.1328487`); `bufbuild/buf`;
     `temporalio/temporal` & `restatedev/restate`; `p-org/P` (DOI
     `10.1145/2491956.2462184`).

## Revalidation

To revalidate the structural mappings and Anneal primitive correspondences in
this report after changes to `trusted/lean/` or the `reference` hardening
packages:

1. **Check the Anneal trusted core definitions (`Trusted/Refinement.lean` and
   `Trusted/StepResult.lean`):**
   Diff `trusted/lean/Trusted/Refinement.lean` and
   `trusted/lean/Trusted/StepResult.lean` against
   `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` to confirm that
   `Partial`, `Language`, `Compiles`, `Abstracts`, `VerificationResultOn`,
   `StepResult`, `ReachesPrefix`, and `BehaviorOf` retain their definitions and
   polarity.
2. **Rerun the mechanized Lean 4 support modules in the sibling hardening
   reports (`google/zerocopy@df55c524a051d59e7dd35564f282b30d29133392`):**
   Execute the Lean 4.34.1 kernel checks on:
   - `reports/anneal-behavior-codec-and-progress-refinement-2026/support/BehaviorCodecExpressiveness.lean`
     (verifying `PartialBehaviorCodec`, `EventualBehaviorOf`, and
     `eventual_wellFormed_iff_prefix_wellFormed`),
   - `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/support/StructuralExternalCallAndCanaries.lean`
     (verifying `StepResult.externalCall` and `open_world_callback_composition_sound`),
     and
   - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/support/ProofGatedCompilationAndTrustPolicy.lean`
     (verifying `ScopedVerificationResult` and `BoundaryCodec`).
3. **Validate the report package metadata and structure:**
   Run `python3 tools/reference.py check` from the root of the `reference`
   worktree.
