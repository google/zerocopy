<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Historical Verification, Miscompilation, and Operational Failures Across Databases, Storage, Distributed Systems, Networking, Authorization, Build Systems, and Tensor Compilers

## Summary

Across eight non-traditional systems domains—relational query optimizers and
incremental view maintenance (SQL/DBSP), crash-consistent storage engines,
distributed consensus and transaction protocols, Kubernetes reconciliation
controllers, programmable network data/control planes (P4/BGP), cloud
authorization and differential privacy engines (`Cedar`/`OpenDP`), hermetic and
incremental build systems (`Bazel`/`Ninja`/`Salsa`), and deep-learning tensor
compilers (`XLA`/`TVM`/`Triton`/`Halide`)—historical postmortems, differential
fuzzing campaigns, and formal verification errata reveal that severe bugs
rarely arise from isolated arithmetic mistakes inside already-verified pure
kernels. Instead, historical failures cluster around four structural seams at
the boundary between specification, lowering, environment interaction, and
partial verification:

1. **Silent semantic drift across three-valued partiality, multiset
   multiplicity, and representation decoding (`Language SemObs`, `Partial`, and
   `BehaviorCodec`):**
   - In relational databases (`PostgreSQL`, `MySQL`, `CockroachDB`, `SQLite`,
     `TiDB`, `Apache Calcite`, `Spark SQL`), `SQLancer`'s Ternary Logic
     Partitioning (`TLP`, OOPSLA 2020) and Non-Optimizing Reference Engine
     Construction (`NoREC`, ESEC/FSE 2020) uncovered hundreds of silent
     wrong-result bugs where query rewrite passes conflated Kleene three-valued
     `UNKNOWN` (`NULL`) with boolean `FALSE`, dropped duplicate rows under bag
     semantics, or pushed unguarded division/cast expressions below filters.
     Similarly, early SQL equivalence provers (`Cosette`, CIDR/PLDI 2017; `UDP`,
     VLDB 2018) hit expressiveness boundaries on `NULL` three-valued semantics,
     outer joins, and window functions while exposing classic `COUNT(*)`
     empty-group aggregation bugs (such as the Kim 1982 nested-query rewrite
     bug).
   - In programmable networks, `Gauntlet` (OSDI 2020) and `Petr4` (POPL 2021)
     uncovered 96 distinct bugs (62 crashes and 34 silent miscompilations) in
     `p4c`, `BMv2`, and the Barefoot Tofino compiler, driven by out-of-order
     side-effect hoisting in match-action table keys and unvalidated header
     validity bits (`isValid()`).
   - In tensor compilers, `Tzer` (ISSTA 2022), `NNSmith` (ASPLOS 2023), and
     production `XLA GSPMD` / `Triton` bug trackers document silent numerical
     corruptions caused by omitted `AllReduce` collectives across sharded device
     meshes, out-of-bounds polyhedral halo loads in `Halide`/`TVM`, and
     shared-memory (`smem`) race conditions under asynchronous GPU barriers
     (`mbarrier`).
   - **Architectural lesson for Anneal:** Separating `defined : Prop` from
     `Partial.ub` (`Trusted/Refinement.lean`) and anchoring `BehaviorCodec` with
     `Option`-valued outcome decoding (`decodeOut : L₂.Out → Option L₁.Out`) and
     semantic spine preservation (`obs_decodeOut : L₂.obs o₂ = L₁.obs o₁`)
     prevents optimizers from introducing new traps on dead paths, erasing
     multiset multiplicities, reading invalid P4 header bits, or leaving TPU/GPU
     mesh shards unreduced (`decodeOut = none`).

2. **Degenerate "vacuous safety" implementations and non-terminating control
   loops (`ProductiveOn`, `InhabitedPre`, and `EventualBehaviorOf`):**
   - A transaction manager that aborts 100% of transactions trivially satisfies
     Strict Serializability; a firewall compiler that emits `DROP ALL` trivially
     satisfies tenant isolation; an authorization residual filter that returns
     `Deny` on every row trivially prevents data leaks; a streaming engine
     (`Apache Flink`) that holds watermarks at $-\infty$ forever never emits
     wrong window aggregates; and a Kubernetes operator that returns
     `RequeueAfter(∞)` never performs an unsafe state transition.
   - Conversely, systems that perform variable-step ($1 \to k$) convergence can
     diverge into permanent oscillation or exponential backtracking: BGP route
     reflection combined with Multi-Exit Discriminator (`MED`) attributes forms
     Griffin-Shepherd-Wilf *Dispute Wheels* that oscillate forever (`RFC 3345`);
     competing Kubernetes operators enter infinite reconciliation livelocks
     (`Sieve`, OSDI 2022; `Anvil`, OSDI 2024); `Salsa` incremental query engines
     in `rust-analyzer` panic on dynamically formed dependency cycles; and
     backtracking NFA regex engines caused global production outages at
     `Stack Overflow` (July 20, 2016; 34 minutes) and `Cloudflare` (July 2,
     2019; 27 minutes, 82% global traffic drop) via $O(2^N)$ catastrophic
     backtracking (`ReDoS`).
   - **Architectural lesson for Anneal:** Pairing `InhabitedPre` and
     `ProductiveOn` with fuel-internalized `EventualBehaviorOf`
     (`anneal-behavior-codec-and-progress-refinement-2026`) forces positive
     progress on valid inputs, verifies both all-prefix intermediate safety
     (`∀ n <= k, isSafe`) and finite-step convergence (`.terminated`), and
     refutes non-terminating BGP Dispute Wheels, Kubernetes livelocks, and
     unbounded backtracking without requiring coinduction or `Classical.choice`.

3. **Unchecked environment boundaries, stale caches, and hardware reorderings
   (`StepResult.externalCall`):**
   - Verified storage systems (`FSCQ`, SOSP 2015; `Yggdrasil`, OSDI 2016)
     experienced real bugs in their unverified FUSE/C shims and relied on disk
     barrier models where omitting a Force Unit Access (`FUA`) or `fsync`
     barrier before overwriting metadata causes power-loss corruption; in LSM
     storage engines (`RocksDB` `DeleteRange` issues `#4747`, `#4760`, `#5616`,
     `#7703`), compacting and dropping a range tombstone above an active
     snapshot or lower SSTable level resurrects deleted keys.
   - In Kubernetes controllers, reading from a lagging local informer cache
     creates time-of-check-to-time-of-use (`TOCTOU`) races (`Sieve` OSDI 2022;
     `Anvil` OSDI 2024) where a controller overwrites newer `etcd` state or
     leaks orphan cloud resources after partial API failures.
   - In differential privacy libraries (`OpenDP`, `Diffprivlib`, `Chorus`),
     implementing real-valued Laplace/Gaussian noise and sum aggregations in
     IEEE-754 floating-point arithmetic without boundary rounding/sensitivity
     guards enabled Mironov's least-significant-bit (`LSB`) reconstruction
     attack (CCS 2012) and Casacuberta et al.'s widespread sensitivity
     underestimation attacks (CCS 2022).
   - In build systems (`Bazel`, `Ninja`), spawning a compiler subprocess whose
     sandbox mounts header files or environment variables omitted from the
     content-addressed `ActionKey` digest causes persistent remote cache
     poisoning.
   - **Architectural lesson for Anneal:** Modeling every I/O, RPC, cache read,
     CSPRNG sample, and subprocess spawn via `StepResult.externalCall
     (boundaryInv : Bool) (branches : State → Obs → Prop)`
     (`anneal-structural-external-calls-and-tcb-mutation-testing-2026`) checks
     caller-side boundary invariants (`flushedLSN >= pageLSN`,
     `tombstone.seq <= earliest_snapshot`, `resourceVersion` preconditions,
     `sandboxMounts ⊆ hashedInputs`, and discrete DP budget/sensitivity bounds)
     before exposing execution to demonic environment nondeterminism.

4. **Pointwise contradiction and partial-waiver contamination
   (`VerificationResult`, `ScopedVerificationResult`, and `TrustPolicy`):**
   - When a complex system (such as a 150-rule SQL optimizer, a multi-pass ML
     compiler waiving IEEE-754 reassociation in `AllReduce`, or an incremental
     build system waiving SHA-256 collision resistance) waives an unproven rule
     by placing a concrete assumption on the left-hand side of an implication
     (`→`), any edge-case bug in the waived rule makes the antecedent `False`
     and discharges every other obligation in the system by `False.elim`.
   - **Architectural lesson for Anneal:** Positive per-obligation consequent
     masking (`ob.id ∈ waived ∨ ob.prop` in `ScopedVerificationResult`, combined
     with universal `TCBModel` quantification in
     `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`)
     isolates waived rules, hardware assumptions, and external solver steps so a
     bug in an unverified rule can never silently certify an adjacent pass.

## Applicability

This report synthesizes primary-source evidence from the eight subject groups in
`REPORT.json` and maps their failure modes onto Anneal's trusted verification
primitives:

| Subject Group | Primary Sources & Coordinates | Examined Scope |
| :--- | :--- | :--- |
| **Anneal Trusted Core & Extensions** | `joshlf/anneal` at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` (`trusted-core`) and `4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`), plus companion 2026 reference reports | `Language`, `Partial`, `BehaviorCodec`, `PartialBehaviorCodec`, `Compiles`, `Abstracts`, `ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, `StepResult.externalCall`, `VerificationResult`, `ScopedVerificationResult`, `TrustPolicy` |
| **SQL Optimizers & `SQLancer`** | Rigger & Su: `NoREC` (`10.1145/3368089.3409710`, ESEC/FSE 2020), `TLP` (`10.1145/3428279`, OOPSLA 2020), `PQS` (OSDI 2020); `sqlancer/sqlancer` | Silent wrong-result bugs in `PostgreSQL`, `MySQL`, `CockroachDB`, `SQLite`, and `TiDB` involving Kleene 3VL `NULL`, joins, predicates, and aggregates |
| **SQL Equivalence & IVM (`Cosette`, `UDP`, `WeTune`, `DBSP`)** | Chu et al. `Cosette` (CIDR/PLDI 2017) & `UDP` (`10.14778/3192965.3192971`, VLDB 2018); Wang et al. `WeTune` (`10.1145/3514221.3526125`, SIGMOD 2022); Budiu et al. `DBSP` (`10.14778/3587136.3587137`, VLDB 2023) | Automated SQL rewrite verification boundaries, `COUNT` / bag-vs-set bugs, correlated subquery unnesting, and streaming $\mathbb{Z}$-set / watermark retractions in `Materialize` and `Apache Flink` |
| **Storage & Consensus (`FSCQ`, `Yggdrasil`, `RocksDB`, `Jepsen`/`Elle`)** | Chen et al. `FSCQ` (`10.1145/2815400.2815402`, SOSP 2015); Sigurbjarnarson et al. `Yggdrasil` (OSDI 2016); `facebook/rocksdb` `DeleteRange`; Kingsbury & Alvaro `Elle` (`10.14778/3457390.3457396`, VLDB 2020); Ongaro `Raft` (ATC 2014 / PhD 2014) | Unverified C/FUSE shims, disk barrier reorderings, LSM range-tombstone compaction drops, Raft Figure 8 & membership-change bugs, and distributed isolation anomalies in `CockroachDB`, `TiKV`, and `MongoDB` |
| **Kubernetes Controllers (`Sieve`, `Anvil`)** | Sun et al. `Sieve` (OSDI 2022); Sun et al. `Anvil` (OSDI 2024) | Stale informer-cache TOCTOU races, non-idempotent API retries, orphan resource leaks, and reconciliation livelocks in Kubernetes operators |
| **Networking (`Gauntlet`, `Petr4`, `BGP RFC 3345`)** | Ruffy et al. `Gauntlet` (`arXiv:2006.01074`, OSDI 2020); Doenges et al. `Petr4` (`10.1145/3434304`, POPL 2021); Griffin, Shepherd & Wilf (ICNP/SIGCOMM 1999); McPherson et al. `RFC 3345` (2002) | 96 compiler/semantic bugs in `p4c`, `BMv2`, and Barefoot Tofino; P4-16 specification undefined behaviors; BGP route-reflection / MED Dispute Wheel oscillations |
| **Cloud IAM & Differential Privacy (`Cedar`, `Mironov`, `Casacuberta`)** | Cutler et al. `Cedar` (`arXiv:2403.04651`, OOPSLA 2024); Mironov (`10.1145/2382196.2382264`, CCS 2012); Casacuberta et al. (`10.1145/3548606.3560708`, CCS 2022) | Pre-release validator and evaluator bugs caught by Lean 4 proofs and DRT in AWS `Cedar`; IEEE-754 LSB and sensitivity-underestimation attacks in `OpenDP`, `Diffprivlib`, and `Chorus` |
| **Build Systems, Tensor Compilers & `ReDoS`** | Erdweg et al. `Pluto` (`10.1145/2814270.2814316`, OOPSLA 2015); Mokhov et al. `Build Systems à la Carte` (`10.1145/3236774`, ICFP 2018); Liu et al. `Tzer` (`10.1145/3533767.3534388`, ISSTA 2022) & `NNSmith` (`10.1145/3575693.3575707`, ASPLOS 2023); `Cloudflare` (2019) & `Stack Overflow` (2016) postmortems | Dynamic dependency and remote-cache poisoning in `Bazel`/`Ninja`/`Salsa`; miscompilations in `XLA GSPMD`, `Triton`, `TVM`, and `Halide`; catastrophic regex backtracking outages |

The architectural mappings in this report apply whenever Anneal's `trusted/lean/`
primitives are used to verify domain-specific compilers, query optimizers,
storage engines, distributed controllers, policy evaluators, or incremental
build systems, as well as to Anneal's own Rust/Lean compilation and caching
infrastructure.

## Findings

### 1. SQL Query Optimizer, Equivalence Prover, and Incremental View Maintenance Failures

`Basis: documentation + source + derived`

#### 1.1 Three-Valued Kleene `NULL` Logic (`UNKNOWN`) and Query-Partitioning Failures (`SQLancer` across `PostgreSQL`, `MySQL`, `CockroachDB`, `SQLite`, and `TiDB`)

In standard SQL (ISO/IEC 9075), predicates evaluate in Kleene three-valued logic
(`TRUE`, `FALSE`, `UNKNOWN`, where `NULL` acts as `UNKNOWN`). While `WHERE p`
and `INNER JOIN ... ON p` retain only rows where `p` evaluates to `TRUE`
(collapsing `FALSE` and `UNKNOWN`), `NOT p`, `CASE WHEN`, `LEFT/RIGHT/FULL
OUTER JOIN`, `NOT IN`, and `HAVING` treat `UNKNOWN` and `FALSE` asymmetrically
($\neg \text{UNKNOWN} = \text{UNKNOWN}$).

Manuel Rigger and Zhendong Su exposed the systemic fragility of industrial query
optimizers under three-valued logic through three metamorphic and differential
testing oracles in `SQLancer`:

- **Ternary Logic Partitioning (`TLP`, OOPSLA 2020, `10.1145/3428279`):** For
  any query $Q$ and predicate $p$, `TLP` partitions $Q$ into three sub-queries
  filtered by `WHERE p`, `WHERE NOT (p)`, and `WHERE (p) IS NULL`. By the law of
  excluded fourth in Kleene logic, the multiset union (or aggregate combination)
  of the three partitioned queries must equal $Q$.
- **Non-Optimizing Reference Engine Construction (`NoREC`, ESEC/FSE 2020,
  `10.1145/3368089.3409710`):** Rewrites an optimizable query `SELECT * FROM T
  WHERE p` (which triggers index selection, predicate pushdown, and join
  reordering) into an unoptimizable projection `SELECT (p) IS TRUE FROM T` and
  counts matching rows.
- **Pivoted Query Synthesis (`PQS`, OSDI 2020):** Selects a concrete database
  row $r_{\text{pivot}}$ (including `NULL` columns), synthesizes complex AST
  predicates guaranteed to evaluate to `TRUE` on $r_{\text{pivot}}$ under
  three-valued rules, and verifies that the engine returns $r_{\text{pivot}}$.

Across `SQLite`, `MySQL`, `PostgreSQL`, `CockroachDB`, and `TiDB`, `SQLancer`
found **over 350 previously unknown logic bugs** (175 in `TLP`, 159 in `NoREC`,
and 99 in `PQS`). Representative root causes include:

1. **Pushing predicates past `OUTER JOIN` null-extension (`PostgreSQL`,
   `MySQL`, `CockroachDB`):** When `LEFT JOIN` fails to match a right-hand row,
   it synthesizes `NULL` columns. If an upper filter $p(R.b)$ is **not
   null-rejecting** (for example, `R.b IS NULL`, `COALESCE(R.b, 0) = 0`, or
   `NOT (R.b = 1 AND FALSE)`), pushing $p$ into the `LEFT JOIN` condition or
   converting the `LEFT JOIN` into an `INNER JOIN` alters the output multiset:
   either the join drops the left row entirely (wrongly converting `LEFT JOIN`
   to `INNER JOIN`), or pushing $p$ into the `ON` clause causes the `LEFT JOIN`
   to emit a null-extended row that the post-join `WHERE` would have filtered or
   vice versa.
2. **Short-circuit boolean/algebraic rewrites unsound on `NULL` (`MySQL`,
   `CockroachDB`, `TiDB`):** Rewriting `x = x` to `TRUE` (unsound when `x IS
   NULL`, where `NULL = NULL` is `UNKNOWN`), rewriting `x NOT IN (y₁, y₂)` via
   De Morgan's law without preserving `UNKNOWN` propagation when any $y_i$ is
   `NULL` (`x <> y₁ AND x <> y₂` evaluates to `UNKNOWN`, not `TRUE`, if $y_2$
   is `NULL`), or simplifying `NOT (a AND b)` using two-valued boolean complements
   in range-index scan builders (`CockroachDB` `optgen` constraint-propagation
   rules).
3. **Partial-index and generated-column `NULL` equivalence mismatches (`SQLite`,
   `PostgreSQL`, `MySQL`):** Using `IS NOT DISTINCT FROM` (where `NULL` equals
   `NULL`) vs. `=` (where `NULL = NULL` is `UNKNOWN`) when matching query
   predicates against partial-index conditions or `UNIQUE` constraints (where
   SQL standard allows multiple `NULL` keys unless `NULLS NOT DISTINCT` is
   specified).

#### 1.2 Bag (Multiset) vs. Set Duplicate Semantics and `COUNT(*)` Empty-Group Bugs (`Cosette`, `UDP`, `WeTune`)

Relational algebra in textbooks is typically defined over **sets** ($R \subseteq
\text{Tuple}$), where idempotence ($R \cup R = R$) and join-projection pushdown
hold unconditionally. Real SQL engines execute over **bags (multisets)** ($R :
\text{Tuple} \to \mathbb{N}$), where every tuple carries a non-negative integer
multiplicity.

When Shumo Chu, Konstantin Weitz, Chenglong Wang, Alvin Cheung, and Dan Suciu
developed `Cosette` (CIDR 2017 / PLDI 2017, built on Rosette and Coq/`HoTTSQL`)
and `UDP` (VLDB 2018, `10.14778/3192965.3192971`, modeling queries as symbolic
semiring/U-expressions over $\mathbb{N}$), and when Zhaoguo Wang et al. built
`WeTune` (SIGMOD 2022, `10.1145/3514221.3526125`), their verification campaigns
highlighted both historical optimizer bugs and hard boundaries in early automated
SQL verifiers:

1. **The Kim (1982) `COUNT` Bug and Empty-Group Aggregation Distortion:**
   Won Kim's classic 1982 paper *"On Optimizing an SQL-like Nested Query"*
   proposed unnesting a correlated `SELECT ... FROM R WHERE R.a = (SELECT
   COUNT(S.b) FROM S WHERE S.c = R.c)` into a `GROUP BY` subquery joined with
   `R` via an inner join. As `Cosette` and `HoTTSQL` mechanized in Coq, this
   rewrite is **unsound whenever a group is empty**: for an $r \in R$ with no
   matching rows in $S$, the correlated subquery returns `COUNT(S.b) = 0` (so if
   `r.a = 0`, $r$ must be returned), whereas `SELECT c, COUNT(b) FROM S GROUP
   BY c` produces **zero rows** for that `c`, causing the unnested join to drop
   $r$! Even replacing `INNER JOIN` with `LEFT OUTER JOIN` fails if `COUNT` is
   evaluated after the outer join as `COUNT(*)` (which counts the single
   null-padded outer-join row and returns `1` instead of `0`) rather than
   `COUNT(S.b)` on a non-nullable column of $S$.
2. **Bag Multiplicity Inflation/Deflation in Semi-Join and Pushdown Rewrites
   (`Apache Calcite`, `Spark SQL`, `MySQL`):**
   Rewriting `SELECT R.* FROM R WHERE EXISTS (SELECT 1 FROM S WHERE R.k = S.k)`
   into `SELECT R.* FROM R INNER JOIN S ON R.k = S.k` is sound only if `S.k` is
   guaranteed to be unique (`UNIQUE NOT NULL`); without a uniqueness constraint,
   multiple matching rows in $S$ multiply the multiplicity of $R$'s rows in the
   output bag. Conversely, pushing `DISTINCT` below a union or join—or eliminating
   a self-join `R JOIN R ON R.k = R.k` when `R.k` is not a primary key—silently
   changes tuple multiplicities from $m^2$ to $m$. `WeTune` (SIGMOD 2022) showed
   that verifying rewrite rules requires explicit SMT constraints over uniqueness,
   not-null, and foreign-key invariants; omitting any of those preconditions in
   `Apache Calcite` or `Spark Catalyst` causes silent duplicate corruption.
3. **Early Verifier Expressiveness Boundaries (`Cosette` & `UDP`):**
   Early versions of `Cosette` and `UDP` themselves exhibited instructive
   verification boundaries: `HoTTSQL`/`Cosette` initially modeled `NULL`-free set
   and bag fragments using homotopy type theory / univalent relations, struggling
   to decide three-valued `NULL` predicates combined with arithmetic or
   correlated outer joins; `UDP` relied on canonicalizing U-expressions ($\sum_t
   \llbracket P(t) \rrbracket$) via syntactic isomorphism and SMT over linear
   integer arithmetic, which could not decide equivalence of queries involving
   non-linear aggregations, `ORDER BY ... LIMIT` tie-breaking, or stateful window
   functions (`ROW_NUMBER() OVER (PARTITION BY ...)`).

#### 1.3 Correlated Subquery Decorrelation (`Apply` Unnesting) and Guard-Ordering Traps

Modern analytical optimizers (`PostgreSQL`, `CockroachDB`, `DuckDB`, `HyPer`,
`Spark SQL`) rely on general subquery decorrelation algorithms (most notably
Thomas Neumann and Alfons Kemper's *"Unnesting Arbitrary Queries"*, BTW 2015)
that push a dependent join (`Apply` operator $\bowtie_{\text{dep}}$) down the
query plan tree using a duplicate-eliminated domain projection $D =
\Pi_{\text{corr}}(L)$.

Two recurring bug classes affect decorrelation and predicate pushdown in
production engines:

1. **Domain-Projection Nullability and Lateral Correlation Mismatches:**
   When pushing $D$ through a `LEFT OUTER JOIN` or `FULL OUTER JOIN` on the
   correlated side, the identity $L \bowtie_{\text{dep}} (T_1 \ T_2) = (L
   \bowtie_{\text{dep}} T_1) \ (D \bowtie_{\text{dep}} T_2)$ requires joining on
   `IS NOT DISTINCT FROM` (`<=>`) over the correlation attributes of $D$. Using
   ordinary equality `=` drops correlation bindings whenever a correlation
   attribute in $L$ is `NULL`, causing correlated rows with `NULL` keys to lose
   their right-hand matches.
2. **Guard-Ordering and Introduced Runtime Exceptions (`Division-by-Zero` /
   `CAST` Traps):**
   In SQL, a query such as `SELECT 100 / x FROM (SELECT x FROM T WHERE x <> 0)
   WHERE 100 / x > 5` is well-defined because the inner filter `x <> 0` guards
   the division `100 / x`. When a cost-based optimizer merges subqueries and
   reorders predicates by selectivity—or when decorrelation evaluates the inner
   plan over a superset domain before applying outer filters—evaluating `100 / x
   > 5` or `CAST(str_col AS INT) > 10` before the guard predicate `x <> 0` or
   `is_numeric(str_col)` triggers a runtime `.divByZero` or `.invalidTextRepresentation`
   abort on rows that the unoptimized query never evaluated (`PostgreSQL` planner
   predicate-ordering hazard; `Spark SQL` / `Calcite` filter-pushdown bugs).

#### 1.4 Incremental View Maintenance (`DBSP`, `Materialize`, `Apache Flink`) Retraction Drift and Watermark Bugs

Incremental View Maintenance (`IVM`) and streaming SQL engines (`Materialize`,
`Feldera` / `DBSP` VLDB 2023 `10.14778/3587136.3587137`, and `Apache Flink`
Table/SQL) compile a relational query $Q(I)$ into a stateful streaming dataflow
graph $Q^\Delta(\Delta I)$ over $\mathbb{Z}$-sets (multisets where each tuple
carries a signed integer weight $w \in \mathbb{Z}$: $+1$ for insertion, $-1$ for
retraction/deletion).

Historical bugs in `Apache Flink` and differential/incremental dataflow systems
fall into three distinct mechanisms:

1. **Missing or Asymmetric Retraction Propagation (`Flink` Upsert/Retract Stream
   Bugs, e.g., `FLINK-9528`, `FLINK-17093`, `FLINK-20374`):**
   In `Apache Flink`'s Blink/Table planner, operators communicate via append-only,
   retract (`+I`, `-U`, `+U`, `-D` changelog kinds), or upsert streams. When a
   non-monotonic operator (such as `GROUP BY` aggregation followed by a `JOIN`,
   `OVER` window, or `ROW_NUMBER() <= k` Top-$N$ rank filter) updates an existing
   key's value, it emits a retraction `-U(old_row)` followed by `+U(new_row)`.
   Bugs in changelog mode inference (`ModifyKindSetTrait` / `UpdateKindTrait`)
   or sink materialization (`SinkUpsertMaterializer`) caused downstream operators
   to drop `-U` retractions, process `+U` before `-U` across hash-partitioned
   channels with different key sharding, or fail to retract previous Top-$N$
   winners, leaving phantom rows permanently materialized in the output view.
2. **Non-Linear / Non-Associative Aggregate State Drift Under Retractions
   (`Materialize` / `DBSP` / `Flink`):**
   For linear group-by aggregates like `COUNT` and integer `SUM`, maintaining a
   $\mathbb{Z}$-set state is an exact ring homomorphism ($\sum (w_i \cdot v_i)$).
   However, for **`MIN` / `MAX`** (which are semilattice operations without
   additive inverses!) or **floating-point `SUM(float8)`**, retracting the
   current minimum value requires maintaining the full ordered multiset of values
   in the group (creating $O(N)$ state amplification unless garbage-collected),
   and retracting floating-point values via subtraction $(S + x) - x$ accumulates
   catastrophic IEEE-754 cancellation drift so that after a burst of insertions
   followed by retracting every row back to the empty table, the materialized
   view outputs a non-zero residual (`1.42e-14`) instead of `0.0` (or fails to
   delete the empty group).
3. **Premature Watermark Advancement and State Garbage-Collection Drops (`Flink`
   / `Timely Dataflow`):**
   In event-time streaming, a watermark $W(t)$ asserts that no future input
   records carry timestamp $t' \le W(t)$. In `Apache Flink`, when a multi-input
   operator (such as `IntervalJoin` or `WindowOperator`) computes its output
   watermark as $\min(W_{\text{left}}, W_{\text{right}})$, bugs in idle-partition
   watermark alignment (`WatermarkStatus.IDLE`) or asynchronous Chandy-Lamport
   checkpoint recovery caused one input's watermark to jump ahead while buffered
   records from the other input were still in flight. Once the watermark crossed
   the window's cleanup timer (`window.maxTimestamp() + allowedLateness`), the
   operator fired the incomplete window and purged its `RocksDBStateBackend`
   entries, silently dropping all remaining valid in-flight events.

#### 1.5 Architectural Lessons for Anneal's Four `trusted/` Primitives in Relational and Streaming Engines

Each of the SQL and IVM failure classes above maps directly onto a specific invariant
in Anneal's four `trusted/lean/` primitives:

- **Primitive 1 (`Language SemObs` & `Partial`):**
  - **Guarding against introduced runtime exceptions (`100 / x` pushdown):** In
    Anneal's `Partial`, `defined = False` (`Partial.ub`) sits at the top of the
    refinement order ($\top$). If `L_Rel` models runtime data traps (division by
    zero, invalid `CAST`, regex compile errors) either as `defined = False` or
    as an explicit `.aborted err` variant in `SemObs` (`obs : Out → SemObs`),
    then `Compiles` ($L_{\text{Phys}}.\text{sem}(P) \le \pi(L_{\text{Rel}}.\text{sem}(Q))$)
    **categorically forbids** a predicate-pushdown or decorrelation pass from
    turning a query that succeeds (`defined = True`, `.committed rows`) into a
    plan that traps (`.aborted .divByZero` or `Partial.ub`).
  - **Three-valued Kleene logic in `SemObs`:** Defining `Query` over nullable
    tuples (`Option Val`) and three-valued evaluation (`KleeneBool : .true |
    .false | .unknown`) inside `L_Rel.sem` makes `TLP` (Ternary Logic
    Partitioning) a theorem of the semantic model rather than an ad-hoc fuzzer
    oracle: any rewrite rule sound under `Compiles` must preserve `SemObs` on
    all `NULL` combinations, automatically rejecting `x = x ↦ TRUE` and
    non-null-rejecting outer-join pushdowns.
- **Primitive 2 (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`, &
  `Abstracts`):**
  - **Bag multiplicity and empty-group preservation via `obs_decodeOut`:** By
    fixing `SemObs` to the exact multiset of output rows (`Multiset Tuple`) and
    requiring `obs_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ =
    L₁.obs o₁`, no physical plan or `egglog` rewrite can alter row multiplicities
    (ruling out unguarded semi-join-to-inner-join rewrites) or drop empty groups
    in Kim-style `COUNT` decorrelation.
  - **DBSP $\Delta$-circuit correctness via stream-codec retraction:** For IVM,
    the `BehaviorCodec` between batch relational semantics $L_{\text{Rel}}$ and
    streaming $\mathbb{Z}$-set semantics $L_{\text{DBSP}}$ defines `encodeQuery`
    by splitting a database history into $\Delta D_t$ steps and `decodeOut` by
    integrating ($\mathcal{I}(\Delta O) = \sum_{t} \Delta O_t$) the emitted
    changelog stream (requiring weights to be non-negative and `+U`/`-U` pairs to
    be balanced; otherwise `decodeOut = none`). `Compiles` then directly proves
    the fundamental DBSP invariant $\mathcal{I}(Q^\Delta(\Delta I)) =
    Q(\mathcal{I}(\Delta I))$ and rejects Flink-style missing retractions!
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`):**
  - **Blocking the "Abort-All / Hold-Watermarks-Forever" loopholes:** A query
    optimizer that compiles complex joins to `.aborted .outOfMemory` or a Flink
    pipeline that holds watermarks at $-\infty$ forever is refuted by
    `ProductiveOn SchemaInv P_phys` + `EventualBehaviorOf`, which requires
    finite-step termination with a valid decoded output (`decodeOut o₂ = some
    o₁`) on all database instances and bounded-lateness streams satisfying
    `SchemaInv` (which itself must be non-empty by `InhabitedPre SchemaInv`).
- **Primitive 4 (`VerificationResult` / `ScopedVerificationResult` &
  `TrustPolicy`):**
  - In a rule-based optimizer (`Apache Calcite`, `CockroachDB` `optgen`, or an
    `egglog` equality-saturation certifier) applying a chain of rewrite steps
    $P_0 \to P_1 \to \dots \to P_m$, positive per-obligation scoping (`ob.id ∈
    waived ∨ ob.prop`) allows verified core relational/Kleene rules to run at
    `waived = []` while explicitly isolating any unverified vendor UDF rule or
    floating-point `SUM` reassociation waiver (`waived := [.fpSumReassoc]`)
    without contaminating the soundness of the surrounding join/decorrelation
    plan.

### 2. Storage Engines, Distributed Consensus, and Kubernetes Controller Failures

`Basis: normative + documentation + source + derived`

#### 2.1 Verified Storage Boundary Gaps: Unverified FUSE/C Shims and Volatile Disk Write-Cache Reordering (`FSCQ`, `Yggdrasil`, `Perennial`)

Even landmark formally verified file systems have suffered bugs at the boundary
between their mechanized proof models and the unverified host/hardware
environment:

1. **`FSCQ` (SOSP 2015, `10.1145/2815400.2815402`) and `Perennial` / `GoJournal`
   (SOSP 2019 / OSDI 2020) Unverified Shim and Extraction Seams:**
   `FSCQ` mechanized Crash Hoare Logic (`CHL`) in Coq and extracted the verified
   Coq specification to Haskell, executing in user space on top of a `FUSE` C/Haskell
   binding layer and raw block device I/O wrapper. Subsequent analysis by the MIT
   PDOS group (during `DFSCQ` SOSP 2017 and `Perennial` SOSP 2019) identified
   concrete defects along this boundary:
   - **Haskell integer/buffer marshaling and FUSE protocol assumptions:** In
     `FSCQ`, the unverified Haskell FUSE driver and block-device syscall layer
     initially contained bugs in multi-block write offset calculations and error-code
     translations, and because Coq extraction erased static type proofs before the
     unverified Haskell/C FUSE glue executed, a mismatch in how `stat` / `rename`
     flags were unpacked could bypass the Coq theorem's preconditions.
   - **Asynchronous disk write-back vs. barrier modeling:** Early crash models
     assumed synchronous sector writes enhanced with explicit `flush` barriers.
     In `DFSCQ` (SOSP 2017), modeling page-cache write-back asynchronous queues
     revealed that if an application calls `fsync(fd)` on a file whose directory
     entry was newly created, flushing the file's data blocks and inode without
     also flushing the parent directory's log/inode barrier allows a power cut
     to leave an allocated inode unreachable after reboot.
2. **`Yggdrasil` (OSDI 2016) SMT Crash-Refinement and Unverified Cython/FUSE
   Wrapper Gaps:**
   `Yggdrasil` verified crash refinement ($\forall \text{crash}, \text{Recover}(\text{Impl})
   \subseteq \text{Spec}$) for `Yxv6` using Z3 decision procedures over bitvectors
   and arrays, compiling Python/Z3 models via Cython to C. While the Z3
   verification caught subtle bugs in `xv6` (such as freeing a data block in the
   on-disk bitmap before clearing the inode pointer to that block, which allows a
   crash + realloc to cross-link two files to the same physical disk block!),
   `Yggdrasil`'s TCB still trusted: (a) the translation from the Python DSL to
   both Z3 SMT formulas and Cython C code (a dual-emitter seam analogous to
   Anneal's `Mir.lean` vs. `Prog.s` seam), (b) the unverified C FUSE dispatch
   loop, and (c) the hardware assumption that an NVMe/SATA controller honors
   `fdatasync` / `FLUSH CACHE EXT` without silently dropping volatile drive-cache
   writes when `FUA` (Force Unit Access) is disabled.

#### 2.2 LSM-Tree Compaction and Range-Delete Tombstone Resurrection Bugs (`RocksDB` and `PebblesDB`)

Log-Structured Merge-tree (`LSM`) storage engines (`RocksDB`, `PebblesDB` SOSP
2017, `CockroachDB` `Pebble`) do not overwrite or delete keys in place. Instead,
`Delete(k)` appends a point tombstone `(k, seq, kTypeDeletion)` and
`DeleteRange(begin_key, end_key)` appends a range tombstone `[begin_key,
end_key) @ seq` to the active memtable and Write-Ahead Log (`WAL`). Background
**compaction** merges SSTables from level $L_i$ into $L_{i+1}$ and garbage-collects
tombstones only when two invariants simultaneously hold:
1. **Snapshot Visibility Invariant:** The tombstone's sequence number `seq` is
   strictly older than the earliest active MVCC snapshot (`seq <
   earliest_snapshot`); otherwise, an active reader holding `snap_seq < seq`
   could see keys hidden or exposed inconsistently.
2. **Bottommost Level / Lower-Level Disjointness Invariant:** No SSTable in any
   deeper level $L_j$ ($j > i+1$) has key bounds overlapping the tombstone's key
   So long as an older entry `(k, seq_old, kTypeValue)` with `seq_old < seq`
   resides in a deeper level $L_j$, dropping the tombstone at $L_{i+1}$ causes
   subsequent `Get(k)` or `Iterator::Seek(k)` calls to fall through to $L_j$ and
   **resurrect the deleted key**!

Across `facebook/rocksdb`'s production history, violating the interaction between
range tombstones, SSTable boundary clipping, and snapshot sequence numbers
produced a series of severe data-corruption and key-resurrection bugs:

- **Premature Range-Tombstone Dropping Across Snapshots (`facebook/rocksdb#4747`,
  `#4760`, `#5616`):** In `RocksDB` v5.x–v6.x (`RangeDelAggregator` /
  `CompactionIterator`), when a `DeleteRange` tombstone spanned multiple
  snapshots or was fragmented across SSTable file boundaries during compaction,
  `CompactionIterator::PrepareOutput` miscalculated which snapshot stripe a
  fragmented range tombstone belonged to, dropping range tombstones whose `seq`
  was still needed to mask keys at lower levels or violating snapshot isolation
  for concurrent iterators.
- **SSTable Boundary Truncation Bleed and Off-by-One Clipping
  (`facebook/rocksdb#7703`, `#10250`):** When splitting compaction output into
  multiple SSTables at target file-size boundaries, `RocksDB` truncates a spanning
  range tombstone `[a, z) @ seq` at the output SSTable's `largest_key`. Because
  SSTable `largest_key` metadata stores an **internal key** `(user_key, seq,
  type)`, off-by-one sequence-number comparisons at the truncation boundary either
  left a 1-key gap `(user_key, seq_older)` uncovered between adjacent SSTables
  (resurrecting `user_key`) or extended the tombstone to delete a newer version
  `(user_key, seq_newer)` written after the `DeleteRange`!
- **`PebblesDB` Fragmented LSM Guards (SOSP 2017):** `PebblesDB` introduced
  *guards* to partition LSM levels into disjoint key intervals without rewriting
  full levels. However, when guards are inserted dynamically and SSTables are
  lazily split across compaction rounds, failing to propagate range or point
  tombstones into every sub-guard interval that overlaps a deeper uncompacted
  guard resurrects stale values during range scans (`Seek` merging across guard
  iterators).

#### 2.3 Distributed Consensus and Transactional Isolation Failures Under Fault Injection (`Raft`, `CockroachDB`, `TiKV`, `MongoDB` via `Jepsen` and `Elle`)

Distributed consensus engines (`Raft`, `Multi-Paxos`) and distributed
transactional databases (`CockroachDB`, `TiKV`/`TiDB`, `MongoDB`, `etcd`) must
preserve linearizability and transactional isolation across asynchronous network
partitions, leader failovers, and dynamic cluster membership reconfigurations.
Historical verification and `Jepsen`/`Elle` (Kingsbury & Alvaro, VLDB 2020,
`10.14778/3457390.3457396`) investigations exposed four canonical protocol and
implementation failures:

1. **The Raft "Figure 8" Previous-Term Commit Bug (Ongaro & Ousterhout ATC 2014):**
   In `Raft`, if a newly elected leader in term $T$ immediately advances
   `commitIndex` for an uncommitted log entry from an **older term** $T' < T$ as
   soon as that entry is stored on a majority of servers—without first appending
   and replicating at least one entry from its **own current term $T$**—a
   subsequent leader elected in term $T+1$ (whose log has a higher last-entry
   term on a different majority quorum) can overwrite the "committed" entry from
   term $T'$, causing split-brain state-machine divergence. Multiple early Raft
   implementations tested by `Jepsen` omitted the `log[N].term == currentTerm`
   guard on `commitIndex` advancement and lost committed writes under asymmetric
   partitions.
2. **Diego Ongaro's Single-Server Raft Membership-Change Bug (2015 Erratum to
   Ongaro PhD Dissertation §4.1):**
   In his 2014 PhD dissertation, Ongaro proposed simplifying Raft cluster
   reconfiguration from two-phase *Joint Consensus* ($C_{\text{old,new}}$) to
   single-server additions/removals ($C_{\text{old}} \to C_{\text{new}}$
   differing by 1 node), arguing that because any majority of $C_{\text{old}}$
   and $C_{\text{new}}$ overlap on a single change, joint consensus was
   unnecessary. In 2015, Amosjel and Ongaro discovered a **protocol-level
   safety bug** when two single-server membership changes are pipelined or when
   a leader failure occurs mid-change: suppose $C_0 = \{s_1, s_2, s_3\}$. Leader
   $s_1$ appends $C_1 = \{s_1, s_2, s_3, s_4\}$ (not yet committed), then crashes;
   $s_3$ is elected leader in a new term using votes from $\{s_2, s_3\}$ (which
   have not seen $C_1$) and appends $C_2 = \{s_1, s_2, s_3, s_5\}$. Now $C_1$ and
   $C_2$ can have disjoint majorities ($\{s_1, s_2, s_4\}$ vs. $\{s_3, s_5\}$),
   allowing two concurrent leaders unless a new leader is forbidden from
   proposing a configuration change until it has committed a no-op entry in its
   own term! Both `etcd/raft` (`CockroachDB`) and `TiKV` (`tikv/raft-rs`) had to
   adopt explicit joint-consensus quorums and strict `pending_conf_index` guards
   after encountering reconfiguration split-brains.
3. **`MongoDB` v3.2–v3.6 Rollback and Read-Concern Majority Bugs (`Jepsen`
   2015–2020 & MongoDB TLA+ Verification):**
   In early `MongoDB` replica sets (`pv0` and early `pv1` before TLA+ model
   checking of `ReplSet`), replication pulled oplog entries asynchronously from
   any secondary rather than enforcing strict leader-to-follower prefix matching,
   and `readConcern: "local"` / `"majority"` decoupled dirty in-memory
   `WiredTiger` visibility from the majority-committed oplog point (`SOLR`/
   rollback bugs). `Jepsen` demonstrated that under network partitions,
   `MongoDB` acknowledged writes that were subsequently rolled back when the old
   primary rejoined, and `Elle` (VLDB 2020) further uncovered repeatable-read
   and snapshot-isolation anomalies in `MongoDB` v4.2.6 when client sessions
   omitted explicit causal-consistency timestamps (`afterClusterTime`).
4. **`CockroachDB` and `TiKV`/`TiDB` Timestamp-Cache and Lock-Resolution
   Isolation Bugs (`Jepsen` & `Elle`):**
   - In `CockroachDB` beta (`2016–2017` Jepsen audit), clock-offset assumptions
     and incomplete range-lease transfers during Raft leader elections allowed
     two nodes to serve reads/writes for the same key range during lease
     handoff, violating single-key linearizability.
   - In `TiDB`/`TiKV` (`Elle` VLDB 2020), Percolator-style two-phase commit
     (`Prewrite` $\to$ PD Timestamp Oracle `commit_ts` $\to$ `Commit`) suffered
     from an isolation bug when pessimistic/optimistic lock cleanup raced with
     schema metadata changes or when `ReadIndex` bypassed the Raft log without
     checking whether a higher-term leader had already committed a conflicting
     write, yielding `G1c` (circular information flow) and `G-single` (read skew)
     cycles in `Elle`'s dependency graph.

#### 2.4 Kubernetes Operator Stale-Informer-Cache TOCTOU, Orphan Leaks, and Infinite Reconciliation Livelocks (`Sieve` OSDI 2022 and `Anvil` OSDI 2024)

Kubernetes operators (`Cassandra-Operator`, `ZooKeeper-Operator`,
`RabbitMQ-Operator`, `MongoDB-Operator`, `Percona-XtraDB-Operator`, `Yugabyte-Operator`)
implement level-triggered control loops (`reconcile(ctx, req)`) that read
cluster state from a local in-memory **informer cache** (populated asynchronously
via `Watch` streams from `kube-apiserver`/`etcd`) and issue imperative API
mutations (`Create`, `Update`, `Delete`, `Patch`).

Xudong Sun et al. systematically analyzed and verified these operators in two
milestone studies—**`Sieve`** (OSDI 2022, which discovered **28 new safety and
liveness bugs across 10 widely used Kubernetes operators**) and **`Anvil`**
(OSDI 2024 Jay Lepreau Best Paper, which built formally verified Kubernetes
controllers for ZooKeeper, RabbitMQ, and FluentBit in `Verus` using **Eventually
Stable Reconciliation (`ESR`)**):

1. **Time-of-Check-to-Time-of-Use (`TOCTOU`) Stale-Cache Overwrites and Data
   Loss (`Sieve` Stale-State Bug Class):**
   Suppose at step $t_1$, an operator reconciler creates a `PersistentVolumeClaim`
   (`PVC-0`) or scales a `StatefulSet` from 3 to 4 pods on `kube-apiserver`. At
   step $t_2$, another event triggers a second invocation of `reconcile` **before**
   the `Watch` notification for step $t_1$ has arrived at the operator's local
   informer cache. Reading the stale cache (`r.Get` / `r.List`), the operator
   believes `PVC-0` does not exist (or that the `StatefulSet` still has 3 pods)
   and re-issues a conflicting creation, overwrites a newer `Spec` with a stale
   in-memory struct (Without a `resourceVersion` precondition check!), or
   triggers a premature scale-down that deletes an active database node's
   underlying storage volume.
2. **Unobserved Intermediate State Transitions (`Sieve` Time-Travel /
   Skipped-State Bug Class):**
   Because Kubernetes `Watch` streams coalesce or drop intermediate updates when
   watches reconnect (`410 Gone` relist), an operator written with implicit
   **edge-triggered** assumptions (for example, waiting to observe `Pod.Status.Phase
   == Running` before initializing a Raft peer, or waiting to see a temporary
   annotation before removing a finalizer) permanently stalls when the cluster
   transitions `Pending -> Running -> Terminating` between two informer snapshots.
3. **Orphan Resource Leaks on Crash / Partial Failure Before Finalizer
   Registration (`Anvil` OSDI 2024):**
   When an operator provisions an external resource (such as an AWS RDS instance,
   load balancer, or sub-resource `Secret`) before persisting a Kubernetes
   `finalizer` or `ownerReference` in `etcd`, a crash or transient `500 Internal
   Server Error` right after the external creation leaves an untracked orphan
   resource that continues billing or exposing network ports even after the parent
   Custom Resource (`CR`) is deleted.
4. **Infinite Reconciliation Oscillation / Livelock (`Sieve` & `Anvil`):**
   Two controllers watching overlapping fields—or a single controller whose map/slice
   serialization order (`EnvVars`, volume mounts, or floating-point CPU resource
   strings `"100m"` vs. `"0.1"`) differs from `kube-apiserver`'s canonicalized
   admission defaults—detect a spurious diff on every `reconcile` tick, issuing
   an endless stream of `Update` calls that increment `resourceVersion`, trigger
   a new `Watch` event, and spin `kube-apiserver` and `etcd` at 100% CPU forever
   (`EventualOut.diverges`).

#### 2.5 Architectural Lessons for Anneal's Four `trusted/` Primitives in Storage, Consensus, and Control Loops

- **Primitive 1 (`Language SemObs` & `Partial`):**
  - **All-prefix availability and durability invariants:** In storage engines and
    Kubernetes controllers, correctness is not merely a property of the final
    quiescent state; a rolling update that drops `activePods` below
    `PodDisruptionBudget` at step 4 before recovering at step 8 has caused a
    production outage. Because Anneal's `BehaviorOf` and `EventualBehaviorOf`
    define `defined : Prop` by quantifying over **every finite step prefix $n$**
    (`∀ n tr out, ReachesPrefix M p init n init tr out → out.isSafe`), encoding
    continuous safety invariants (no key resurrection, no split-brain commit at
    any index, `activeReplicas >= minAvailable` at every step) into the transition
    guard `StepResult.failed` guarantees **zero-downtime intermediate safety** across
    all prefixes.
- **Primitive 2 (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`, &
  `Abstracts`):**
  - **Closing the unverified shim / dual-emitter gap (`FSCQ` / `Yggdrasil`):**
    Just as `Yggdrasil` translated a Python model into both Z3 and Cython C, and
    Anneal's `mir-to-x86` branch (`4f45f0a391a9`) initially translated MIR to
    both `Mir.lean` and `.anneal/Prog.s` in unverified Rust, any unverified shim
    between the verified model and the executed code is a single point of failure.
    Anneal's **proof-gated compilation** (`Compiles L_Spec L_Impl codec`) and
    single-source `.olean`-bound code emission
    (`anneal-rustc-obligation-inventory-and-single-source-codegen-2026`) keep the
    concrete implementation inside the refinement chain rather than trusting an
    external extractor.
  - **Linearizability and isolation (`Elle` VLDB 2020) via `Compiles`:** When the
    source language $L_{\text{Serial}}$ models a single-node atomic transaction
    executor and the target language $L_{\text{Dist}}$ models distributed Raft /
    2PC replicas, `Compiles L_Serial L_Dist codec` requires that for every
    asynchronous network schedule, the client-visible transaction history (`SemObs`)
    decoded from $L_{\text{Dist}}$ is a valid serial history of $L_{\text{Serial}}$,
    automatically ruling out `Elle`'s `G1c`/`G-single` isolation cycles and Raft
    Figure 8 split-brains.
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`):**
  - **`StepResult.externalCall` as the universal boundary guard for WAL, LSM
    compactions, and Kubernetes `resourceVersion` preconditions:**
    - In a storage engine, every disk write or SSTable compaction emit is an
      `externalCall (boundaryInv : Bool) branches`: `boundaryInv` checks
      `flushedLSN >= page.pageLSN` (the ARIES Write-Ahead Logging rule) and, for
      LSM tombstone drops, `tombstone.seq < earliest_snapshot ∧
      disjointFromDeeperLevels(tombstone.range)`. Any `RocksDB` `#4747`/`#7703`
      premature tombstone drop evaluates `boundaryInv = false` and steps
      immediately to `.failed`!
    - In a Kubernetes operator, every informer read and `kube-apiserver` write is
      an `externalCall`: `branches` demonically supplies arbitrary lagging
      informer states (modeling `Sieve`'s stale-cache perturbations), while
      `boundaryInv` on `Update`/`Delete` requires an explicit `resourceVersion`
      optimistic-concurrency check and requires finalizer registration before
      external cloud resource allocation (`Anvil` ESR safety).
  - **`ProductiveOn` + `EventualBehaviorOf` for ESR convergence and
    anti-abort-all:**
    - Rules out the trivial transaction manager that aborts 100% of transactions
      and the trivial Kubernetes controller that returns `RequeueAfter(∞)`: under
      post-GST / quiescent conditions (`pre`), `ProductiveOn` +
      `EventualBehaviorOf` forces finite-step convergence (`.terminated`) to a
      state satisfying `DesiredSpec`, refuting infinite reconciliation livelocks!
- **Primitive 4 (`VerificationResult` / `ScopedVerificationResult` &
  `TrustPolicy`):**
  - Separates unconditional safety obligations (which must hold under arbitrary
    message loss, crashes, and stale informer caches with `waived = []`) from
    conditional liveness/convergence obligations that depend on hardware/network
    fairness assumptions (such as `GST`—Global Stabilization Time—or bounded disk
    I/O completion, tracked as explicit `TCBModel` parameters or scoped policy
    entries).

### 3. Network Data/Control Planes (`P4` / `BGP`) and Cloud IAM / Differential Privacy Failures

`Basis: normative + documentation + source + derived`

#### 3.1 P4 Compiler Miscompilations and Specification Ambiguities (`Gauntlet` OSDI 2020 and `Petr4` POPL 2021)

Programmable network switches (Intel/Barefoot Tofino ASICs, SmartNICs, `BMv2`
software switches) execute packet-processing pipelines written in `P4-16` and
compiled by `p4c` into fixed-stage hardware Match-Action Tables (`MATs` backed
by TCAM and SRAM) and VLIW action engines. Because line-rate packet pipelines
have no general-purpose CPU loops or dynamic heap, `p4c` performs aggressive AST
inlining, side-effect hoisting, copy propagation, dead-code elimination, and
header-validity analysis.

Two foundational verification projects—**`Gauntlet`** (Fabian Ruffy, Tao Wang,
and Anirudh Sivaraman, OSDI 2020, `arXiv:2006.01074`, which applied SMT-based
translation validation across every IR pass of `p4c`) and **`Petr4`** (Ryan
Doenges et al., POPL 2021, `10.1145/3434304`, which mechanized a formal
operational semantics for `P4-16`)—uncovered **96 distinct compiler bugs** (62
crash bugs and 34 silent miscompilations across `p4c`, `BMv2`, and the
proprietary Barefoot Tofino compiler) and dozens of ambiguities in the official
`P4-16` specification:

1. **Side-Effect Ordering Corruption in Match-Action Table (`MAT`) Keys and
   Action Arguments (`Gauntlet` OSDI 2020):**
   In `P4-16`, expressions inside `table` match keys (`key = { f(hdr.ipv4.ttl) :
   exact; }`) or `switch (t.apply().action_run)` blocks can invoke functions or
   externs that mutate packet headers or metadata as a side effect. `p4c`'s
   `SideEffectOrdering` and `LocalCopyProp` passes hoisted side-effecting calls
   out of table keys or reordered them across short-circuiting boolean operators
   (`&&` / `||`) and array slice assignments (`hdr.eth.srcAddr[47:24]`),
   causing the hardware pipeline to match against the **post-mutation** header
   value instead of the **pre-mutation** value (or vice versa) and silently
   forwarding packets to the wrong egress port.
2. **Header Validity Bit (`isValid()`) Corruption and Uninitialized Header Reads
   (`Gauntlet` & `Petr4`):**
   Every `P4` header struct carries a hidden 1-bit validity flag (`valid : Bool`),
   set by `packet.extract(hdr.ipv4)` or `hdr.ipv4.setValid()` and cleared by
   `hdr.ipv4.setInvalid()`. Reading or writing a field of an invalid header
   (`!hdr.ipv4.isValid()`) produces an undefined value in `P4-16`, and emitting an
   invalid header in the deparser is a no-op. `Gauntlet` discovered multiple
   miscompilations in `p4c` and the Barefoot Tofino back end where:
   - Dead-code elimination or struct initialization passes (`SimplifyDefUse`,
     `RemoveMiss`) dropped a `.setValid()` / `.setInvalid()` assignment when
     none of the header's *data fields* were subsequently read before deparse,
     causing the deparser to silently drop an encapsulated tunnel header (or emit
     a deleted header onto the wire!).
   - Struct copy assignments (`hdr_a = hdr_b`) copied the data fields without
     copying the validity bit in certain Tofino PHV (Packet Header Vector)
     container allocations.
3. **Undefined Parser State Fallthrough and Header-Stack Out-of-Bounds Indexing
   (`Petr4` POPL 2021):**
   `Petr4`'s mechanized operational semantics exposed gaps where the `P4-16`
   specification left behavior contradictory or implementation-defined:
   - When a `parser` state finishes executing its statements without an explicit
     `transition` statement, does it implicitly transition to `reject` (dropping
     the packet) or `accept`? Different targets disagreed.
   - When indexing into a P4 header stack (`hdr.mpls[idx]`) with an out-of-bounds
     runtime index or pushing/popping (`push_front`, `pop_front`), `p4c`'s
     constant-folding passes wrapped or truncated indices differently from the
     `BMv2` software switch and Tofino hardware.

#### 3.2 BGP Persistent Route Oscillation, Dispute Wheels, and MED Non-Determinism (`Griffin-Shepherd-Wilf` 1999 and `RFC 3345`)

At the network control-plane layer, Autonomous Systems (`ASes`) run the Border
Gateway Protocol (`BGP-4`) to exchange reachability paths. Rather than computing
shortest paths over a global scalar metric (like `OSPF`/Dijkstra), each BGP
speaker applies local policy rankings (`LOCAL_PREF`, AS-path length, `ORIGIN`,
`MED`—Multi-Exit Discriminator, eBGP over iBGP, IGP cost to `NEXT_HOP`) and
advertises only its single best route to peers.

Two classic failure mechanisms cause BGP control planes to **diverge into
permanent oscillation** or converge to **non-deterministic routing tables** that
depend on the temporal arrival order of messages:

1. **The Stable Paths Problem (`SPP`) and Dispute Wheels (Griffin, Shepherd, &
   Wilf, ICNP 1999 / SIGCOMM 1999 / IEEE/ACM ToN 2002):**
   Timothy Griffin, Bruce Shepherd, and Gordon Wilf formalized policy-based
   routing as the Stable Paths Problem (`SPP`) and proved that checking whether a
   set of local BGP preference policies has a stable routing assignment is
   **NP-complete**, and that even when a unique stable solution exists,
   asynchronous BGP message passing can diverge forever if the policy graph
   contains a cyclic preference dependency structure called a **Dispute Wheel**
   (where AS $u_0$ prefers a path through $u_1$ over its direct path, $u_1$
   prefers $u_2$, ..., and $u_{k-1}$ prefers $u_0$). Under a single link failure
   or policy edit, routers trapped in a Dispute Wheel endlessly advertise and
   withdraw routes in an infinite loop (`EventualOut.diverges`), causing packet
   blackholes and route-flap damping cascades.
2. **iBGP Route Reflection + `MED` Persistent Oscillation and Non-Determinism
   (`RFC 3345`, McPherson, Gill, Walton, & Retana, August 2002):**
   Even **inside a single AS** (where `LOCAL_PREF` policies are uniform),
   combining iBGP **Route Reflection** (`RFC 4456`, where a route reflector
   advertises only its best path rather than a full mesh) with the `MED`
   attribute causes persistent route oscillation documented in **`RFC 3345`**.
   Because `MED` is compared *only* among paths received from the **same
   neighboring AS** (whereas IGP metric to `NEXT_HOP` is compared across *all*
   ASes), the BGP best-path relation is **non-transitive** ($A \prec B$ via
   IGP cost across different ASes, $B \prec C$ via lower `MED` within the same
   AS, and $C \prec A$ via IGP cost!). In a 3-cluster route-reflector topology
   (`RFC 3345` §2), choosing $A$ hides $C$, allowing $B$ to beat $A$, which
   re-exposes $C$ to beat $B$, oscillating ad infinitum. Furthermore, without
   `bgp deterministic-med`, the route selected by a Cisco/Juniper router depends
   on the chronological order in which routes arrived in the RIB (`age`-based
   tie-breaking), so two identically configured routers in the same AS converge
   to incompatible forwarding tables and create a **permanent forwarding loop**.

#### 3.3 Cloud IAM Authorization Policy Verification and Pre-Release Bug Discovery (`AWS Cedar` OOPSLA 2024)

Fine-grained cloud authorization engines (`AWS Cedar` powering Amazon Verified
Permissions and AWS Verified Access, Google `Zanzibar`, `Open Policy Agent` Rego)
evaluate security policies on every API request. Joseph W. Cutler, Craig Disselkoen,
Aaron Eline, Shaobo He, Kyle Headley, Michael Hicks, Kesha Hietala, Eleftherios
Ioannidis, John Kastner, Anwar Mamat, Darin McAdams, Matt McCutchen, Neha Rungta,
Emina Torlak, and Andrew Wells reported in *"Cedar: A New Language for Expressive,
Fast, Safe, and Analyzable Authorization"* (OOPSLA 2024, `arXiv:2403.04651`) how
they applied **Verification-Guided Development (`VGD`)**—mechanizing Cedar's
evaluator, authorizer, and validator in **Lean 4** while running **Differential
Random Testing (`DRT`)** (`cargo-fuzz` + Lean 4 FFI oracle executing at ~5 $\mu$s
per test case) against the production Rust implementation (`cedar-policy`).

Even though Cedar was designed from scratch by formal-methods experts alongside
its Lean 4 specification, the Lean 4 proofs and DRT campaign uncovered **25 real
bugs before production release** (**4 bugs during interactive Lean 4 proofs** and
**21 bugs during DRT and property-based testing**):

1. **4 Validator Soundness Bugs Caught During Interactive Lean 4 Proofs:**
   Cedar's static type/schema validator is intended to guarantee that any policy
   accepted by `validate(policy, schema)` will never encounter a runtime type
   error or missing-attribute error during authorization (`validate_sound`).
   While attempting to prove `validate_sound` in Lean 4, the authors discovered
   four edge cases where the validator unsoundly accepted ill-typed policies:
   - **Lub (Least Upper Bound) record-attribute optionality mismatch:** When
     computing the least upper bound of two record types in an `if-then-else`
     branch (`if c then {a: 1} else {}`), the validator failed to mark absent
     attributes as optional or failed to check capability sets across branches,
     allowing a subsequent `.a` access to crash at runtime.
   - **Short-circuiting boolean capability propagation (`&&` / `||`):** The
     validator tracks a set of "known-present" optional attributes (`has` guards,
     such as `principal has dept && principal.dept == "eng"`). A bug in how
     capability sets were intersected/unioned across negations (`!`) and `||`
     allowed an unguarded optional attribute read `principal.dept` to pass
     validation when `principal has dept` was false!
   - **Entity-type hierarchy (`in`) and unspecified entity handling:** Edge cases
     in checking `principal in Group::"admins"` when the schema defined empty
     entity sets or action groups.
2. **21 Evaluator, Parser, and Partial-Evaluation Bugs Caught by Lean 4 DRT:**
   Running millions of structure-aware fuzz inputs (`DRT`) comparing the Lean 4
   definitional evaluator against the Rust `cedar-policy` crate exposed 21
   discrepancies:
   - **Error-masking in `forbid` vs. `permit` (`Deny-Trumps-Allow` corner cases):**
     In Cedar, if a policy throws a runtime evaluation error (e.g., integer
     overflow in `ip()` or `decimal()` extension functions or missing entity),
     that individual policy is skipped while recording diagnostics, and `forbid`
     still overrides `permit`. Discrepancies in error short-circuiting and
     extension-function overflow checks caused Rust and Lean to disagree on error
     reporting or authorization outcomes.
   - **Unicode/escaping and namespace resolution in the parser:** Differences in
     how `\u{...}` escapes, wildcard `*` patterns in `like` expressions
     (`"foo*bar"`), and namespace prefixes were normalized between the CST-to-AST
     lowering passes in Rust and Lean.

#### 3.4 Floating-Point Discrete Sampling and Sensitivity Underestimation Attacks on Differential Privacy (`Mironov` CCS 2012 & `Casacuberta et al.` CCS 2022)

Differential Privacy (`DP`) systems (`OpenDP`, IBM `Diffprivlib`, `Chorus`,
Google `PipelineDP`) execute statistical queries over sensitive datasets by
bounding the query's global sensitivity $\Delta f = \max_{D \sim D'} \|f(D) -
f(D')\|_1$ and adding random noise drawn from a Laplace ($\text{Lap}(\Delta f /
\epsilon)$) or Gaussian distribution so that for all neighboring datasets $D \sim
D'$ and output sets $S$:
$$\Pr[\mathcal{M}(D) \in S] \le e^\epsilon \Pr[\mathcal{M}(D') \in S] + \delta$$

Two landmark papers proved that **translating textbook real-number ($\mathbb{R}$)
DP proofs directly into IEEE-754 floating-point (`f64`) software completely
destroys differential privacy ($\epsilon = \infty$)**:

1. **Ilya Mironov's Least-Significant-Bit (`LSB`) Floating-Point Attack (CCS
   2012, `10.1145/2382196.2382264`):**
   Standard implementations generate $\text{Lap}(b)$ noise via inverse transform
   sampling: drawing a uniform IEEE-754 double $U \in (0, 1)$ and computing
   $X = -b \ln(U)$. Because IEEE-754 `f64` has only 53 bits of significand and
   `ln(U)` is evaluated in finite precision, the set of reachable floating-point
   values $-b \ln(U)$ is **sparse**: over $99\%$ of adjacent `f64` bit patterns
   in certain intervals can *never* be produced for a given true count $f(D) =
   c$, and the set of possible `f64` outputs shifts when $f(D)$ changes from $c$
   to $c + 1$! By observing the **least significant bits** of the returned `f64`
   noisy sum, an attacker immediately rules out $f(D) = c$ in a single query
   (violating pure $\epsilon$-DP with $\epsilon = \infty$) and reconstructs the
   exact private record in a few queries. Fixing this required replacing
   continuous `f64` Laplace sampling with exact discrete or snapping mechanisms
   (such as Mironov's **Snapping Mechanism** or Canonne-Kamath-Steinke's exact
   rational **Discrete Laplace / Discrete Gaussian** samplers).
2. **Casacuberta, Shoemate, Vadhan, and Wagaman's Widespread Sensitivity
   Underestimation Attacks on `OpenDP`, `Diffprivlib`, and `Chorus` (CCS 2022,
   `10.1145/3548606.3560708`):**
   Even after libraries adopted discrete or snapping noise samplers, Sílvia
   Casacuberta et al. discovered that **every major open-source DP library
   (`OpenDP`, `Diffprivlib`, `Chorus`) underestimated the sensitivity $\Delta f$
   of basic `SUM` and `MEAN` queries over bounded floating-point or integer data**,
   allowing exact membership-inference attacks:
   - **Non-Associativity and Rounding Drift in Bounded `f64` Sums (`Diffprivlib`,
     `OpenDP`):** Over real numbers, if a user contributes one value $x \in [L,
     U]$ to a dataset $D$, the sensitivity of $\sum_{y \in D} y$ is $\Delta f =
     U - L$. Over IEEE-754 `f64`, floating-point addition is **neither
     associative nor distance-preserving**: if $D$ contains $N$ large numbers that
     shift the floating-point exponent (ULP spacing) and then cancel out, inserting
     a single record $x = 0$ at the start of the summation array changes the
     rounding of every subsequent addition! Consequently, the true IEEE-754
     sensitivity of `SUM(f64)` grows with the dataset size $N$ ($\Delta f_{\text{IEEE}}
     \gg U - L$), allowing an attacker to distinguish $D$ from $D'$ when the
     library calibrates noise only to $U - L$.
   - **Integer Overflow Wrap-Around and clamping/NaN bypasses (`Diffprivlib`,
     `Chorus`):** When computing bounded integer sums in fixed-width two's
     complement (`i32`/`i64`), if the unclipped or intermediate sum overflows and
     wraps from `INT64_MAX` to `INT64_MIN`, a single user's contribution changes
     the query output by $2^{64}$ instead of $U - L$, completely swamping the
     Laplace noise! Similarly, passing `-0.0`, `NaN`, or subnormal floats bypassed
     naive clamping comparisons (`if x < L { L } else if x > U { U } else { x }`
     returns `NaN` when `x` is `NaN` because both `<` and `>` evaluate to
     `false`!).

#### 3.5 Architectural Lessons for Anneal's Four `trusted/` Primitives in Networking, Authorization, and Privacy

- **Primitive 1 (`Language SemObs` & `Partial`):**
  - **P4 Header Validity & Side-Effect Ordering (`Gauntlet` / `Petr4`):** By
    modeling each P4 header in `State` as `Option HeaderBits` (where `none`
    represents `isValid() = false`) and defining `SemObs` as the deparser's
    serialized wire byte stream, any `p4c` optimization pass that drops a
    `.setValid()` call or reorders a side-effecting function inside a `MAT` key
    changes `SemObs` (or triggers `defined = False` on uninitialized header field
    reads) and is immediately rejected by `Compiles`.
  - **Machine-Checked IEEE-754 & Two's-Complement Semantics vs. Real-Arithmetic
    Fictions (`Mironov` / `Casacuberta`):** Just as Anneal's `BoundaryCanarySuite`
    (`anneal-structural-external-calls-and-tcb-mutation-testing-2026`) refuted
    the unmasked `Nat` ALU fiction in `X86Semantics.lean` and enforced exact
    64-bit modular arithmetic and `INT64_MIN / -1` trap checks, Casacuberta et
    al. (CCS 2022) and Mironov (CCS 2012) prove that verifying privacy or
    numerical compilers over idealized $\mathbb{R}$ or $\mathbb{Z}$ while
    executing `f64` or `i64` in production is fundamentally unsound. In Anneal,
    `L_Target` must model exact bit-level `BitVec 64` / IEEE-754 rounding (and
    reject `NaN` clamping bypasses via `defined = False`).
- **Primitive 2 (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`, &
  `Abstracts`):**
  - **Certification of Residual Policy Compilation (`Cedar` / `Zanzibar` $\to$
    SQL):** When partially evaluating a `Cedar` policy into a residual SQL `WHERE`
    predicate, `obs_decodeOut` locks the boolean authorization decision (`Allow`
    vs. `Deny`): the residual SQL query neither leaks unauthorized rows nor
    silently over-filters authorized rows.
  - **Sensitivity Abstract Interpretation via `Abstracts` (`OpenDP`):** Computing
    a sound upper bound on floating-point or fixed-point query sensitivity (using
    exact integer/fixed-point accumulators or ULP-aware rounding bounds as
    prescribed by Casacuberta et al. CCS 2022) is a textbook instance of
    `Abstracts L_Sensitivity L_Query codec`: the abstract sensitivity domain must
    soundly over-approximate the concrete 2-safety distance across all neighboring
    pairs $(D_1, D_2)$.
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`):**
  - **Eliminating BGP Dispute Wheels and `RFC 3345` Route Oscillations via
    `EventualBehaviorOf`:** In BGP verification, a set of router configurations
    satisfies `Compiles L_Intent L_BGP` under `EventualBehaviorOf` **if and only
    if** for every link-failure scenario $F$ with $|F| \le k$ (`InhabitedPre`),
    asynchronous BGP route propagation **terminates in finitely many steps**
    (`.terminated fib`) and the converged `fib` satisfies the reachability/isolation
    intent. Any `RFC 3345` `MED` + Route-Reflection oscillation or Dispute Wheel
    diverges (`EventualOut.diverges`) and is rejected!
  - **Blocking the "Drop-All Firewall" and "Deny-All Authorizer" Goodhart Traps:**
    Requiring `ProductiveOn AuthorizedTrafficPre` paired with `obs_decodeOut`
    makes emitting a `DROP ALL` ACL or a `Deny`-everything policy compiler a hard
    kernel failure, while `InhabitedPre (fun req => eval policy req = .allow)`
    detects shadowed/dead `permit` rules in `Cedar` policies.
  - **`StepResult.externalCall` for DP Privacy-Budget & Discrete-Sampler Gating:**
    Before releasing a noisy query output or calling an external CSPRNG,
    `boundaryInv` verifies `remainingBudget >= queryEpsilon ∧
    noNaNOrOverflowInInput ∧ exactDiscreteSamplerUsed`.
- **Primitive 4 (`VerificationResult` / `ScopedVerificationResult` &
  `TrustPolicy`):**
  - In `Cedar`'s Verification-Guided Development (`OOPSLA 2024`), core theorems
    (`deny_trumps_allow`, `validate_sound`) are proved with zero waivers
    (`waived = []`), while any external IP/Decimal extension function or regex
    engine assumption is isolated as an explicit `TrustPolicy` entry.

### 4. Hermetic Build Systems, Tensor/ML Compilers, and Catastrophic Backtracking (`ReDoS`) Failures

`Basis: documentation + source + derived`

#### 4.1 Build System Dynamic Dependency Unsoundness, Non-Hermetic Cache Poisoning, and Cycle Panics (`Make`/`Ninja`, `Bazel`, `Salsa`, `Pluto`, and `Build Systems à la Carte`)

As Andrey Mokhov, Neil Mitchell, and Simon Peyton Jones formalized in *"Build
Systems à la Carte"* (ICFP 2018 / JFP 2020, `10.1145/3236774`) and Sebastian
Erdweg, Moritz Lichter, and Manuel Weiel proved in *"A Sound and Optimal
Incremental Build System with Dynamic Dependencies"* (`Pluto`, OOPSLA 2015,
`10.1145/2814270.2814316`), an incremental build system is **sound** ("from-scratch
consistent") if and only if building target $T$ in workspace state $W_i$ with a
warm cache produces the exact same output artifact as a clean build (`clean &&
build`) on $W_i$.

In production build and incremental computation engines (`Make`, `Ninja`,
`Bazel`, `Buck2`, `Salsa` in `rust-analyzer`, and `Lake` in Lean 4), four
recurring bug mechanisms break from-scratch consistency or crash the build:

1. **Post-Facto Depfile (`gcc -MMD` / `Ninja`) Header Insertion and Deletion
   Anomalies (`Pluto` OOPSLA 2015 & `Build Systems à la Carte`):**
   `Ninja` and `Make` discover C/C++ `#include` dependencies *only after*
   running `gcc`/`clang` with `-MMD -MF foo.o.d`. Because the `.d` depfile records
   only the files that were actually opened during the *previous* compilation:
   - **Shadowed include path insertion:** Suppose `foo.c` contains `#include
     "config.h"`, search path `-I dir1 -I dir2` is used, and initially only
     `dir2/config.h` exists. The recorded `.d` file lists `dir2/config.h`. If a
     developer later creates `dir1/config.h` (without touching `foo.c` or
     `dir2/config.h`), `Ninja` checks `stat()` only on `foo.c` and
     `dir2/config.h`, sees neither changed, and **skips recompiling `foo.o`**,
     even though a clean build would pick up `dir1/config.h`!
   - **Timestamp granularity (`mtime` slewing) and `stat` caching:** In classic
     `Make` (an *apriori* / timestamp-verifying rebuilder in Mokhov et al.'s
     taxonomy), sub-second edits within a single filesystem timestamp quantum or
     clock skew across NFS/containers cause newly generated headers to appear
     older than stale object files.
2. **Non-Hermetic Sandbox Escapes and Remote Build Execution (`RBE`) Cache
   Poisoning (`Bazel` / `Buck2` / `Lake`):**
   Content-addressed build systems (`Bazel`, `Buck2`) key their shared remote
   action cache (`ActionCache`) by the SHA-256 Merkle digest of the action's
   declared command line, environment variables, and input file tree. Whenever an
   action escapes its sandbox or reads an **undeclared input**—such as:
   - reading host environment variables (`PATH`, `LD_LIBRARY_PATH`, `LANG`,
     `PYTHONHOME`) when `--incompatible_strict_action_env` is not enforced,
   - reading untracked files inside a mounted directory or symlink tree (or in
     Lean 4 `Lake`, relocating prebuilt `.olean` archives across workspaces or
     changing toolchain/import graphs without invalidating cached module hashes,
     as documented in `anneal-v1-interactive-dependency-invalidation-2026-09-28`),
   - or suffering a race condition between dynamic dependency discovery (`CppCompile`
     header scanning / `.d` pruning) and remote cache upload—
   the worker uploads an artifact built against unhashed local state into the
   shared remote CAS under a clean `ActionKey`, **poisoning the remote cache**
   for every developer and CI runner on the repository until the cache key is
   manually salted or flushed.
3. **Salsa / Red-Green Early-Cutoff Dynamic Dependency Cycle Panics
   (`rust-analyzer` / `salsa-rs`):**
   Fine-grained demand-driven incremental frameworks (`Salsa` in `rust-analyzer`,
   `Adapton`, `rustc` query engine) use the **red-green** algorithm: before
   re-executing query $Q(k)$ at revision $R_i$, the runtime walks $Q(k)$'s
   recorded dependencies from revision $R_{i-1}$ (`maybe_changed_after`). If
   every dependency's output equals its $R_{i-1}$ value (**Early Cutoff**), $Q(k)$
   is marked *green* without re-running. However, when a source edit in $R_i$
   changes control flow (for example, changing a Rust trait impl or macro expansion
   in `rust-analyzer`), checking whether an old dependency $D_{\text{old}}$ is
   green can dynamically re-enter $Q(k)$ along a newly formed path that would
   **not** even be reachable if $Q(k)$ were evaluated from scratch in $R_i$
   (a **phantom cycle** during `maybe_changed_after` validation), or can hit a
   genuine mutual-recursion cycle in user code (cyclic trait bounds / type
   aliases) that lacked a monotone fixed-point recovery handler
   (`cycle_recovery`), crashing the `rust-analyzer` LSP server with
   `panicked at 'dependency graph cycle when querying ...'`.

#### 4.2 Tensor and Polyhedral ML Compiler Silent Corruptions (`XLA GSPMD`, `Triton`, `Halide`, and `TVM` via `Tzer` and `NNSmith`)

Deep learning and image-processing compilers (`OpenXLA` / `GSPMD`, OpenAI
`Triton`, `Halide`, Apache `TVM`, `TensorRT`, `PyTorch Inductor`) apply
multi-stage schedule, layout, and distributed-sharding transformations to tensor
graphs. Automated compiler fuzzers—notably **`Tzer`** (Jiawei Liu et al., ISSTA
2022, `10.1145/3533767.3534388`, which found **49 new bugs in Apache `TVM`**)
and **`NNSmith`** (Jiawei Liu et al., ASPLOS 2023, `10.1145/3575693.3575707`,
which found **72 new bugs across `TVM`, `TensorRT`, `ONNXRuntime`, and
`PyTorch`**)—alongside production `OpenXLA` and `Triton` bug trackers document
three critical classes of silent numerical corruption:

1. **`XLA GSPMD` Sharding Propagation and Missing/Misplaced `AllReduce` Bugs:**
   In `OpenXLA`, `GSPMD` (Xu et al., `arXiv:2105.04663`) partitions a single-device
   `HLO`/`StableHLO` computation graph across an $N$-dimensional device mesh
   (`NamedSharding` / `HloSharding`: `Replicated`, `Tiled`, or `Partial`—meaning
   each device holds a partial sum that must be reduced via `AllReduce` or
   `ReduceScatter` before any non-linear operation). Historical bugs in `GSPMD`
   sharding propagation (which motivated Google's migration toward the MLIR-based
   `Shardy` dialect) occurred when:
   - A tensor in `Partial` sharding state (holding unreduced partial sums from a
     contracting `dot_general` matrix multiplication dimension) was passed through
     an elementwise operation, slice, pad, or custom call that assumed `Replicated`
     state without inserting an `AllReduce`, causing each TPU/GPU device to
     apply a non-linear activation ($\text{GeLU}(\sum_i x_i) \ne \sum_i
     \text{GeLU}(x_i)$) to its local partial sum and silently corrupting LLM
     training gradients!
   - Resharding across transposed or unevenly padded mesh dimensions (`PadToStatic`
     / dynamic slice with non-divisible shard sizes) failed to mask out-of-bounds
     halo padding elements (`0` vs. `-inf`) before a `ReduceMax` or `Softmax`
     collective, corrupting attention logits on boundary tokens.
2. **`Triton` GPU Compiler Shared-Memory (`smem`) Data Races, Swizzling Collisions,
   and `mbarrier` Synchronization Bugs:**
   The `Triton` compiler (`triton-lang/triton`) lowers blocked Python tile
   programs (`tl.load`, `tl.dot`, `tl.store`) into LLVM/NVPTX or AMDGCN assembly
   using multi-stage software pipelining (`num_stages`), shared-memory XOR
   swizzling (`TritonGPU` layout encodings: `#blocked`, `#mma`, `#shared`), and
   NVIDIA Hopper asynchronous Tensor Memory Accelerator (`TMA` / `cp.async` +
   `wgmma.mma_async` + `mbarrier`). Recurring miscompilations in `Triton`'s layout
   conversion and pipelining passes (`TritonGPUToLLVM`, `Pipeline`, `InsertBarriers`)
   include:
   - **Missing shared-memory read-after-write (`RAW`) and write-after-read (`WAR`)
     barriers across software-pipelined loop iterations:** When double- or
     triple-buffering `tl.dot` inside a `for` loop, if `InsertBarriers` /
     `MembarAnalysis` fails to insert `bar.sync` (or `wgmma.wait_group`) between
     the warp reading shared-memory buffer slot `stage % K` and the async copy
     overwriting that same slot in iteration `stage + K`, warps silently read
     half-overwritten tile data, producing non-deterministic `NaN`s or wrong
     matrix products that only manifest under high GPU occupancy.
   - **Broken layout-swizzle bijectivity and masked out-of-bounds vector loads:**
     When converting a tensor between `#blocked` and `#mma` layouts via shared
     memory, bugs in computing XOR swizzle parameters (`perPhase`, `maxPhase`,
     `order`) caused two threads in the same warp to write to the same shared-memory
     bank offset (overwriting elements), or caused vectorized `ld.global.v4`
     instructions to ignore a predicate mask `mask = offs < N` when the base
     pointer was not 16-byte aligned.
3. **`Halide` and `TVM` Polyhedral Bounds-Inference, Sliding-Window, and
   Loop-Vectorization Bugs (`Tzer` ISSTA 2022 & `NNSmith` ASPLOS 2023):**
   Both `Halide` and Apache `TVM` (`Tir` / `HalideIR`) separate pure functional
   tensor definitions from imperative scheduling directives (`split`, `reorder`,
   `compute_at`, `store_at`, `rfactor`, `vectorize`, `storage_align`). While
   Clément and Cohen (POPL 2022) and `HaliVer` (CAV 2023) worked to formalize
   Halide scheduling rewrites, `Tzer` and `NNSmith` demonstrated that unverified
   lowering passes in `TVM` and `Halide` routinely miscompile schedules:
   - **Interval-arithmetic bounds-inference underestimation on non-monotonic index
     expressions:** To allocate a scratchpad buffer for a producer stage `P`
     computed at consumer loop level `compute_at(C, xo)`, the compiler infers the
     min/max bounding box of `P` read by `C`. When `C` indexes `P` via modulo,
     floor-division, or negative-stride expressions (`P[x % 3 - y]`), naive
     interval evaluation under-approximated the required domain, allocating a
     buffer too small and reading out-of-bounds memory (`Tzer` `NarrowDataType` /
     `StorageRewrite` bugs).
   - **Unsound loop fusion and `LetStmt` / thread-extent hoisting (`Tzer` ISSTA
     2022):** Merging two loops or hoisting a conditional `Allocate` / `AttrStmt`
     (`threadIdx.x`) across a guard predicate caused threads outside the valid
     iteration domain to write garbage into output tensors or divide by zero in
     index expressions.

#### 4.3 Catastrophic Regular-Expression Backtracking (`ReDoS`) Global Outages (`Stack Overflow` July 20, 2016 and `Cloudflare` July 2, 2019)

Regular expressions are compiled into state machines executed on untrusted network
and user inputs in WAFs (Web Application Firewalls), API gateways, log parsers,
and authorization engines. Unlike Thompson's Non-deterministic Finite Automaton
(`NFA`) lockstep simulation (`RE2`, Rust `regex` crate) which processes an input
byte string of length $N$ in guaranteed $O(N \cdot |R|)$ time, backtracking
Spencer-style regex engines (`PCRE`, JavaScript, Python `re`, Java, `.NET`, Go
backtracking libs, and legacy Lua/PCRE WAF rules) explore ambiguous NFA
transitions via depth-first backtracking, taking **$O(2^N)$ exponential steps**
on inputs that nearly match an ambiguous quantified sub-pattern.

Two of the most famous global outages in modern internet history were caused by
a single catastrophic-backtracking regular expression:

1. **Stack Overflow Global Outage (July 20, 2016 — 34 Minutes Total Downtime):**
   - **Trigger:** A user posted a programming question containing a malformed line
     with approximately **20,000 consecutive space characters (`' '`)** at the end
     of a line without any non-whitespace character following them.
   - **Root Cause:** Stack Overflow's homepage/question list renderer invoked a
     built-in string-trimming routine implemented with the unanchored regular
     expression `^[\s\u200c]+|[\s\u200c]+$` to strip leading and trailing
     whitespace/zero-width non-joiners. Because the second alternation
     `[\s\u200c]+$` was unanchored at the start of the match, when the engine
     encountered 20,000 spaces followed by a non-matching character before the
     end of the string (`$`), it backtracked across every starting position and
     length combination ($O(N^2)$ steps—roughly $2 \times 10^8$ backtracking
     steps per render!).
   - **Blast Radius:** Every web server thread rendering the homepage or question
     feed was pinned at 100% CPU, exhausting the IIS thread pool across the entire
     fleet until engineers replaced the regex with a simple linear loop.
2. **Cloudflare Global Edge Outage (July 2, 2019 — 27 Minutes, 82% Global Traffic
   Drop):**
   - **Trigger:** A Cloudflare engineer deployed a routine Managed WAF rule update
     (`WAF-100178` / XSS detection) containing the sub-expression:
     `(?:(?:\"|'|\]|\}|\\|\d|(?:nan|infinity|true|false|null|undefined|symbol|math)|\`|\-|\+)+[)]*;?((?:\s|-|~|!|{}|\|\||\+)*.*(?:.*=.*)))`
   - **Root Cause:** Notice the nested adjacent wildcard quantifiers at the end:
     `.*(?:.*=.*)`. In a backtracking NFA/PCRE engine (or when PCRE/Lua fallback
     paths without DFA execution budgets are triggered), matching `.*.*=` against
     an HTTP request body containing $N$ characters before an `=` that later fails
     to match tries all $O(2^N)$ ways to split the string between the first `.*`
     and the second `.*`!
   - **Blast Radius:** Within seconds of global deployment, CPU utilization hit
     **100% across every CPU core** on Cloudflare's global edge proxy fleet in
     190+ cities, dropping 82% of global HTTP/HTTPS traffic (`HTTP 502 Bad
     Gateway`). Post-incident, Cloudflare migrated its entire WAF regex engine to
     the **Rust `regex` crate** (based on Thompson NFA / lazy DFA execution with
     guaranteed $O(N)$ linear-time complexity and zero backtracking).

#### 4.4 Architectural Lessons for Anneal's Four `trusted/` Primitives in Build Systems, Tensor Compilers, and Regex Engines

- **Primitive 1 (`Language SemObs` & `Partial`):**
  - **Out-of-bounds halo loads and GPU barrier races as `Partial.ub` (`Halide`,
    `TVM`, `Triton`):** In `L_Kernel`, any out-of-bounds tensor access, unaligned
    vectorized load, or shared-memory read without an intervening barrier after a
    cross-warp write steps to `.failed` (`defined = False`). Consequently,
    `Compiles L_Tensor L_Kernel` forces polyhedral schedule verifiers and
    `Triton` pipelining passes to prove bounds safety and barrier synchronization
    across all valid symbolic shapes `(B, S, H, D)`.
- **Primitive 2 (`BehaviorCodec` / `PartialBehaviorCodec`, `Compiles`, &
  `Abstracts`):**
  - **Distributed Tensor Sharding (`GSPMD` / `Shardy`) as a `PartialBehaviorCodec`:**
    When compiling a single-device tensor graph $L_{\text{Tensor}}$ to an $N$-device
    SPMD mesh $L_{\text{SPMD}}$, `encodeQuery` partitions input tensors into device
    shards and `decodeOut : L_SPMD.Out → Option L_Tensor.Out` reconstructs the
    global output tensor—returning **`none` whenever a tensor annotated as
    `Replicated` differs across devices or remains in an unreduced `Partial` sum
    state**! Thus, a `GSPMD` pass that forgets to insert an `AllReduce` before a
    non-linear activation fails `Compiles` (`decodeOut = none` violates
    `ProductiveOn` and `obs_decodeOut`).
  - **`Triton` Shared-Memory XOR Swizzling as a Verified `BehaviorCodec`:** A
    swizzled shared-memory layout is sound if and only if the coordinate transform
    `(row, col) ↦ (bank, offset)` is a **bijection** on the tile domain—which is
    literally the `decodeOut_encodeOut` and `encodeOut_of_decodeOut` round-trip
    law of `BehaviorCodec`!
  - **Incremental Build Soundness via Clean-vs-Warm `Compiles`:** Modeling clean
    topological evaluation as $L_{\text{CleanBuild}}$ and stateful incremental
    evaluation (`Skyframe`, `Buck2 DICE`, `Salsa`, `Lake`) as $L_{\text{IncBuild}}$
    with `SemObs := Sha256Digest` makes from-scratch consistency across any edit
    sequence $[W_0, \dots, W_m]$ a direct `Compiles L_CleanBuild L_IncBuild`
    theorem.
- **Primitive 3 (`ProductiveOn`, `InhabitedPre`, `EventualBehaviorOf`, &
  `StepResult.externalCall`):**
  - **Preventing `Bazel` / `Ninja` Cache Poisoning via `StepResult.externalCall`:**
    When a build engine spawns a compiler action or reads a file (`externalCall`),
    `boundaryInv` verifies `accessedPath ∈ declaredActionKeyInputs` (and for
    `Ninja`/`Pluto` dynamic dependencies, verifies that *both* positive file reads
    and negative directory-lookup absences along `-I` search paths are recorded in
    the dependency trace). Any undeclared host read evaluates `boundaryInv = false`
    and aborts before polluting the remote cache!
  - **Preventing `Salsa` Cycle Panics and `Cloudflare`/`Stack Overflow` `ReDoS`
    Outages via `ProductiveOn`, `EventualBehaviorOf`, and `CertifiedOptimizationPass`:**
    - In `Salsa` / `DICE`, `EventualBehaviorOf` refutes phantom validation cycles
      by requiring `maybe_changed_after` to terminate on all acyclic query graphs
      (`ProductiveOn AcyclicGraphPre`) and requiring cyclic queries with
      monotone fixed-point handlers to converge in finitely many steps.
    - In regex and parser engines, using Anneal's step-dilated refinement
      `π_dilated k` (`anneal-polar-ctfe-admission-and-semantic-polarity-2026`,
      where $k = O(|R|)$ per input byte) proves **linear-time $O(N)$ execution
      progress** in `BehaviorOf`—mathematically rejecting exponential $O(2^N)$
      backtracking engines (`Cloudflare` `.*.*=.*` and `Stack Overflow`
      `[\s\u200c]+$`) at compile time!
- **Primitive 4 (`VerificationResult` / `ScopedVerificationResult` &
  `TrustPolicy`):**
  - In ML compilers (`XLA` / `TVM` / `Triton`), floating-point parallel reduction
    (`AllReduce` tree summation) is non-associative in IEEE-754. Rather than
    weakening the core `BehaviorCodec` for all passes, `ScopedVerificationResult`
    isolates `.fpAssocInAllReduce` as an explicit, per-pass `TrustPolicy` waiver
    while enforcing strict bitwise identity (`waived = []`) on layout
    transpositions, sharding gathers, and integer/quantized kernels.

#### 4.5 Cross-Domain Synthesis Matrix: Mapping Historical Failure Classes to Anneal's Trusted Primitives

| Historical Failure Case & Primary Source | Root Technical Failure Mechanism | Anneal `trusted/lean/` Primitive That Blocks It | Exact Mechanism in Anneal's TCB |
| :--- | :--- | :--- | :--- |
| **`SQLancer` `TLP`/`NoREC`** (OOPSLA/FSE 2020): >350 wrong-result bugs in `Postgres`, `MySQL`, `CockroachDB`, `SQLite`, `TiDB` | Conflating Kleene 3VL `UNKNOWN` (`NULL`) with `FALSE` in outer-join pushdowns and `NOT IN` / index rules | `Language SemObs` & `BehaviorCodec.obs_decodeOut` | `L_Rel` evaluates predicates in 3VL (`KleeneBool`); `obs_decodeOut` forces target plan to match exact `NULL`-partitioned multiset on all inputs |
| **Kim (1982) `COUNT` Bug & Bag-vs-Set Rewrites** (`Cosette` 2017, `UDP` 2018, `WeTune` SIGMOD 2022) | Inner-join decorrelation drops empty groups (`COUNT = 0`); semi-join rewrite inflates duplicate row counts | `BehaviorCodec` (`SemObs := Multiset Tuple`) | `obs_decodeOut` preserves exact tuple multiplicities ($\text{Tuple} \to \mathbb{N}$) and empty-group rows |
| **SQL Predicate-Pushdown Division-by-Zero Traps** (`Postgres`, `Calcite`, `Spark SQL`) | Pushing `100 / x > 5` below `WHERE x <> 0` introduces runtime trap on dead rows | `Partial` (`defined` vs. `Partial.ub`) & `Compiles` | `Compiles` ($t \le \pi(s)$) forbids turning a `defined = True` query into `Partial.ub` or `.aborted .divByZero` |
| **`Flink` / `Materialize` IVM Retraction & Watermark Bugs** (`DBSP` VLDB 2023, `FLINK-9528`) | Dropping `-U` retractions in Top-$N$/joins; advancing watermarks early and GC-dropping valid window state | `PartialBehaviorCodec` & `ProductiveOn` + `EventualBehaviorOf` | Stream codec returns `decodeOut = none` on unbalanced changelog retractions; `ProductiveOn` blocks holding watermarks at $-\infty$ |
| **`FSCQ` (SOSP 2015) & `Yggdrasil` (OSDI 2016)** FUSE/C shim and disk barrier gaps | Unverified Haskell/Cython FUSE glue bugs; missing `fsync`/`FUA` parent-directory or WAL barriers before data writes | Proof-Gated Compilation (`Compiles`) & `StepResult.externalCall` | Single-source `.olean` codegen eliminates dual-emitter shims; `externalCall` checks `boundaryInv : flushedLSN >= pageLSN` at every disk write |
| **`RocksDB` `DeleteRange` Compaction Bugs** (`#4747`, `#4760`, `#5616`, `#7703`) | Dropping or mis-clipping a range tombstone `[a, z) @ seq` above an active snapshot or deeper SSTable level | `StepResult.externalCall` & `PartialBehaviorCodec` | Compaction emit checks `boundaryInv : seq < earliest_snapshot ∧ disjointFromDeeperLevels`; `obs_decodeOut` rejects resurrected keys |
| **`Raft` Figure 8 & Single-Server Membership Bug** (Ongaro 2014/2015) & **`Jepsen`/`Elle`** (`CockroachDB`, `TiKV`, `MongoDB`) | Committing prior-term entries or pipelining membership changes creates disjoint quorums; stale reads cause `G1c`/`G-single` cycles | `Abstracts` + `Compiles` ($L_{\text{Serial}} \to L_{\text{TLA}} \to L_{\text{Dist}}$) & `ProductiveOn` | Refinement to atomic serial histories rules out split-brains and `Elle` cycles; `ProductiveOn` blocks "abort 100% of transactions" |
| **`Sieve` (OSDI 2022, 28 bugs) & `Anvil` (OSDI 2024)** Kubernetes Operator bugs | Stale informer-cache `TOCTOU` overwrites; orphan cloud resource leaks; infinite reconciliation livelocks | `StepResult.externalCall` & `EventualBehaviorOf` | `externalCall` models demonic lagging informer caches and requires `resourceVersion` + finalizer guards; `EventualBehaviorOf` enforces all-prefix safety + ESR convergence |
| **`Gauntlet` (OSDI 2020, 96 bugs) & `Petr4` (POPL 2021)** in `p4c`, `BMv2`, and Barefoot Tofino | Side-effect reordering in `MAT` keys; dropping `.setValid()` header validity updates; undefined parser fallthrough | `Language SemObs` & `Partial` (`defined`) | Reading an invalid header (`valid = false`) is `Partial.ub`; side-effect hoisting in `MAT` keys alters `SemObs` egress packet bytes |
| **BGP Persistent Route Oscillation** (`Griffin-Shepherd-Wilf` 1999 Dispute Wheels & `RFC 3345` `MED` + Route Reflection) | Non-transitive `MED` + route reflection hides alternate paths, causing infinite `UPDATE`/`WITHDRAW` oscillation | `EventualBehaviorOf` & `ProductiveOn` | `EventualBehaviorOf` requires finite-step BGP convergence (`.terminated fib`) on all $k$-link failures, rejecting `.diverges` |
| **AWS `Cedar` Pre-Release Bugs** (OOPSLA 2024: 4 validator bugs in Lean 4 proof + 21 DRT bugs) | Unsound record-attribute capability LUB in validator (`has` across `||`/`!`); Rust-vs-Lean parser/overflow divergences | `Abstracts` (Validator Soundness) & `Compiles` (Lean-to-Rust Equivalence) | `Abstracts` forces validator acceptance to imply `defined = True` (zero runtime attribute errors); `obs_decodeOut` locks `Allow ↔ Allow` |
| **`Mironov` (CCS 2012) LSB & `Casacuberta et al.` (CCS 2022)** DP Sensitivity Attacks on `OpenDP`, `Diffprivlib`, `Chorus` | Sparse `f64` `-b ln(U)` LSB leaks; `f64` sum non-associativity, `i64` overflow wrap, and `NaN` clamping bypasses | Exact Bit-Level `Language` (`BoundaryCanarySuite`), `Abstracts`, & `StepResult.externalCall` | Rejects idealized $\mathbb{R}$ fictions; `Abstracts` bounds exact bit-level sensitivity; `externalCall` checks budget, `NaN`-freedom, and discrete sampler |
| **`Pluto` (OOPSLA 2015), `Ninja` Depfiles, `Bazel` RBE Cache Poisoning, & `Salsa` Cycle Panics** | Missing negative directory-lookup dependencies; mounting unhashed host files in sandbox; `maybe_changed_after` phantom cycles | `StepResult.externalCall`, `Compiles` ($L_{\text{Clean}} \to L_{\text{Inc}}$), & `CertifiedOptimizationPass` | `externalCall` enforces `sandboxMounts ⊆ hashedInputs`; `Compiles` proves clean-build equivalence; `CertifiedOptimizationPass` enforces Early Cutoff |
| **`XLA GSPMD` Sharding, `Triton` GPU Barriers, & `Halide`/`TVM` Schedule Bugs** (`Tzer` ISSTA 2022, `NNSmith` ASPLOS 2023) | Omitted `AllReduce` on `Partial` shards; missing `bar.sync`/`mbarrier` across `smem` stages; under-approximated halo bounds | `PartialBehaviorCodec` (Sharding/Swizzle Bijection) & `Partial` (`defined`) | Sharding `decodeOut` returns `none` if replicated shards diverge or remain `Partial`; `defined` rejects out-of-bounds halo loads and barrier races |
| **`Stack Overflow` (2016) & `Cloudflare` (2019) `ReDoS` Outages** | Backtracking NFA regexes (`[\s\u200c]+$`, `.*.*=.*`) taking $O(N^2)$ to $O(2^N)$ steps on adversarial inputs | `BehaviorOf` Step-Dilated Refinement (`π_dilated k`) & `ProductiveOn` | Bounding target step budget by $k \cdot N$ per input of length $N$ in `BehaviorOf` proves guaranteed linear-time $O(N)$ execution |

## Boundaries

To prevent future agents from over-generalizing the historical findings or
architectural mappings in this report, the following boundaries apply:

- **Not examined — Mechanized domain instantiations in `theory/`:** While
  Anneal's four core `trusted/lean/` primitives (`Language`/`Partial`,
  `BehaviorCodec`/`PartialBehaviorCodec`, `StepResult.externalCall`/
  `EventualBehaviorOf`/`ProductiveOn`, and `VerificationResult`/
  `ScopedVerificationResult`) are mechanized and kernel-verified across
  `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`,
  `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`, and the five
  companion 2026 reference reports, full production front ends for SQL/DBSP,
  P4-16, Kubernetes controllers, or `StableHLO`/`Triton` have not yet been
  implemented inside `theory/`.
- **Known not to apply — Unmodified deterministic `Partial (Out → Prop)` for
  quantitative probabilistic couplings without relational lifting:** Standard
  single-trace `Partial (Out → Prop)` directly captures safety, totality,
  multiplicity, linearizability, and deterministic sensitivity bounds, but
  expressing approximate $(\epsilon, \delta)$-differential privacy
  ($\Pr[\mathcal{M}(D_1) \in S] \le e^\epsilon \Pr[\mathcal{M}(D_2) \in S] +
  \delta$) or quantitative floating-point ULP error envelopes requires either:
  (a) instantiating `Language` over a 2-safety relational product ($L^2$, where
  `Query := D₁ × D₂` and `Out` carries an approximate relational Hoare logic
  coupling witness), or (b) parameterizing `SemObs` with a quantitative
  approximation relation in `theory/`.
- **Unsupported — Proving true asynchronous liveness (`◇P`) without fairness or
  synchrony hypotheses:** Under completely unconstrained demonic environment
  nondeterminism (where an adversarial network drops 100% of packets forever or
  an OS scheduler never schedules a thread), no distributed consensus protocol
  (`FLP` impossibility, Fischer-Lynch-Paterson 1985) or Kubernetes controller
  can guarantee finite-step termination. In Anneal, `EventualBehaviorOf` and
  `ProductiveOn pre` verify convergence relative to an explicit precondition
  `pre : Query → Prop` that bounds adversarial faults prior to Global
  Stabilization Time (`GST`) or bounds link failures ($|F| \le k$).

## Evidence

All technical claims in this report are grounded in the following primary
sources and repository revisions (observed and cross-checked on `2026-10-31`):

1. **Anneal Trusted Core and Companion Mechanizations (`joshlf/anneal`):**
   - `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`:
     `trusted/lean/Trusted/Refinement.lean` (lines 1–466: `Partial`, `Language`,
     `BehaviorCodec`, `Compiles`, `Abstracts`, `Compiler.SoundOn`,
     `Compiler.Verified`, `TrustedAssumption`, `TrustPolicy`,
     `VerificationResultOn`) and `trusted/lean/Trusted/StepResult.lean` (lines
     1–220: `StepResult`, `PrefixOutcome`, `ExecQuery`, `ExecOut`,
     `SmallStepMachine`, `ReachesPrefix`, `BehaviorOf`).
   - `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`:
     `trusted/lean/Trusted/X86Semantics.lean` and
     `theory/Anneal/Compiler/Peephole.lean`.
   - Companion corpus packages on `refs/heads/reference`
     (`df55c524a051d59e7dd35564f282b30d29133392`):
     - `reports/anneal-behavior-codec-and-progress-refinement-2026/REPORT.md`
       (`PartialBehaviorCodec`, `EventualBehaviorOf`, `ProductiveOn`,
       `InhabitedPre`, `CertifiedOptimizationPass`),
     - `reports/anneal-polar-ctfe-admission-and-semantic-polarity-2026/REPORT.md`
       (`π_dilated k` step-dilated refinement),
     - `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/REPORT.md`
       (`StepResult.externalCall` and `BoundaryCanarySuite`), and
     - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/REPORT.md`
       (`TCBModel`, proof-gated compilation cut elimination, and
       `ScopedVerificationResult`).

2. **Database Query Optimizers, SQL Equivalence, and Incremental View
   Maintenance:**
   - Manuel Rigger and Zhendong Su, *"Detecting Optimization Bugs in Database
     Engines via Non-Optimizing Reference Engine Construction"* (`NoREC`),
     ESEC/FSE 2020, DOI `10.1145/3368089.3409710`.
   - Manuel Rigger and Zhendong Su, *"Finding Bugs in Database Systems via
     Query Partitioning"* (`TLP`), OOPSLA 2020, PACMPL 4(OOPSLA):211, DOI
     `10.1145/3428279`.
   - Manuel Rigger and Zhendong Su, *"Testing Database Engines via Pivoted Query
     Synthesis"* (`PQS`), USENIX OSDI 2020, pp. 667–682.
   - Shumo Chu, Chenglong Wang, Konstantin Weitz, and Alvin Cheung, *"Cosette:
     An Automated Prover for SQL"*, CIDR 2017; and Shumo Chu, Konstantin Weitz,
     Alvin Cheung, and Dan Suciu, *"HoTTSQL: Proving Query Rewrites with
     Univalent SQL Semantics"*, PLDI 2017, DOI `10.1145/3062341.3062348`.
   - Shumo Chu, Brendan Murphy, Jared Roesch, Alvin Cheung, and Dan Suciu,
     *"Axiomatic Foundations and Algorithms for Deciding Semantic Equivalences
     of SQL Queries"* (`UDP`), PVLDB 11(11):1482–1495, 2018, DOI
     `10.14778/3192965.3192971`.
   - Zhaoguo Wang, Zhou Zhou, Yiren Jiang, Haoran Ding, Gansen Hu, Ding Ding,
     Chuzhe Tang, Haibo Chen, and Jinyang Li, *"WeTune: Automatic Discovery and
     Verification of Query Rewrite Rules"*, SIGMOD 2022, pp. 94–107, DOI
     `10.1145/3514221.3526125`.
   - Thomas Neumann and Alfons Kemper, *"Unnesting Arbitrary Queries"*, BTW
     2015, LNI P-241, pp. 383–402.
   - Mihai Budiu, Tej Chajed, Frank McSherry, Leonid Ryzhyk, and Val Tannen,
     *"DBSP: Automatic Incremental View Maintenance for Rich Query Languages"*,
     PVLDB 16(7):1601–1614, 2023 (VLDB 2023 Best Paper), DOI
     `10.14778/3587136.3587137`.

3. **Storage Engines, Distributed Consensus, and Kubernetes Controllers:**
   - Haogang Chen, Daniel Ziegler, Tej Chajed, Adam Chlipala, M. Frans
     Kaashoek, and Nickolai Zeldovich, *"Using Crash Hoare Logic for Certifying
     the FSCQ File System"*, SOSP 2015, pp. 18–37, DOI
     `10.1145/2815400.2815402`.
   - Helgi Sigurbjarnarson, James Bornholt, Emina Torlak, and Xi Wang,
     *"Push-Button Verification of File Systems via Crash Refinement"*
     (`Yggdrasil`), USENIX OSDI 2016, pp. 1–16.
   - Tej Chajed, Joseph Tassarotti, M. Frans Kaashoek, and Nickolai Zeldovich,
     *"Verifying Concurrent, Crash-Safe Systems with Perennial"*, SOSP 2019,
     pp. 243–258, DOI `10.1145/3341301.3359632`.
   - Pandian Raju, Rohan Kadekodi, Vijay Chidambaram, and Ittai Abraham,
     *"PebblesDB: Building Key-Value Stores using Fragmented Log-Structured
     Merge Trees"*, SOSP 2017, DOI `10.1145/3132747.3132765`.
   - `facebook/rocksdb` issue tracker and commits for `DeleteRange` compaction
     and snapshot bugs (`#4747`, `#4760`, `#5616`, `#7703`, `#10250`) and the
     official RocksDB *"DeleteRange: A New Native RocksDB Operation"*
     engineering retrospective.
   - Diego Ongaro and John Ousterhout, *"In Search of an Understandable
     Consensus Algorithm"*, USENIX ATC 2014 (Figure 8 commitment invariant); and
     Diego Ongaro, *"Consensus: Bridging Theory and Practice"*, Stanford PhD
     Dissertation, 2014 (plus 2015 single-server membership change erratum).
   - Kyle Kingsbury and Peter Alvaro, *"Elle: Inferring Isolation Anomalies from
     Experimental Observations"*, PVLDB 14(3):268–280, 2020, DOI
     `10.14778/3457390.3457396`.
   - Xudong Sun, Wenqing Luo, Jiawei Tyler Gu, Aishwarya Ganesan, Ramnatthan
     Alagappan, Michael Gasch, Lalith Suresh, and Tianyin Xu, *"Automatic
     Reliability Testing for Cluster Management Controllers"* (`Sieve`), USENIX
     OSDI 2022, pp. 143–159.
   - Xudong Sun, Wenjie Ma, Jiawei Tyler Gu, Zicheng Ma, et al. (UIUC,
     UW-Madison, VMware Research), *"Anvil: Verifying Liveness of Cluster
     Management Controllers"*, USENIX OSDI 2024, pp. 649–666.

4. **Networking, Cloud IAM Authorization, and Differential Privacy:**
   - Fabian Ruffy, Tao Wang, and Anirudh Sivaraman, *"Gauntlet: Finding Bugs in
     Compilers for Programmable Packet Processing"*, USENIX OSDI 2020, pp.
     683–699, `arXiv:2006.01074`.
   - Ryan Doenges, Mina Tahmasbi Arashloo, Santiago Bautista, Alexander Chang,
     Newton Ni, Samwise Parkinson, Rudy Peterson, Alaia Solko-Breslin, Amanda
     Xu, and Nate Foster, *"Petr4: Formal Foundations for P4 Data Planes"*,
     PACMPL 5(POPL):1–32, 2021, DOI `10.1145/3434304`.
   - Timothy G. Griffin, F. Bruce Shepherd, and Gordon Wilfong, *"The Stable
     Paths Problem and Interdomain Routing"*, IEEE/ACM Transactions on
     Networking 10(2):232–243, 2002 (preliminary versions in ICNP 1999 and
     SIGCOMM 1999).
   - Danny McPherson, Vijay Gill, Daniel Walton, and Alvaro Retana, *"Border
     Gateway Protocol (BGP) Persistent Route Oscillation Condition"*, IETF
     `RFC 3345`, August 2002.
   - Joseph W. Cutler et al., *"Cedar: A New Language for Expressive, Fast,
     Safe, and Analyzable Authorization"*, PACMPL 8(OOPSLA1):Article 118, 2024,
     DOI `10.1145/3649835`, `arXiv:2403.04651`.
   - Ilya Mironov, *"On Significance of the Least Significant Bits for
     Differential Privacy"*, ACM CCS 2012, pp. 650–661, DOI
     `10.1145/2382196.2382264`.
   - Sílvia Casacuberta, Michael Shoemate, Salil Vadhan, and Connor Wagaman,
     *"Widespread Underestimation of Sensitivity in Differentially Private
     Libraries and How to Fix It"*, ACM CCS 2022, pp. 471–484, DOI
     `10.1145/3548606.3560708`, `arXiv:2207.10635`.

5. **Hermetic Build Systems, Tensor/ML Compilers, and Catastrophic Backtracking:**
   - Sebastian Erdweg, Moritz Lichter, and Manuel Weiel, *"A Sound and Optimal
     Incremental Build System with Dynamic Dependencies"* (`Pluto`), OOPSLA
     2015, pp. 89–106, DOI `10.1145/2814270.2814316`.
   - Andrey Mokhov, Neil Mitchell, and Simon Peyton Jones, *"Build Systems à la
     Carte"*, PACMPL 2(ICFP):Article 79, 2018, DOI `10.1145/3236774`.
   - Yuanzhong Xu et al., *"GSPMD: General and Scalable Parallelization for ML
     Computation Graphs"*, `arXiv:2105.04663`, 2021.
   - Jiawei Liu, Yiming Lin, Lukasz Ziarek, et al., *"Coverage-Guided Tensor
     Compiler Fuzzing with Joint IR-Pass Mutation"* (`Tzer`), ISSTA 2022, pp.
     400–412, DOI `10.1145/3533767.3534388`.
   - Jiawei Liu, Jinkun Lin, Fabian Ruffy, Cheng Tan, Jinyang Li, Aurojit Panda,
     and Lingming Zhang, *"NNSmith: Generating Diverse and Valid Test Cases for
     Deep Learning Compilers"*, ASPLOS 2023, Vol. 2, pp. 530–543, DOI
     `10.1145/3575693.3575707`.
   - Stack Exchange Status Blog, *"Outage Postmortem — July 20, 2016"* (20,000
     spaces catastrophic backtracking in `^[\s\u200c]+|[\s\u200c]+$`).
   - John Graham-Cumming (Cloudflare), *"Details of the Cloudflare outage on
     July 2, 2019"*, Cloudflare Technical Postmortem, July 12, 2019 (`WAF`
     `.*(?:.*=.*)` CPU exhaustion and migration to the Rust `regex` engine).

## Revalidation

To revalidate the architectural bindings between these historical failure modes
and Anneal's `trusted/lean/` primitives when `Trusted/Refinement.lean` or
`Trusted/StepResult.lean` evolves:

1. **Check the four `trusted/lean/` primitive signatures and companion Lean 4
   proofs:**
   Verify that the standalone Lean 4 modules in the companion packages—
   `reports/anneal-behavior-codec-and-progress-refinement-2026/support/BehaviorCodecExpressiveness.lean`,
   `reports/anneal-behavior-codec-and-progress-refinement-2026/support/AntiDegeneracyAndCallbackFraming.lean`,
   `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/support/StructuralExternalCallAndCanaries.lean`,
   and
   `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/support/ProofGatedCompilationAndTrustPolicy.lean`—
   continue to typecheck with zero kernel axioms (`lean -DElab.async=false
   -Ddebug.skipKernelTC=false`).
2. **Verify each failure-to-primitive discriminator when modifying `trusted/`:**
   - If `Partial` or `Compiles` is modified, confirm that `defined = False`
     remains at $\top$ so target programs cannot introduce new traps (SQL
     division-by-zero pushdowns, P4 invalid header reads, `Halide`/`Triton`
     out-of-bounds accesses) on queries where the source specification is
     defined.
   - If `BehaviorCodec` / `PartialBehaviorCodec` is modified, confirm that
     `decodeOut : L₂.Out → Option L₁.Out`, `decode_encode_out`, and
     `obs_decodeOut` remain intact so non-surjective target states (diverged
     `GSPMD` device shards, unbalanced `DBSP`/`Flink` changelog retractions,
     corrupted SSTable checksums) map to `none` and fail `Compiles`.
   - If `StepResult.externalCall`, `EventualBehaviorOf`, or `ProductiveOn` is
     modified, confirm that `boundaryInv = false` steps to `.failed`, that
     `EventualBehaviorOf` quantifies `defined` over all finite prefixes while
     rejecting `.diverges` (BGP Dispute Wheels, Kubernetes livelocks), and that
     `ProductiveOn` paired with `InhabitedPre` rejects vacuous "abort-all /
     drop-all / deny-all / hold-watermark" implementations.
   - If `VerificationResult` or `TrustPolicy` is modified, confirm that waived
     obligations remain positively scoped on the consequent (`ob.id ∈ waived ∨
     ob.prop`) so an edge-case defect in a waived rewrite rule or hardware model
     cannot discharge unwaived obligations via `False.elim`.
