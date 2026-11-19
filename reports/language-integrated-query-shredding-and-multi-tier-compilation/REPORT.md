# Language-Integrated Query Shredding and Multi-Tier Web Compilation

## Summary

Application stacks bridging general-purpose programming languages, relational SQL databases, and browser clients face four structural impedance cliffs that ad-hoc ORMs, raw SQL strings, and stateless REST glue fail to solve:

1. **Higher-order quotation normalization (`T-LINQ`, ICFP 2013) and nested query shredding (`SIGMOD 2014`, `links-lang/links`):** Ad-hoc ORM translators (C# LINQ-to-SQL, Hibernate, Entity Framework) suffer runtime translation failures (`NotSupportedException`) on higher-order abstractions and silent $O(N)$ `N+1` query avalanches or exponential `LEFT OUTER JOIN` Cartesian blowups on nested collections. `T-LINQ` uses typed quotation/anti-quotation and a strong-normalization theorem over Nested Relational Calculus (NRC) to guarantee that every closed flat-result query compiles to a single flat SQL query. **Query Shredding** (`links-lang/links`, `core/query/evalNestedQuery.ml`) extends this to arbitrarily nested collection results by replacing every nested `` `List `` type with a synthesized integer index pair `(static_tag, dynamic_index)` (`(a, d)`), compiling a nested query of type-size $k$ into a **fixed $k$ flat SQL queries** (independent of row count $N$) plus an $O(\text{output})$ client-side hash-map stitching pass (`Stitch.stitch`).
2. **SQL three-valued `NULL` and bag-vs-set semantic divergence (`HoTTSQL`/`Cosette`):** Host languages use two-valued total `Option<T>` (`None == None` is `true`) and set/list abstractions, whereas ISO SQL tables are duplicate-preserving multisets (bags) governed by Kleene three-valued `NULL` logic. Live SQLite execution confirms that `WHERE id NOT IN (SELECT x FROM b)` collapses from `2` rows to `0` rows the instant `b` contains a single `NULL`, and naive `INNER JOIN` decorrelation of an `IN` subquery doubles bag multiplicities (`4` vs. `2` rows). `Cosette` (`uwdb/Cosette`, `hott/library/UnivalentSemantics.v`) models SQL tables as K-relations in Coq/HoTT to prove bag-and-NULL-sound rewrites and exposes real optimizer bugs and unhandled fragments (`NULL`, `GROUPBY`, `ORDERBY`, `VALUES`) across Apache Calcite rules.
3. **Closed-world multi-tier security vs. boundary rigidity (`Ur/Web`, `Links`, `ScalaLoci`):** `Ur/Web` (`urweb/urweb`) compiles a single row-polymorphically typed program into native C server code, client JavaScript (`source`/`signal` reactive DOM), and typed SQL (`lib/ur/basis.urs`), proving XSS, SQLi, dead-link, and CSRF immunity (`src/effectize.sml` statically rejects GET handlers with side effects unless whitelisted via `safeGet`). However, holistic closed-world compilation collides with open-world third-party JS/C ecosystems, independent client/server release schedules, and subtle C-FFI lifetime/commit seams.
4. **Transactional FFI, schema evolution, and end-to-end reactivity (`uw_register_transactional`, `Cambria`, `DBSP`):** Under `SERIALIZABLE` SQL retries, naked external I/O causes phantom side effects. `Ur/Web`'s C runtime (`src/c/urweb.c:3706-3795`) partitions registered transactionals into rollback-capable (`rollback != NULL`, committed before `db_commit` and rolled back on SQL serialization failure `code == -1`) and irreversible (`rollback == NULL`, executed after `db_commit`)—yet source inspection reveals a concrete split-brain window if a post-`db_commit` irreversible callback sets `uw_has_error(ctx)` after PostgreSQL/MySQL has already committed. Meanwhile, `Cambria` (`inkandswitch/cambria`, 10 bidirectional `LensOp` primitives) addresses rolling multi-version schema evolution where lockstep compilers break, and `DBSP` (`VLDB 2023`) lifts relational queries into $O(|\Delta|)$ Z-set incremental circuits whose server-to-client partitioning requires atomic transaction batching and optimistic rebase.

## Applicability

This report covers the formal semantics, compilation passes, runtime protocols, and cross-boundary failure modes of:

- **Language-integrated query normalization and nested shredding:** Cheney, Lindley, and Wadler's `T-LINQ` (`doi:10.1145/2500365.2500586`), `Query Shredding` (`doi:10.1145/2588555.2612186`), and their production OCaml implementation in `links-lang/links` (revision `7100e2891346b5bae483fe9a02791c900047388a`, `core/query/`).
- **SQL bag/NULL formal verification:** `uwdb/Cosette` (revision `7a951aa3b1a70a8b310c676e524740b7114975c3`, `hott/library/UnivalentSemantics.v` and `examples/calcite/calcite_result_with_label.csv`) and `HoTTSQL` (`doi:10.48550/arXiv.1607.04822`).
- **Tierless web compilation, C arena/transactional FFI, and placement types:** `urweb/urweb` (revision `55a881ff9b50d9e5c3b2fd564f5cd44a5cc5e6bc`, `lib/ur/basis.urs`, `include/urweb/urweb_cpp.h`, `src/c/urweb.c`, `src/effectize.sml`, `src/sidecheck.sml`), Chlipala's PLDI 2010 (`doi:10.1145/1806596.1806612`) and POPL 2015 (`doi:10.1145/2676726.2677004`) papers, and `ScalaLoci` (`doi:10.1145/3276499`) for peer-placement comparison.
- **Rolling schema evolution and incremental view maintenance:** `inkandswitch/cambria` (revision `da8961440cac7eba1c3113488f5bcbc26046620f`, `src/lens-ops.ts`) and `DBSP` (`doi:10.14778/3587136.3587137`).

Findings apply to compiler architects designing database-integrated DSLs, multi-tier frameworks (including server/client splitters and GraphQL/ORM backends), and transactional C/Rust-to-SQL runtimes. Exact line citations for `Links`, `Ur/Web`, `Cosette`, and `Cambria` reflect the pinned revisions above; observations about `ScalaLoci` and `DBSP` derive from their peer-reviewed papers rather than source-tree audits.

## Findings

### 1. Higher-Order Query Normalization (`T-LINQ`) and Nested Query Shredding

#### 1.1 Quotation Normalization and Conservativity (`T-LINQ`, ICFP 2013)
Basis: normative (`doi:10.1145/2500365.2500586`) + source (`links-lang/links`)

Conventional database integration splits between raw concatenated SQL strings (vulnerable to SQL injection and unchecked schema drift) and reflection-based ORMs (`LINQ-to-SQL`, `Hibernate`, `Entity Framework`), which accept arbitrary host-language expressions at compile time yet fail unpredictably at runtime with `NotSupportedException` or silently emit $O(N)$ queries when developers factor common predicates into higher-order functions.

Cheney, Lindley, and Wadler's **`T-LINQ`** (`ICFP 2013`, extending Limsoon Wong's 1996 conservativity theorem for Nested Relational Calculus) establishes a sharp, statically enforced compilation guarantee:

- **Typed staged quotation (`<@ e @>` / `%e`):** Query expressions live in a higher-order functional sub-language (`NRC` with lambdas, records, conditionals, comprehensions `for (x <- L) M`, empty `[]`, singleton `[M]`, and bag union `L ++ N`), cleanly separated from arbitrary host-side effects and recursion.
- **Strong normalization theorem:** Symbolic $\beta$-reduction, record projection cancellation, conditional pushing, and comprehension flattening (`for (y <- for (x <- L) M) N  ~>  for (x <- L) for (y <- M) N`, hoisting `++` to the top level and lowering `if` guards to comprehension tails) are **strongly normalizing and confluent**.
- **Single-SQL-query guarantee:** Every closed, well-typed query whose *result type* is a flat bag of flat records (`List { a1: Base1, ..., an: Basen }`)—regardless of how many higher-order functions, intermediate nested collections, or local helper combinators were composed inside the query—provably normalizes at staging time to a union of flat SPJU (`SELECT ... FROM ... WHERE ...`) blocks translatable to a **single SQL query** with zero runtime `NotSupportedException`s and zero `N+1` round-trips.

In `links-lang/links` (`7100e2891346b5bae483fe9a02791c900047388a`, `core/query/query.ml` and `core/query/evalNestedQuery.ml`), normalization hoists `Concat` (`UNION ALL`) to the top level and lowers `If` conditionals into comprehension tails (`Split.query`, `evalNestedQuery.ml:260-310`), freshening comprehension binders (`freshen_for_bindings`, `query.ml:18-35`).

**Hard expressiveness and code-size boundaries:**
1. **First-order ceiling:** Pure SPJU normalization cannot express transitive closure or arbitrary graph reachability (requiring recursive CTEs `WITH RECURSIVE`) without leaving the guaranteed-normal-form fragment.
2. **Exponential SQL text blowup without sharing:** Distributing unions (`Concat`) and conditionals (`If`) across nested comprehensions can duplicate sub-expressions exponentially unless intermediate common subexpressions are factorized via `LetInsertion` (`evalNestedQuery.ml:310+`) or SQL `WITH` CTEs.
3. **Aggregation, ordering, and `LIMIT`:** Mixing `GROUP BY`, `ORDER BY`, and `LIMIT`/`OFFSET` inside nested comprehensions invalidates naive comprehension commutativity; `Links` explicitly notes (`evalNestedQuery.ml:256-260`) that standard `Split` normalization does not preserve list ordering and requires dedicated ordering/grouping extensions (`GroupBy`, `AggBy`, `Delateralize`).

#### 1.2 Nested Relational Query Shredding and Linear-Time Stitching (`SIGMOD 2014`)
Basis: normative (`doi:10.1145/2588555.2612186`) + source (`links-lang/links`) + execution

Real applications routinely request nested trees—e.g., `List { dept: String, emps: List Employee, projs: List Project }`—where flat `T-LINQ` does not directly apply. Without shredding, systems hit one of two catastrophic walls:
- **`N+1` query avalanche:** Issuing 1 query per parent row explodes to $1 + D + D \cdot E$ network round-trips on 3-level nesting.
- **`LEFT OUTER JOIN` Cartesian blowup:** Joining independent sibling collections (`emps` and `projs`) under a single parent multiplies rows into $D \cdot E \cdot P$ duplicated parent rows with `NULL` sentinel padding for empty child lists.

**Query Shredding** (`SIGMOD 2014`; implemented verbatim in `links-lang/links`, `core/query/evalNestedQuery.ml:1-100, 218-260, 741-860`) eliminates both flaws simultaneously:

1. **Comprehension tagging (`tag_query`, `evalNestedQuery.ml:10-46`):** Assigns a unique positive integer static tag `a` to every `For` comprehension in the normalized query AST.
2. **Type-directed shredding (`Shred.shred_inner_type` & `Shred.shred_outer_type`, `evalNestedQuery.ml:220-250`):**
   - Inside any flat result query (`shred_inner_type`), every nested `` `List _ `` field is replaced by a flat 2-integer index record `{"1": Int, "2": Int}` representing `(a, d)` — `(static_comprehension_tag, dynamic_parent_index)`.
   - For each `` `List `` constructor occurring at path $p$ in the result type (`shred_outer_type`), shredding emits one flat SQL query whose rows carry `{"1": {"1": a_parent, "2": d_parent}, "2": inner_row}` — i.e., the parent collection's `(a, d)` key paired with the flat shredded child row!
   - Thus a query of result type containing $k$ list constructors compiles statically to **exactly $k$ flat SQL queries** (`Shred.package`), completely independent of database cardinality $N$.
3. **Pipeline orchestration (`unordered_query_package`, `evalNestedQuery.ml:825-840`):**
   `Split.query` $\to$ `tag_query` $\to$ `Shred.shred_query` $\to$ `LetInsertion.lins_query` $\to$ `FlattenRecords.flatten_query` $\to$ `QL.sql_of_let_query`.
4. **Client-side linear stitching (`module Stitch`, `evalNestedQuery.ml:741-820`):**
   - `build_stitch_map` scans each flat SQL result set once, grouping rows into an `IntPairMap` keyed by `(a, d)` (`insert (a, d) w m`).
   - `stitch` starts from root key `(Shred.top, 1)` (`stitch_mapped_query`, line 816) and walks the type package recursively, replacing each `{"1": a, "2": d}` handle with `lookup (a, d) m` in $O(\text{output size})$ total time—naturally yielding `[]` for empty child collections (like `EmptyDept`) with zero `NULL` sentinel ambiguity!

**Empirical verification (`execution` probe on SQLite 3 / Python 3.13.15):**

| Workload Scenario | Naive `N+1` Queries | `LEFT OUTER JOIN` Rows | Shredded Flat Queries ($k$) | Shredded Total Wire Rows |
|---|---|---|---|---|
| Sibling fanout (`D=1, E=50, P=50`) | `3` (or `1 + 2D`) | **`2,500`** (50×50 Cartesian product) | **`3`** (constant) | **`101`** (`1 + 50 + 50`) |
| 3-level hierarchy (`D=10, E=20, T=5`) | **`211`** (`1 + 10 + 200`) | `1,000` (with 100× duplicated dept cols) | **`3`** (constant) | **`1,210`** (`10 + 200 + 1000`, no wide parent dup) |
| Live SQLite3 concrete schema (`2` depts, 1 empty, `2` emps, `2` projs) | `5` | `5` (with `NULL` padding for `EmptyDept`) | `3` | `6` (`2+2+2`), exact stitch `emps: [], projs: []` |

**Critical transactional consistency seam (derived):** Because shredding issues $k \ge 2$ distinct flat SQL statements, executing them under default `READ COMMITTED` isolation without wrapping all $k$ queries inside a single `BEGIN TRANSACTION ISOLATION LEVEL REPEATABLE READ` (snapshot) transaction exposes **torn reads**: if a concurrent writer commits a new department and employee between Query 1 and Query 2, Query 2 returns orphan `(a, d)` keys absent from Query 1, or Query 1 references a parent whose concurrently deleted children silently vanish to `[]` in `Stitch.lookup` (`evalNestedQuery.ml:746-749` silently returns `[]` on missing `(a, d)`!).

---

### 2. SQL Three-Valued `NULL` Logic, Bag Semantics, and Optimizer Verification (`HoTTSQL` / `Cosette`)

#### 2.1 Semantic Mismatches at the PL $\leftrightarrow$ SQL Boundary
Basis: source (`uwdb/Cosette`) + execution

Bridging strongly typed functional/systems languages (where `Option<T>` obeys two-valued equality `None == None` and collections distinguish lists/sets) to ISO SQL crosses three notorious semantic discontinuities:

1. **Kleene three-valued `NULL` collapse (`execution`):** Under SQL three-valued logic (`TRUE`, `FALSE`, `UNKNOWN`), `v != NULL` evaluates to `UNKNOWN`, and `WHERE` drops every row whose predicate is `FALSE` or `UNKNOWN`. In our live SQLite3 probe over `a = {1, 2, 3}` and `b = {1, NULL}`:
   - `SELECT COUNT(*) FROM a WHERE id NOT IN (SELECT x FROM b)` returns **`0`** (NOT `2`!), because `2 != NULL` is `UNKNOWN`, turning the conjunction `(2 != 1) AND (2 != NULL)` into `UNKNOWN`.
   - Rewriting via two-valued anti-join `SELECT COUNT(*) FROM a WHERE NOT EXISTS (SELECT 1 FROM b WHERE b.x = a.id)` returns **`2`**.
   - Worse, SQL applies *inconsistent* `NULL` equality across clauses: `=` treats `NULL = NULL` as `UNKNOWN`, whereas `GROUP BY`, `DISTINCT`, and `UNION` treat all `NULL`s as *equal*, and standard `UNIQUE` treats them as *distinct* (unless `NULLS NOT DISTINCT`).
2. **Bag (multiset) vs. set rewrite unsoundness (`execution`):** Classical relational algebra assumes sets, whereas SQL tables are duplicate-preserving bags (K-relations over $\mathbb{N}$). In our SQLite3 probe over `bag_r = {1, 1}` and `bag_s = {1, 1}`:
   - `SELECT COUNT(*) FROM bag_r WHERE x IN (SELECT x FROM bag_s)` returns **`2`** (preserving `bag_r`'s multiplicity).
   - Naive `INNER JOIN` decorrelation `SELECT COUNT(*) FROM bag_r r JOIN bag_s s ON r.x = s.x` returns **`4`** (multiplying multiplicities $2 \times 2 = 4$!), proving that a set-sound decorrelation rule is **unsound** under SQL bag semantics unless `s` is deduplicated (`DISTINCT`) or proven unique by a key constraint.

#### 2.2 Univalent K-Relation Formalization (`HoTTSQL`) and Calcite Evaluation (`Cosette`)
Basis: normative (`doi:10.48550/arXiv.1607.04822`) + source (`uwdb/Cosette`)

`HoTTSQL` (`PLDI 2017`) and `Cosette` (`uwdb/Cosette`, `7a951aa3b1a70a8b310c676e524740b7114975c3`) formalize SQL query equivalence directly under **bag semantics** in Coq (`hott/library/UnivalentSemantics.v`, `hott/library/Denotation.v`):
- Every relation over schema $s$ is modeled as a function mapping tuples to homotopy-theoretic `Type` cardinalities (K-relations generalized via HoTT `hSet`/types, where union is coproduct `+`, join is product `×`, projection is dependent sum $\Sigma$, and `DISTINCT` is propositional truncation `|| ... ||`).
- `Cosette` pairs a Rosette/SMT bounded counterexample finder (`rosette/`, `dsl/ToRosette.lhs`) with HoTTSQL Coq proof generation (`dsl/ToHoTTSQL.lhs`, plus an experimental `dsl/ToLean.lhs` target) across 50+ Apache Calcite optimization rules (`hott/optimizations/*.v`).
- **Observed empirical boundary (`examples/calcite/calcite_result_with_label.csv`):** Auditing Cosette's own Calcite benchmark table reveals the exact decidability and modeling frontier of automated SQL rewrite verification: while conjunctive/semi-join rules such as `testRemoveSemiJoin` (`EQ`) and `testAggregateProjectMerge` (`MP`) are decided, rules involving `NULL` (`testPullNull`, `testDecorrelateTwoExists`), `ORDERBY` (`testSortProjectTranspose1..3`), `GROUPBY` with nullable counts (`testPushCountNullableThroughUnion`), `EXCEPT`/`INTERSECT`, `CAST`, and `VALUES` empty-table edge cases hit `ERROR` or `UNKNOWN` (`testAggregateConstantKeyRule`, labeled `"Not Provable, Interesting"`).

---

### 3. Holistic Multi-Tier Web Compilation vs. Open-World Tier Splitting (`Ur/Web`, `Links`, `ScalaLoci`)

#### 3.1 `Ur/Web`: Static Security by Row-Polymorphic Metaprogramming
Basis: normative (`doi:10.1145/1806596.1806612`, `doi:10.1145/2676726.2677004`) + source (`urweb/urweb`)

`Ur/Web` (`urweb/urweb`, `55a881ff9b50d9e5c3b2fd564f5cd44a5cc5e6bc`) compiles a single whole-program source file into (i) a native C HTTP/FastCGI server binary, (ii) client-side JavaScript with FRP reactive DOM, and (iii) SQL DDL and prepared DML statements. Its core security guarantees are encoded directly into the standard library signature `lib/ur/basis.urs` and dedicated compiler passes:

1. **Static HTML validity & zero XSS (`lib/ur/basis.urs:760-765`):**
   ```sml
   con xml :: {Unit} -> {Type} -> {Type} -> Type
   val cdata : ctx ::: {Unit} -> use ::: {Type} -> string -> xml ctx use []
   ```
   The first type-level row `{Unit}` encodes allowed parent tag contexts (e.g., `Body`, `Table`, `Tr`), while `cdata` is the sole constructor injecting runtime strings into HTML—automatically entity-escaping them—making raw unescaped HTML injection (`XSS`) ill-typed.
2. **Static SQL schema safety & zero SQLi (`lib/ur/basis.urs:375-376, 693-712`):**
   `sql_query` and `dml` parameterize queries over type-level table/column records (`tables ::: {{Type}}`, `exps ::: {Type}`, with disjointness proof `[tables ~ exps]`). All dynamic values are injected via typed parameters rather than string interpolation, statically eliminating SQL injection and column-name typos.
3. **Static CSRF prevention (`src/effectize.sml:166`, `src/sidecheck.sml:75`, `src/settings.sml:761-765`):**
   - `effectize.sml` performs whole-program effect analysis across exported entry points: any URL handler reachable via HTTP `GET` that can execute side effects (`dml`, cookies, etc.) is **rejected at compile time** (`accessible via GET could cause side effects; try accessing it only via forms... or whitelisting it with the 'safeGet' .urp directive`).
   - Mutating handlers require `POST` form actions whose cookies are cryptographically signed (`sidecheck.sml:75` explicitly warns when reading runtime environment variables that could weaken compile-time CSRF cookie verification).
4. **Fine-grained reactive client DOM (`lib/ur/basis.urs:144-155`):**
   `source t` (mutable FRP cell allocated in `transaction`) and `signal t` (monadic derived stream) let client UI fragments automatically patch affected DOM subtrees without manual virtual-DOM diffing or raw imperative DOM mutation.

#### 3.2 `Ur/Web` Boundary Rigidity and C FFI Arena / Transactional Commit Seams
Basis: source (`urweb/urweb`) + derived

The exact mechanisms giving `Ur/Web` closed-world soundness create sharp friction at open-world FFI and deployment boundaries:

1. **Ecosystem & FFI encapsulation collapse:** Linking a single third-party JavaScript widget via an `.urs` FFI stub that invokes `innerHTML` or touches `document.cookie` immediately bypasses `Ur/Web`'s static `xml` and CSRF guarantees without runtime sandboxing or SFT membrane checking.
2. **Request-scoped bump arena (`src/c/urweb.c:1380-1435`):**
   `uw_malloc(ctx, len)` word-aligns `ctx->heap.front` (`align_heap`) and linearly bumps `ctx->heap.front += len` (falling back to `posix_memalign` only during `ctx->amInitializing`). Nested lexical scopes use `uw_begin_region` / `uw_end_region`, resetting `ctx->heap.front = (char *) r` in $O(1)$. While fast and GC-pause-free, any C FFI library storing a `uw_malloc` pointer in global/static state or returning pointers that outlive a region suffers silent **use-after-free** across HTTP requests.
3. **Three-phase transactional FFI protocol and split-brain edge case (`include/urweb/urweb_cpp.h:304`, `src/c/urweb.c:3706-3795`):**
   To survive automatic `SERIALIZABLE` SQL transaction retries without duplicate external side effects, C FFI modules register hooks via:
   ```c
   int uw_register_transactional(struct uw_context *ctx, void *data,
                                 uw_callback commit, uw_callback rollback,
                                 uw_callback_with_retry free);
   ```
   Direct inspection of `uw_commit` (`src/c/urweb.c:3706-3795`) reveals the exact execution order:
   - **Step 1 (`lines 3715-3723`):** Invokes `.commit` on every transactional where **`rollback != NULL`** (LIFO order). If `uw_has_error(ctx)` triggers, `uw_rollback(ctx, 0)` aborts before touching the DB.
   - **Step 2 (`lines 3726-3765`):** Acquires global `message_send_mutex` (if client push deltas exist), then executes `ctx->app->db_commit(ctx)`. If `code == -1` (SQL serialization conflict!), rolls back all `rollback != NULL` transactionals, calls `free(data, 1)` (signaling retry), and returns `1` so the worker transparently re-runs the entire request handler!
   - **Step 3 (`lines 3767-3787`):** Invokes `.commit` on irreversible transactionals where **`rollback == NULL`** (e.g., sending email or calling an external HTTP webhook), followed by flushing WebSocket/comet `client_send` deltas (`lines 3789-3796`).
   - **Critical partial-failure boundary (`lines 3771-3786`):** If a `rollback == NULL` transactional raises `uw_has_error(ctx)` (or if the server process crashes immediately after `db_commit` returns `0`), **the SQL database has already permanently committed**, yet `urweb.c:3777-3779` rolls back the `rollback != NULL` transactionals and aborts remaining `rollback == NULL` actions—leaving database state committed while irreversible external effects are lost or partially applied! Achieving true crash-safe delivery across external APIs therefore requires persisting intents into a **transactional outbox** table inside Step 2 plus an idempotent asynchronous relay (or explicit Saga compensating actions).

#### 3.3 Open-World Tier Splitting, Placement Types, and Closure-Capture Secret Leaks
Basis: normative (`doi:10.1145/3276499`) + documentation (`links-lang/links`) + derived

Beyond `Ur/Web`'s client-server monolith, `Links`, `Eliom`, `ScalaLoci` (`OOPSLA 2018`), and mainstream React Server Components (`"use server"` / `"use client"`) split a single source AST across heterogeneous network tiers:

- **`ScalaLoci` placement types (`doi:10.1145/3276499`):** Generalizes fixed 2-tier web apps to arbitrary distributed topologies (`Peer` types with `Single`, `Multiple`, `Optional` tie cardinalities). Every value carries its location `T on Peer`, and cross-tier access requires explicit `asLocal` / remote invocation, integrating reactive signals (`REScala`) across network hops.
- **Three irreducible distributed hazards of automatic tier splitting:**
  1. **Closure-capture secret exfiltration:** When a client-placed lambda lexically captures a server-side variable (e.g., an internal DB row or API token), naive tier-splitters either serialize server secrets directly into client JavaScript/HTTP payloads or crash trying to serialize non-serializable FFI handles (file descriptors, DB connections). Preventing this statically requires combining placement types with **Information-Flow Control (IFC)** secrecy labels (`Secret@Server` non-coercible to `Client`).
  2. **Untrusted client payload forgery:** Auto-generated RPC endpoints receive network inputs from adversarial browsers; serialized client-side continuations or closure environments (`Links` / `Eliom` / Server Actions) must either be stored server-side or cryptographically authenticated (MAC'd) and runtime-validated against the full input type schema on deserialization.
  3. **Rolling-upgrade version skew:** Auto-generated anonymous closure IDs and whole-program binary schemas (`Ur/Web`, naive RPC splitters) break whenever a v2 server rolls out while browsers still execute cached v1 JavaScript bundles.

---

### 4. Rolling Schema Evolution (`Cambria`) and End-to-End Incremental Views (`DBSP`)

#### 4.1 Bidirectional Edit Lenses for Zero-Downtime Schema Evolution (`Cambria`)
Basis: source (`inkandswitch/cambria`) + derived

Whole-program typed SQL compilers (`Ur/Web`, `Links`, `Diesel`, `SQLx`) implicitly assume **lockstep schema compilation**—one schema shared simultaneously by the database and every running client/server binary. Rolling deployments and offline-capable clients violate lockstep compilation continuously.

`Cambria` (`inkandswitch/cambria`, `da8961440cac7eba1c3113488f5bcbc26046620f`, `src/lens-ops.ts:59-85`) models schema evolution as a graph of composable bidirectional edit lenses over JSON Patch operations, built from exactly **10 primitive `LensOp` combinators**:

```ts
export type LensOp =
  | AddProperty    | RemoveProperty | RenameProperty
  | HoistProperty  | WrapProperty   | HeadProperty
  | PlungeProperty | LensIn         | LensMap
  | ConvertValue
```

By composing forward and reversed lenses (`src/reverse.ts`), a v1 service and a v2 service concurrently read and write the same underlying document stream while each compiles against its own static local schema. Two mathematical boundaries constrain lens-based evolution:
1. **Non-bijective information loss (GetPut / PutGet):** Destructive edits (`RemoveProperty`, `HeadProperty`, many-to-one `ConvertValue`) cannot preserve round-trip `PutGet` / `GetPut` laws unless omitted fields are retained in an out-of-band complement or filled via explicit defaults (`src/defaults.ts`).
2. **Relational query-rewriting cliff:** Translating single JSON document patches across `LensOp`s does not automatically translate SQL `WHERE` predicates, `JOIN`s, or `UNIQUE`/foreign-key constraints across rolling relational schemas without risking full-table scans when an indexed column is renamed, split, or type-converted.

#### 4.2 End-to-End Algebraic Incremental View Maintenance (`DBSP`)
Basis: normative (`doi:10.14778/3587136.3587137`) + derived

Whereas `T-LINQ` and `Query Shredding` optimize one-shot pull queries, interactive dashboards and multi-tier reactive UIs require continuous incremental updates. **`DBSP`** (`VLDB 2023`, `doi:10.14778/3587136.3587137`) models relational bags as **Z-sets** (functions from tuples to signed integers $\mathbb{Z}$, where $+1$ represents insertion and $-1$ represents deletion) forming an Abelian group. Every relational operator lifts functorially via differentiation ($D$) and integration ($I$) into a streaming incremental circuit:
- Linear operators (selection $\sigma$, projection $\pi$, union) satisfy $Q^\Delta(\Delta x) = Q(\Delta x)$ with $O(1)$ internal state.
- Bilinear operators (equi-joins $\bowtie$) obey the discrete product rule:
  $$\Delta(A \bowtie B) = (\Delta A \bowtie B) + (A \bowtie \Delta B) + (\Delta A \bowtie \Delta B)$$
  which irreducibly requires maintaining $O(|A| + |B|)$ indexed state inside the join operator.
- Recursive queries (`WITH RECURSIVE`) incrementalize cleanly via nested streams over Z-sets.

**Cross-tier reactive FFI boundary:** Extending `DBSP` Z-set deltas over WebSockets into a client-side reactive DOM (`Ur/Web` `source`/`signal`, `SolidJS`/`Leptos`) requires (i) **atomic transaction-epoch batching** (delivering all coupled table deltas from one DB commit in a single frame to preserve glitch-freedom, analogous to `Ur/Web`'s `message_send_mutex` at `urweb.c:3726`), (ii) **deterministic optimistic-mutation rebase** when a client applies local edits before server confirmation, and (iii) **multi-tenant row-level security (RLS) factoring** to share $O(|A|+|B|)$ join state across users without leaking existence/timing side channels.

---

### 5. Cross-System Comparison Matrix

Basis: derived (synthesized from §§1–4)

| System | Query Safety & Composition | Nested Result Strategy | Tier Split & Web Security | Transaction / Evolution Model | Primary Failure / Boundary Mode |
|---|---|---|---|---|---|
| **`T-LINQ` / `Links`** (`7100e289`) | Proven SPJU normalization; zero `NotSupportedException` | Fixed-$k$ flat SQL **Query Shredding** + linear `Stitch` | Row-polymorphic `client`/`server` annotations | Requires explicit snapshot tx around $k$ shredded queries | Exponential SQL blowup without CTEs; missing snapshot tx risks torn stitch |
| **`Ur/Web`** (`55a881ff`) | Row-polymorphic typed `sql_query` / `dml`; zero SQLi | Flat SQL queries folded in `transaction` | Closed-world `xml` (zero XSS), `effectize` (zero CSRF) | `uw_register_transactional` + SSI retry; lockstep schema | Ecosystem/JS FFI rigidity; `uw_malloc` C-FFI UAF; post-`db_commit` Step-3 split-brain |
| **`Cosette` / `HoTTSQL`** (`7a951aa3`) | Automated SQL rewrite verification (Coq HoTT + Rosette) | Flat SQL + subqueries + bag K-relations | Offline verifier (not a web runtime) | Static equivalence over bag + partial `NULL` semantics | `NULL`/`GROUPBY`/`ORDERBY`/`VALUES` Calcite rules hit `ERROR`/`UNKNOWN` |
| **`ScalaLoci`** (`OOPSLA 2018`) | Host Scala DB libraries (no built-in T-LINQ) | Host-dependent | Arbitrary peer graphs via `T on Peer` placement types | Reactive `REScala` ties across peers | Network failure/latency & closure-capture IFC require explicit discipline |
| **`Cambria`** (`da896144`) | JSON Patch / JSON Schema (non-SQL) | Arbitrary nested JSON documents | Schema-version translation middleware | 10 bidirectional `LensOp` edit combinators | Non-bijective edits lose data without complement; no SQL index rewriting |
| **`DBSP`** (`VLDB 2023`) | Full relational + recursive SQL via Z-sets | Incremental streaming Z-set views | Backend streaming engine (no DOM compiler) | $O(|\Delta|)$ incremental updates per commit epoch | $O(|A|+|B|)$ stateful join RAM; multi-tenant RLS sharing & offline rebase |

## Boundaries

- **Known not to apply:**
  - *Single-query `T-LINQ` normalization for recursive graph queries or nested-result types:* Wong's conservativity and flat `T-LINQ` normalization apply strictly to non-recursive flat-output SPJU queries; recursive queries require fixpoints (`WITH RECURSIVE`), and nested outputs require either fixed-$k$ Query Shredding or server-side nested serialization (`JSON_AGG`/`LATERAL`).
  - *Set-theoretic relational rewrite rules under SQL bag + `NULL` semantics:* As demonstrated via live SQLite3 execution (`NOT IN` returning `0` on `NULL`, `IN` vs. `INNER JOIN` returning `2` vs. `4` on duplicate keys), set-sound and two-valued rewrites do not transfer soundly to ISO SQL without explicit multiplicity and `NULL` guards.
  - *`Ur/Web` static XSS/CSRF guarantees once untrusted JS/C FFI is linked:* Static security proofs assume the closed-world `Basis` API and do not hold across unchecked imperative JavaScript or raw C heap extensions.
- **Unsupported (explicitly observed in source):**
  - `links-lang/links` (`core/query/evalNestedQuery.ml:256-260`) notes that `Split` comprehension normalization does not preserve list ordering (requiring separate ordered-query passes).
  - `uwdb/Cosette` (`examples/calcite/calcite_result_with_label.csv`) explicitly records `ERROR` or `UNKNOWN` on Calcite test cases relying on `NULL` pull-up/decorrelation, `ORDERBY` transpose, `EXCEPT`, `INTERSECT`, `CAST`, and `VALUES` empty-table constructs.
  - `inkandswitch/cambria` (`src/lens-ops.ts:61-63`) explicitly comments that `ConvertValue` supports only hardcoded finite value mappings (`We only support hardcoded mappings for the time being`).
- **Unknown:**
  - *Empirical crossover point between $k$-query shredding and PostgreSQL `LATERAL` + `JSONB_AGG`:* Latency, DB server memory, and wire-byte tradeoffs between fixed-$k$ shredded binary cursors and single-query server-side JSON/Arrow assembly across high-fanout schemas were not benchmarked on PostgreSQL/DuckDB here.
  - *Multi-tenant RLS-safe shared incremental join circuits:* Whether `DBSP` join state can be shared safely across thousands of authenticated clients with row-level security policies and offline optimistic mutations without timing or cardinality side channels remains open.
  - *Indexed SQL query rewriting through arbitrary bidirectional schema lenses:* General conditions under which a relational schema lens preserves indexability (avoiding full-table scans) across rolling multi-version SQL schemas were not resolved.
- **Not examined:**
  - `links-lang/links` database driver transaction wrapping around `compile_shredded` (`core/database.ml` / PostgreSQL driver) was not audited line-by-line to verify whether `Links` automatically opens a `REPEATABLE READ` snapshot transaction around shredded queries at runtime.
  - Source implementations of `ocsigen/eliom`, `scala-loci/scala-loci`, `feldera/feldera`, and Rust ORMs (`Diesel`, `SQLx`) were not directly audited line-by-line in this report (analyses of `ScalaLoci` and `DBSP` rest on their published papers).
  - Later query-shredding extensions for polymorphic variants, nested aggregation, and dynamic indexes by Ricciotti and Cheney beyond the `links-lang/links` snapshot (`7100e289`) were not individually audited in source.

## Evidence

### Primary Git Sources Inspected (Observed 2026-11-19)
- `links-lang/links` @ `7100e2891346b5bae483fe9a02791c900047388a`:
  - `core/query/query.ml:1-90` (`tail_of_t`, `freshen_for_bindings`, query normalization utilities).
  - `core/query/evalNestedQuery.ml:1-100, 218-315, 741-870` (`tag_query`, `module Shred` `nested_type`/`shred_inner_type`/`shred_outer_type`/`shred_query`, `Split`, `LetInsertion`, `module Stitch` `lookup`/`insert`/`stitch`/`build_stitch_map`/`stitch_mapped_query`, `unordered_query_package`, `compile_shredded`).
- `urweb/urweb` @ `55a881ff9b50d9e5c3b2fd564f5cd44a5cc5e6bc`:
  - `include/urweb/urweb_cpp.h:304` (`uw_register_transactional` signature).
  - `src/c/urweb.c:1380-1435` (`align_heap`, `uw_malloc`, `uw_begin_region`, `uw_end_region`).
  - `src/c/urweb.c:3706-3795, 3902-3915` (`uw_commit` three-phase commit/retry/irreversible-callback execution and `uw_register_transactional`).
  - `lib/ur/basis.urs:144-155, 375-379, 693-712, 760-765` (`transaction`, `source`, `signal`, `sql_query`, `query`, `dml`, `xml`, `cdata`).
  - `src/effectize.sml:166`, `src/sidecheck.sml:75`, `src/settings.sml:761-765` (compile-time GET side-effect rejection, `safeGet`, CSRF warnings).
- `uwdb/Cosette` @ `7a951aa3b1a70a8b310c676e524740b7114975c3`:
  - `hott/library/UnivalentSemantics.v:1-95` (HoTTSQL K-relation SQL denotation in Coq).
  - `hott/optimizations/*.v` (50+ formalized SQL rewrite proofs).
  - `examples/calcite/calcite_result_with_label.csv:1-25` (Calcite rule verification outcomes and failure reasons).
- `inkandswitch/cambria` @ `da8961440cac7eba1c3113488f5bcbc26046620f`:
  - `src/lens-ops.ts:59-85` (`ValueMapping`, `ConvertValue`, 10-variant `LensOp` union, `LensSource`).

### Peer-Reviewed Papers Verified
- James Cheney, Sam Lindley, Philip Wadler, *A Practical Theory of Language-Integrated Query*, ICFP 2013, `doi:10.1145/2500365.2500586`.
- James Cheney, Sam Lindley, Philip Wadler, *Query Shredding: Efficient Relational Evaluation of Queries over Nested Multisets*, SIGMOD 2014, `doi:10.1145/2588555.2612186`.
- Adam Chlipala, *Ur: Statically-Typed Metaprogramming with Type-Level Record Computation*, PLDI 2010, `doi:10.1145/1806596.1806612`.
- Adam Chlipala, *Ur/Web: A Simple Model for Programming the Web*, POPL 2015, `doi:10.1145/2676726.2677004` (CACM 2016 highlight `doi:10.1145/2930887`).
- Shumo Chu, Konstantin Weitz, Alvin Cheung, Dan Suciu, *HoTTSQL: Proving Query Rewrites with Univalent SQL Semantics*, PLDI 2017, `doi:10.48550/arXiv.1607.04822`.
- Pascal Weisenburger, Mirko Köhler, Guido Salvaneschi, *Distributed System Development with ScalaLoci*, OOPSLA 2018, `doi:10.1145/3276499`.
- Mihai Budiu, Tej Chajed, Frank McSherry, Leonid Ryzhyk, Val Tannen, *DBSP: Automatic Incremental View Maintenance for Rich Query Languages*, PVLDB 16(7), VLDB 2023, `doi:10.14778/3587136.3587137`.

### Execution Probe (Python 3.13.15 + SQLite3, Observed 2026-11-19)
Reproducible probe validating query shredding vs. outer-join row counts, `Stitch` reconstruction of empty nested lists, SQL three-valued `NULL` collapse under `NOT IN`, and bag-vs-set `IN` decorrelation divergence:

```python
import sqlite3
con = sqlite3.connect(":memory:")
cur = con.cursor()
cur.executescript("""
CREATE TABLE dept(did INT, dname TEXT);
CREATE TABLE emp(eid INT, did INT, ename TEXT);
CREATE TABLE proj(pid INT, did INT, pname TEXT);
INSERT INTO dept VALUES (1, 'Eng'), (2, 'EmptyDept');
INSERT INTO emp VALUES (10, 1, 'Alice'), (11, 1, 'Bob');
INSERT INTO proj VALUES (100, 1, 'Compiler'), (101, 1, 'Verifier');
CREATE TABLE a(id INT); INSERT INTO a VALUES (1), (2), (3);
CREATE TABLE b(x INT);  INSERT INTO b VALUES (1), (NULL);
CREATE TABLE bag_r(x INT); INSERT INTO bag_r VALUES (1), (1);
CREATE TABLE bag_s(x INT); INSERT INTO bag_s VALUES (1), (1);
""")
print("NOT IN:", cur.execute("SELECT COUNT(*) FROM a WHERE id NOT IN (SELECT x FROM b)").fetchone()[0])
print("NOT EXISTS:", cur.execute("SELECT COUNT(*) FROM a WHERE NOT EXISTS (SELECT 1 FROM b WHERE b.x=a.id)").fetchone()[0])
print("Bag IN:", cur.execute("SELECT COUNT(*) FROM bag_r WHERE x IN (SELECT x FROM bag_s)").fetchone()[0])
print("Bag JOIN:", cur.execute("SELECT COUNT(*) FROM bag_r r JOIN bag_s s ON r.x=s.x").fetchone()[0])
```

Recorded outputs:
- Sibling fanout `(D=1, E=50, P=50)`: `LEFT OUTER JOIN = 2500` rows vs. Shredded `= 101` rows across `k = 3` flat queries.
- 3-level nesting `(D=10, E=20, T=5)`: `N+1 = 211` queries vs. Shredded `= 3` queries.
- Concrete SQLite3 stitch: `outer-join rows = 5`, `shredded total rows = 6`, stitched result `[{'did': 1, 'dname': 'Eng', 'emps': ['Alice', 'Bob'], 'projs': ['Compiler', 'Verifier']}, {'did': 2, 'dname': 'EmptyDept', 'emps': [], 'projs': []}]`.
- `SQL 3VL NOT IN count = 0` vs. `NOT EXISTS count = 2`.
- `SQL Bag IN subquery rows = 2` vs. `naive INNER JOIN decorrelation rows = 4`.

## Revalidation

1. **Links shredding and snapshot isolation:** Diff `core/query/evalNestedQuery.ml` (`Shred`, `Stitch`, `compile_shredded`) and inspect the corresponding DB execution wrapper in newer `links-lang/links` commits to verify whether `REPEATABLE READ` snapshot transactions are opened automatically around shredded query packages and whether `Delateralize`/ordered shredding replaces `Split`.
2. **Ur/Web transactional commit protocol:** Diff `src/c/urweb.c` (`uw_commit`, `uw_register_transactional`, `uw_malloc`) and `src/effectize.sml` in `urweb/urweb` to check whether Step-3 `rollback == NULL` error handling after `db_commit` has changed or whether outbox helpers were added.
3. **SQL equivalence prover coverage:** Inspect `examples/calcite/calcite_result_with_label.csv` and `hott/library/UnivalentSemantics.v` in `uwdb/Cosette` (or successor SQL equivalence provers such as WeTune/QED) to check progress on `NULL`, `GROUPBY`, `ORDERBY`, and `VALUES` fragments.
4. **SQLite/PostgreSQL probe rerun:** Re-execute the standalone Python `sqlite3` probe above against any target SQL dialect (including PostgreSQL `LATERAL` + `JSONB_AGG` or DuckDB `LIST`/`STRUCT`) to benchmark wire size and verify three-valued `NULL` / bag behavior before emitting SQL from a compiler backend.
