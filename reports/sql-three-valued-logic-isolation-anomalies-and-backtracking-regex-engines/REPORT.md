# SQL Three-Valued Logic, Bag Semantics, MVCC Isolation Anomalies, and Backtracking vs Linear-Time Regex Engines

## Summary

Two ubiquitous declarative domain-specific languages—**SQL** and **regular expressions**—deceive developers, query optimizers, and static/SMT verification tools because their industrial semantics violate foundational mathematical abstractions (Boolean set algebra, serializable transactions, and regular-language finite automata):

1. **SQL Three-Valued Logic (`NULL`) & Clause Asymmetry**: SQL evaluates predicates under Strong Kleene three-valued logic ($K_3 = \{\mathbf{T}, \mathbf{F}, \mathbf{U}\}$), breaking the Law of Excluded Middle (`val = 10 OR val != 10` omits `NULL`), breaking De Morgan / negation assumptions, and turning `x NOT IN (subquery)` into a **0-row annihilator** whenever the subquery returns *any* `NULL`. Crucially, SQL applies opposite acceptance polarities across clauses: `WHERE`/`HAVING`/`ON` require $\mathbf{T}$ (rejecting $\mathbf{U}$), whereas `CHECK (...)` constraints reject only $\mathbf{F}$ (silently **accepting** $\mathbf{U}$, so `CHECK (val > 0)` admits `NULL`!). Simultaneously, `GROUP BY`, `DISTINCT`, `INTERSECT`, and `EXCEPT` use two-valued *distinctness* (`IS NOT DISTINCT FROM`, coalescing `NULL`s) while `UNIQUE` permits multiple `NULL`s by default.
2. **Bag (Multiset) Relational Algebra & HoTTSQL/Cosette (`uwdb/Cosette`)**: SQL relations are **bags**, not sets, so classical set equivalences fail ($\sigma_{p \lor q}(R) \neq \sigma_p(R) \cup_{\text{bag}} \sigma_q(R)$ doubles rows satisfying $p \land q$; `COUNT` decorrelation fails on empty groups). HoTTSQL (`UnivalentSemantics.v`, PLDI 2017) models relations as K-relations `Tuple s -> Type`, projection as dependent sum $\Sigma$, and `DISTINCT` as homotopy propositional truncation `merely`, enabling machine-checked query-rewrite verification in Coq and SMT-backed counterexample synthesis in Cosette.
3. **MVCC Isolation Anomalies & PL/pgSQL Triggers (`postgres/postgres`)**: ANSI SQL isolation levels fail to classify MVCC anomalies (Berenson et al. SIGMOD 1995; Adya et al. ICDE 2000). Under PostgreSQL **Read Committed**, concurrent updates trigger `EvalPlanQual` (`execMain.c`), re-evaluating *only* the modified target tuple against the newly committed version while join/subquery inputs and `BEFORE`/`AFTER` triggers (`trigger.c`) observe mixed snapshots—creating lost updates, split-brain reads, and repeated trigger executions. Under **Snapshot Isolation** (`REPEATABLE READ`), disjoint writes over mutually read sets produce **Write Skew (`A5B`)** and **Read-Only Anomalies**; PostgreSQL's `SERIALIZABLE` mode implements Cahill et al.'s Serializable Snapshot Isolation (SSI, `predicate.c`) by tracking `SIREAD` predicate locks and aborting dangerous `T1 --rw--> T2 --rw--> T3` structures.
4. **Backtracking Regex Engines (`ECMA-262`, `PCRE2`, `V8 Irregexp`, Python `re`) vs Linear-Time Automata (`google/re2`, `rust-lang/regex`)**:
   - Industrial backtracking regexes use **ordered leftmost-first alternation** (not POSIX longest-match: `/(aa|aabaac|ba|b|c)*/` on `"aabaac"` yields `"aaba"`, not `"aabaac"`), exhibit subtle cross-engine **capture-reset divergences** inside loops (on `^(?:(a)|b)*$` against `"ab"`, ECMA-262 `RepeatMatcher` and Perl 5.40 reset group 1 to `undefined`/`undef`, whereas Python `re` retains `'a'`), and break regularity via **backreferences** (`\1`, NP-complete; ECMA-262 itself encodes unary $\gcd$ in a regex!) and **lookarounds**.
   - Ambiguous quantifiers (`^(a+)+b$`) induce $\Omega(2^n)$ **catastrophic backtracking (`ReDoS`)**: verified live on `"a"*26 + "!"` taking `4565.7 ms` in Python `re` and `650.7 ms` in Node V8 Irregexp (~$4\times$ growth per $+2$ characters), versus `0.037 ms` (and `5.2 ms` for $n=10000$) in a Thompson NFA.
   - **Google RE2** (`nfa.cc`, `dfa.cc`, `bitstate.cc`) and **Rust `regex-automata`** (`strategy.rs`, `hybrid/dfa.rs`, `pikevm.rs`) omit backreferences and lookaround to guarantee strict $O(m \cdot n)$ worst-case matching via layered prefilters, bounded-cache Lazy DFAs, OnePass DFAs, memoized BoundedBacktrackers, and Thompson/PikeVM fallbacks (and V8 added a non-backtracking `NfaInterpreter` experimental engine for the linear-time subset).

## Applicability

This report is aimed at compiler/query-optimizer engineers, SMT/formal-verification authors modeling SQL or regex semantics, database application architects writing triggers/constraints under MVCC, and security engineers mitigating ReDoS or parser differentials across regex engines.

- **Subject relationships**:
  - **SQLite 3.53.4** (`sqlite/sqlite` @ `ec00a487...`, live local execution) demonstrates standard SQL 3VL (`CHECK`, `NOT IN`, `GROUP BY`, `UNIQUE`, aggregates) and bag-vs-set behavior.
  - **HoTTSQL / Cosette** (`uwdb/Cosette` @ `7a951aa3...`, PLDI 2017 DOI `10.1145/3062341.3062348`) supplies the mechanized bag-relational semantics (`hott/library/UnivalentSemantics.v`).
  - **PostgreSQL** (`postgres/postgres` @ `2c077c7d...`) supplies concrete MVCC concurrency, Read Committed `EvalPlanQual` (`execMain.c`), trigger lifecycle (`trigger.c`), and SSI `SIREAD` conflict tracking (`predicate.c`), contextualized against Berenson et al. (SIGMOD 1995), Adya et al. (ICDE 2000), and Cahill et al. (SIGMOD 2008).
  - **ECMA-262** (`tc39/ecma262` @ `b1eaed82...`), **V8** (`v8/v8` @ `e88118f6...`, tested via Node.js `v24.21.0`), **PCRE2** (`PCRE2Project/pcre2` @ `0705b4a3...`), Python 3 `re`, and Perl `v5.40.1` characterize backtracking regex semantics and ReDoS, contrasted directly against **Google RE2** (`google/re2` @ `2da00568...`) and **Rust `regex` / `regex-automata`** (`rust-lang/regex` @ `fde4946d...`).
- **Scope and dialect qualifications**:
  - SQL 3VL rules shown apply across ISO SQL:2023, PostgreSQL, SQLite, MySQL, and DuckDB, except where noted (e.g., Oracle notoriously conflates empty string `''` with `NULL`; PostgreSQL 15+ and SQL:2023 support opt-in `UNIQUE NULLS NOT DISTINCT`).
  - PostgreSQL's `EvalPlanQual` and `SIREAD` SSI mechanics are PostgreSQL-specific implementations of Read Committed and Serializable isolation (contrasted against MySQL InnoDB's gap-locking `REPEATABLE READ` and SQLite's single-writer WAL serialization).
  - Regex execution probes ran on Linux x86-64 with Python 3 `re`, Node.js `v24.21.0` (V8 Irregexp), and Perl `v5.40.1`; PCRE2, RE2, and Rust `regex` internals were inspected at pinned source revisions without compiling local C/Rust binaries.

## Findings

### 1. SQL Three-Valued Logic (`NULL`) and Semantic Inconsistencies

#### 1.1 Strong Kleene Logic ($K_3$) and Classical Equivalence Failures

Basis: normative (ISO SQL) + execution (`SQLite 3.53.4`, Probe A)

SQL evaluates boolean expressions containing `NULL` over the Strong Kleene three-valued lattice $\{\mathbf{F} < \mathbf{U} < \mathbf{T}\}$ where $\text{AND} = \min$, $\text{OR} = \max$, $\text{NOT}(\mathbf{T}) = \mathbf{F}$, $\text{NOT}(\mathbf{F}) = \mathbf{T}$, and $\text{NOT}(\mathbf{U}) = \mathbf{U}$:

| $P$ | $Q$ | $P \land Q$ | $P \lor Q$ | $\neg P$ |
| :--- | :--- | :--- | :--- | :--- |
| $\mathbf{T}$ | $\mathbf{U}$ | **$\mathbf{U}$** | **$\mathbf{T}$** | $\mathbf{F}$ |
| $\mathbf{F}$ | $\mathbf{U}$ | **$\mathbf{F}$** | **$\mathbf{U}$** | $\mathbf{T}$ |
| $\mathbf{U}$ | $\mathbf{U}$ | **$\mathbf{U}$** | **$\mathbf{U}$** | **$\mathbf{U}$** |

Every comparison operator (`=`, `<>`, `<`, `<=`, `>`, `>=`) with a `NULL` operand yields $\mathbf{U}$ (`NULL = NULL` is $\mathbf{U}$, `NULL <> NULL` is $\mathbf{U}$). Consequently, classical Boolean identities fail:
- **Law of Excluded Middle fails**: `val = 10 OR val != 10` evaluates to $\mathbf{U} \lor \mathbf{U} = \mathbf{U}$ when `val IS NULL`. In Probe A on `SQLite 3.53.4`, `SELECT id FROM items WHERE val = 10 OR val != 10` omitted `id = 3` (`val = NULL`), returning only `[(1,), (2,), (4,)]`.
- **Law of Non-Contradiction fails**: `NOT (val = 10)` evaluates to $\mathbf{U}$ (rejected by `WHERE`) when `val IS NULL`, so partitioning a table by `WHERE P` and `WHERE NOT P` silently drops every row where `P` is $\mathbf{U}$!
- **`NOT IN` annihilation**: `x NOT IN (SELECT y FROM S)` is normatively equivalent to `ALL (x <> y)` = $\bigwedge_{y \in S} (x \neq y)$. If $S$ contains even a single `NULL`, then for any $x$ not equal to a non-null element of $S$, the conjunction is $\mathbf{T} \land \dots \land \mathbf{U} = \mathbf{U}$, which `WHERE` rejects!
  - Verified in Probe A (`items` has `val ∈ {10, 10, NULL, 20}`, `banned` has `{10, NULL}`):
    - `SELECT id, val FROM items WHERE val NOT IN (SELECT val FROM banned)` -> **`[]` (0 rows!)** (even `val = 20` disappears!).
    - `SELECT id, val FROM items i WHERE NOT EXISTS (SELECT 1 FROM banned b WHERE b.val = i.val)` -> **`[(3, None), (4, 20)]`** (two-valued `EXISTS` returns $\mathbf{F}$ on empty match, so `NOT EXISTS` returns $\mathbf{T}$!).
  - **Optimizer / SMT pitfall**: Rewriting `NOT EXISTS (SELECT 1 FROM S WHERE S.y = R.x)` to `R.x NOT IN (SELECT y FROM S)` (or vice versa) is **unsound** unless *both* `R.x` and `S.y` are provably `NOT NULL`!

#### 1.2 Clause Polarity Inversion and Equality vs Distinctness Split

Basis: normative (ISO SQL) + execution (`SQLite 3.53.4`, Probe A)

SQL does **not** apply a single interpretation of `NULL` or $\mathbf{U}$ across language constructs; instead it mixes three incompatible semantics:

| SQL Construct | Treatment of `UNKNOWN` / `NULL` | Verified Result in Probe A (`SQLite 3.53.4`) | Consequence for Verification & Invariants |
| :--- | :--- | :--- | :--- |
| `WHERE P` / `HAVING P` / `JOIN ON P` | **Accept iff $\mathbf{T}$** (drops $\mathbf{F}$ and $\mathbf{U}$) | `WHERE val = 10 OR val != 10` drops `id=3 (NULL)` | Predicates act as `IS TRUE(P)` |
| `CHECK (P)` table/column constraint | **Reject iff $\mathbf{F}$** (**accepts $\mathbf{T}$ and $\mathbf{U}$!**) | `val INT CHECK (val > 0)` **accepted** `(3, NULL, NULL)`! | `CHECK (x > 0)` does NOT imply `x > 0` without explicit `NOT NULL`! |
| `GROUP BY`, `DISTINCT`, `UNION`, `INTERSECT`, `EXCEPT`, `IS NOT DISTINCT FROM` | **Two-valued distinctness**: all `NULL`s are equal (`NOT DISTINCT`) | `GROUP BY grp` merged `(3, NULL, NULL)` and `(4, NULL, 20)` into one `(None, ...)` group | `GROUP BY` disagrees with `=`; self-join on `a.grp = b.grp` loses `NULL` groups |
| `UNIQUE` constraint (default) | **Distinct-nulls**: `NULL` is treated as distinct from `NULL` | `CREATE TABLE uq (k INT UNIQUE); INSERT (NULL), (NULL)` succeeded (`COUNT(*) = 2`) | `UNIQUE` does not enforce singleton `NULL` unless SQL:2023 `UNIQUE NULLS NOT DISTINCT` is used |
| Aggregates (`COUNT(*)`, `COUNT(col)`, `SUM(col)`) | `COUNT(*)` counts `NULL`s (`0` on empty); `COUNT(col)` skips `NULL`s (`0` on empty); `SUM`/`AVG`/`MIN`/`MAX` skip `NULL`s and return **`NULL`** on empty input | Empty table `SELECT COUNT(*), COUNT(val), SUM(val)` -> `(0, 0, None)`; NULL-group `COUNT(*)=2, COUNT(val)=1, SUM(val)=20` | Replacing `SUM(x)` over empty group with `0` is unsound without `COALESCE`; causes the classic Kim/Ganski-Wong `COUNT` decorrelation bug |

---

### 2. Bag vs Set Relational Algebra, HoTTSQL, and Cosette

Basis: source (`uwdb/Cosette` @ `7a951aa3b1a70a8b310c676e524740b7114975c3`, `hott/library/UnivalentSemantics.v` L50–67, L115–201) + documentation (Chu, Weitz, Cheung, Suciu, PLDI 2017, DOI `10.1145/3062341.3062348`) + execution (Probe A)

Textbook relational algebra operates over **sets**, whereas SQL operates over **bags (multisets)** unless `DISTINCT` or a set operator (`UNION`, `INTERSECT`, `EXCEPT` without `ALL`) is applied.

**Concrete set-algebra rewrites that are UNSOUND under SQL bag semantics**:
1. **Disjunction splitting**: Under set semantics, $\sigma_{P \lor Q}(R) = \sigma_P(R) \cup \sigma_Q(R)$. Under SQL bag semantics (`UNION ALL`), any tuple satisfying $P \land Q$ is **duplicated**! Verified in Probe A (`SQLite 3.53.4`): `SELECT COUNT(*) FROM items WHERE val >= 10 OR val <= 20` returns `3`, whereas `UNION ALL` of the two selections returns `6`!
2. **Selection / `DISTINCT` / Join commuting**: Pushing `DISTINCT` below a projection or across an outer/inner join changes multiplicities unless functional dependencies or primary keys preserve injectivity.
3. **Correlated `COUNT` subquery decorrelation (Kim's bug, 1982)**: Flattening `SELECT a FROM R WHERE R.k = (SELECT COUNT(*) FROM S WHERE S.x = R.x)` into an *inner* `JOIN ... GROUP BY` drops rows of `R` whose matching `S` group is empty (`COUNT(*) = 0`), requiring a `LEFT OUTER JOIN` plus `COUNT(S.non_null_col)` (NOT `COUNT(*)`, which would count the single `NULL`-padded outer-join row as `1`!).

**HoTTSQL Univalent K-Relation Semantics (`uwdb/Cosette`, `hott/library/UnivalentSemantics.v` L62–66, L115–181)**:
Rather than fixing multiplicities to finite `Tuple s -> nat` (which breaks infinite-domain projection sums), HoTTSQL generalizes Green-Karvounarakis-Tannen K-relations into Homotopy Type Theory by interpreting a relation as a **type family over tuples**:
```coq
Definition Relation s := Tuple s -> Type.
Definition Query Γ s := Tuple Γ -> Relation s.
```
Each SQL operator maps directly to a HoTT type constructor (`UnivalentSemantics.v` L165–180):
- **Bag Union (`union a0 a1`)**: coproduct (`a0 g t + a1 g t`, summing cardinalities);
- **Cartesian Product (`product a0 a1`)**: Cartesian product (`a0 g (fst t) * a1 g (snd t)`, multiplying cardinalities);
- **Projection (`project proj a`)**: dependent sum $\Sigma$ (`∑ t, denoteSQL a g t * BuildhProp (denoteProj proj (g, t) = t')`, summing multiplicities across every preimage tuple $t$);
- **`DISTINCT` (`distinct a`)**: **propositional truncation** (`merely (denoteSQL a g t)` = $\| \llbracket a \rrbracket(g, t) \|_{-1}$, collapsing any inhabited multiplicity type into a singleton `hProp`, i.e., exact bag-to-set coercion!);
- **`EXISTS` (`inhabited a`)**: `hexists (fun t => denoteSQL a g t)` (`hProp`).

Under the **Univalence Axiom**, two SQL queries $Q_1, Q_2$ are equivalent iff for every environment $g$ and output tuple $t$, their multiplicity types are equivalent ($\llbracket Q_1 \rrbracket(g, t) \simeq \llbracket Q_2 \rrbracket(g, t)$), which reduces to exact cardinality equality on finite bags while allowing algebraic proofs of correlated subqueries, magic-set rewrites (`hott/optimizations/Magic.v`), and aggregate pull-up/push-down (`PullAggregateThroughUnion.v`, `PushFilterPastAgg.v`). **Cosette** pairs this Coq proof backend with a Rosette/Z3 SMT bounded symbolic counterexample finder so inequivalent rewrites fail fast with concrete small counterexample tables.

---

### 3. MVCC Isolation Anomalies, PostgreSQL `EvalPlanQual`, `SSI`, and PL/pgSQL Triggers

#### 3.1 ANSI SQL Isolation Phenomena vs Adya Generalized Isolation Taxonomy

Basis: documentation (Berenson et al. SIGMOD 1995 DOI `10.1145/223784.223785`; Adya et al. ICDE 2000 DOI `10.1109/ICDE.2000.839388`; Cahill et al. SIGMOD 2008 DOI `10.1145/1376616.1376715`) + source (`postgres/postgres` @ `2c077c7d...`)

ANSI SQL-92 defined isolation levels solely in terms of three lock-centric phenomena (*Dirty Read* `P1`, *Non-Repeatable Read* `P2`, *Phantom* `P3`), leaving out **Lost Update (`P4`)**, **Read Skew (`A5A`)**, and **Write Skew (`A5B`)**. Adya et al. (ICDE 2000) replaced lock-based definitions with implementation-independent Direct Serialization Graph (`DSG`) cycles over `ww` (write-write), `wr` (write-read), and `rw` (read-write antidependency) edges:

| Anomaly | Adya Cycle / Pattern | Prevented by PostgreSQL `READ COMMITTED`? | Prevented by PostgreSQL `REPEATABLE READ` (SI)? | Prevented by PostgreSQL `SERIALIZABLE` (SSI)? |
| :--- | :--- | :--- | :--- | :--- |
| **Dirty Write (`G0`)** | `ww` cycle of uncommitted writes | Yes (row locks) | Yes (row locks) | Yes |
| **Dirty Read (`G1a/b/c`)** | Reading aborted/intermediate writes or `ww`/`wr` cycle | Yes (MVCC snapshots) | Yes (MVCC snapshots) | Yes |
| **Non-Repeatable Read / Fuzzy Read** | Second `SELECT` in same txn sees newer committed row | **No** (new snapshot per statement) | Yes (single txn snapshot) | Yes |
| **Lost Update (`P4` / `P4C`)** | `T1` reads $x$, `T2` reads $x$, `T2` writes $x$ & commits, `T1` writes $x$ blindly | **No** (unless `UPDATE` re-evaluates or uses `SELECT FOR UPDATE`) | **Yes** (`First-Committer-Wins` serialization failure `40001`) | Yes |
| **Write Skew (`A5B` / `G2-item`)** | `T1` reads $x$, `T2` reads $y$, `T1` writes $y$, `T2` writes $x$ (`T1 --rw--> T2 --rw--> T1`) | **No** | **No!** (Disjoint write sets pass First-Committer-Wins!) | **Yes** (`SIREAD` dangerous-structure abort `40001`) |
| **Read-Only Anomaly** | `T3` (RO) sees inconsistent interleaving of `T1 --rw--> T2` | **No** | **No!** (Fekete et al. 2004) | **Yes** (PostgreSQL `DEFERRABLE` RO / SSI tracking) |

#### 3.2 PostgreSQL Read Committed `EvalPlanQual` (EPQ) and PL/pgSQL Trigger Anomalies

Basis: source (`postgres/postgres` @ `2c077c7d602dba034e209227ea04a14b10797c42`, `src/backend/executor/execMain.c` L2713–2730, L2869–2885; `src/backend/commands/trigger.c` L97–108, L3017–3032)

Under PostgreSQL's default **Read Committed** isolation level, each top-level SQL statement takes a fresh MVCC snapshot $S_1$. When an `UPDATE`, `DELETE`, `MERGE`, or `SELECT FOR UPDATE` locates a target tuple $t$ visible under $S_1$ and attempts to lock/modify it, a concurrent transaction $T_c$ may have already modified and committed a newer version $t'$ (visible only at $S_2 > S_1$). Instead of aborting, PostgreSQL invokes **`EvalPlanQual` (`EPQ`, `execMain.c` L2714–2726)**:
1. EPQ follows the tuple update chain (`ctid`) to the latest committed version $t'$;
2. It spins up a sub-plan recheck (`EvalPlanQualBegin`), replacing **only the target relation's tuple** with $t'$ while retaining the **original snapshot $S_1$** for all other scanned/joined tables (or rowmark slots fetched via `EvalPlanQualFetchRowMark`, `execMain.c` L2869–2884) and **without re-evaluating `WHERE` subqueries**!
3. If $t'$ still satisfies the `WHERE` predicate under this **hybrid chimeric state** ($t'$ from $S_2$ joined against $S_1$), the `UPDATE` proceeds—even though no single consistent database snapshot ever contained that combination of rows!

**PL/pgSQL Trigger Hazards (`src/backend/commands/trigger.c` L3017–3032)**:
- **Multiple `BEFORE` trigger invocations per row**: When `ExecBRUpdateTriggers` (`trigger.c` L3017) fires on a row that hits a concurrent update race, PostgreSQL can fire the `BEFORE UPDATE` trigger, detect `TM_Updated` when attempting the heap lock/update, run `EvalPlanQual` to fetch the new tuple $t'$, and **re-fire the `BEFORE UPDATE` trigger a second time** on $t'$! Any side effect inside a `BEFORE` trigger (audit log insertion via `dblink`, sequence increments `nextval()`, advisory side tables) executes **twice** or against stale `OLD` values.
- **Snapshot drift inside `BEFORE` / `AFTER` triggers**: Inside a PL/pgSQL trigger function executing under Read Committed, each nested SQL query (`SELECT`, `UPDATE`) takes its **own brand-new snapshot** (advancing past the triggering statement's snapshot!), whereas a `BEFORE` trigger mutating `NEW` cannot see subsequent row updates of the same multi-row `UPDATE` statement; conversely, `AFTER` triggers are queued via `AfterTriggerSaveEvent` (`trigger.c` L97–105) and run after all rows of the statement (or at `COMMIT` for `DEFERRABLE INITIALLY DEFERRED` constraint triggers), observing the post-statement heap state—yet under Read Committed, two concurrent transactions enforcing a cross-row invariant (e.g., "at least one doctor on call" or "account total $\ge 0$") in `AFTER` triggers **still suffer Write Skew** because neither sees the other's uncommitted row!

#### 3.3 Serializable Snapshot Isolation (SSI) in PostgreSQL (`predicate.c`)

Basis: source (`postgres/postgres` @ `2c077c7d...`, `src/backend/storage/lmgr/predicate.c` L27–43, L1725–1741) + documentation (Cahill, Röhm, Fekete, SIGMOD 2008, DOI `10.1145/1376616.1376715`)

PostgreSQL implements true serializability (`SET TRANSACTION ISOLATION LEVEL SERIALIZABLE`) without two-phase read locks via **Serializable Snapshot Isolation (SSI)** (`predicate.c` L27–43):
- Every read acquires a non-blocking in-memory **`SIREAD` predicate lock** covering either the tuple, heap page, index range, or entire relation (escalating coarseness when lock RAM approaches capacity, `L34–42`).
- Every write checks overlapping `SIREAD` locks to record **`rw-antidependency` edges** (`T1 --rw--> T2`, meaning `T1` read a version overwritten by `T2`, so `T1` must serialize *before* `T2`).
- By Cahill et al.'s theorem, every non-serializable cycle under Snapshot Isolation contains a **dangerous structure** of two consecutive `rw`-antidependencies `T1 --rw--> T2 --rw--> T3` where `T3` commits first (pivot `T2`). PostgreSQL aborts one participating transaction with SQLSTATE `40001` (`serialization_failure`) upon detecting this structure (yielding occasional **false-positive** aborts due to coarse page/relation lock escalation or non-cyclic `T1 --rw--> T2 --rw--> T3` chains, which applications must handle via idempotent retry loops).
- **Safe read-only optimization (`predicate.c` L1725–1737)**: A `READ ONLY` transaction starting when `PredXact->WritableSxactCount == 0` cannot participate in a dangerous structure and skips SSI tracking entirely (`DEFERRABLE` read-only transactions wait once for a safe snapshot and then run with zero `40001` aborts).

---

### 4. Backtracking Regex Engines, Non-Regularity, Catastrophic ReDoS, and Linear-Time Automata

#### 4.1 Backtracking Operational Semantics and Cross-Engine Divergences

Basis: normative (`tc39/ecma262` @ `b1eaed82...`, `spec.html` L37975–38034) + source (`PCRE2Project/pcre2` @ `0705b4a3...`, `src/pcre2_match.c` L925–928, L5933–5948) + execution (Probe B-1 on Python 3 `re`, Node.js `v24.21.0` V8 Irregexp, Perl `v5.40.1`)

Backtracking regex engines (ECMA-262 / V8 Irregexp, PCRE2, Perl, Python `re`, Java `java.util.regex`, Ruby Onigmo) do **not** implement classical mathematical regular expressions or POSIX ERE leftmost-longest matching; they implement a **recursive depth-first search (DFS) continuation machine** with explicit priority rules:

1. **Ordered Leftmost-First Alternation (Not Leftmost-Longest)**:
   As normatively illustrated in ECMA-262 (`spec.html` L38022–38030), `/(aa|aabaac|ba|b|c)*/.exec("aabaac")` returns **`["aaba", "ba"]`**, NOT `["aabaac", "aabaac"]`: the first branch `"aa"` succeeds immediately on iteration 1, then `"ba"` succeeds on iteration 2, and greedy choice-point ordering commits without backtracking unless the *sequel* fails!
2. **Empty-Match Quantifier Termination (`RepeatMatcher`, `spec.html` L37994)**:
   To prevent infinite loops on nullable subexpressions like `(a*)*`, ECMA-262 `RepeatMatcher` (`step-repeatmatcher-done`, `L37994`) checks: `If min = 0 and y.[[EndIndex]] = matchState.[[EndIndex]], return ~failure~`, forcing termination of zero-width iterations once `min` is satisfied.
3. **Capture-Group Reset Divergence Inside Loops (Verified by Execution, Probe B-1)**:
   ECMA-262 `RepeatMatcher` (`step-repeatmatcher-clear-captures`, `spec.html` L37999) **explicitly clears every capturing group inside the repeated atom to `undefined` at the start of every iteration**:
   > `For each integer k in the inclusive interval from parenIndex + 1 to parenIndex + parenCount, set capability[k] to undefined.`

   Direct execution on `^(?:(a)|b)*$` against `"ab"` and `^(?:(a)?b)*$` against `"abb"` reveals a live semantic split across major runtimes:
   - **Node.js `v24.21.0` (V8 Irregexp, ECMA-262)**: `group[1] = undefined` on both `"ab"` and `"abb"` (cleared on iteration 2).
   - **Perl `v5.40.1`**: `$1 = undef` on both `"ab"` and `"abb"` (modern Perl clears captures on entering the next repetition where the group did not participate).
   - **Python 3 `re`**: **`group(1) = 'a'`** on both `"ab"` and `"abb"` (retains the capture from iteration 1!).

#### 4.2 Non-Regularity: Backreferences (`\1`) and Lookarounds

Basis: normative (`tc39/ecma262` @ `b1eaed82...`, `spec.html` L38031–38033, L38116–38130) + source (`PCRE2Project/pcre2` @ `0705b4a3...`, `src/pcre2_match.c` L5933–5948) + derived

- **Backreferences (`\1`, `OP_REF` / `OP_DNREF` in `pcre2_match.c` L5933–5948)**:
  Matching a regex with backreferences is **NP-complete** (reducible from 3-SAT; even the copy language $L = \{ww \mid w \in \Sigma^*\}$ matched by `^(.*)\1$` is not context-free!). ECMA-262 (`spec.html` L38031–38033) explicitly exhibits a unary arithmetic algorithm inside a single regex:
  ```js
  "aaaaaaaaaa,aaaaaaaaaaaaaaa".replace(/^(a+)\1*,\1+$/, "$1") // -> "aaaaa" (gcd(10, 15) = 5)
  ```
  Consequently, **no polynomial-time DFA or Thompson NFA simulation can support arbitrary backreferences** unless $\text{P} = \text{NP}$.
- **Lookarounds (`(?=...)`, `(?!...)`, `(?<=...)`, `(?<!...)`)**:
  Positive/negative lookahead preserves regularity *in theory* (Boolean closure of regular languages without captures), and ES2018 variable-length lookbehind runs a reverse matcher (`direction = -1`), whereas PCRE2 restricts lookbehind branches to fixed/bounded length. However, lookarounds combined with **capture groups inside lookahead** or **arbitrary backtracking interaction** break single-pass streaming automata (`O(1)` input cursor monotonicity) and are therefore rejected by both `google/re2` and `rust-lang/regex`.

#### 4.3 Catastrophic Backtracking (`ReDoS`) vs Linear-Time Automata (`RE2`, `rust-lang/regex`, `V8 Experimental`)

Basis: source (`PCRE2Project/pcre2` `src/pcre2_match.c` L925–928; `v8/v8` `src/regexp/experimental/experimental-interpreter.cc` L253–268; `google/re2` `re2/nfa.cc` L385–485, `re2/bitstate.cc` L36–55; `rust-lang/regex` `regex-automata/src/meta/strategy.rs` L452–462, `regex-automata/src/hybrid/dfa.rs` L118–126, `regex-automata/src/nfa/thompson/pikevm.rs` L1040–1085) + execution (Probe B-2)

**Root cause of ReDoS**: Whenever a backtracking DFS visits the same `(bytecode_pc, input_index)` configuration via multiple paths—classically **ambiguous nested quantifiers** (`(a+)+b`, `(a|a)+b`, `(\w+)*$`) yielding $\Omega(2^n)$ exponential paths, or **overlapping adjacent quantifiers** (`.*a.*b`, `a+a+$`) yielding $\Omega(n^k)$ polynomial paths—a mismatching suffix forces the engine to exhaust every partition before failing.

**Empirical ReDoS Benchmark (Probe B-2, Linux x86-64, pattern `^(a+)+b$` on `"a"*n + "!"`)**:

| Input Length $n$ | Python 3 `re` (Backtracker) | Node.js `v24.21.0` V8 Irregexp (Backtracker) | Pure-Python Thompson NFA ($O(m \cdot n)$) |
| :--- | :--- | :--- | :--- |
| $n = 16$ | `4.231 ms` (`False`) | `3.402 ms` (`false`) | `0.048 ms` (`False`) |
| $n = 20$ | `79.352 ms` (`False`, $18.8\times$) | `9.435 ms` (`false`) | `0.032 ms` (`False`) |
| $n = 24$ | `1134.028 ms` (`False`, $14.3\times$) | `150.276 ms` (`false`, $15.9\times$) | `0.046 ms` (`False`) |
| $n = 26$ | **`4565.703 ms`** (`False`, $4.03\times$) | **`650.656 ms`** (`false`, $4.33\times$) | **`0.037 ms`** (`False`) |
| $n = 100$ | *(unrunnable: $>2^{100}$ steps)* | *(unrunnable: $>2^{100}$ steps)* | **`0.065 ms`** (`False`) |
| $n = 10000$ | *(unrunnable: $>2^{10000}$ steps)* | *(unrunnable: $>2^{10000}$ steps)* | **`5.221 ms`** (`False`) |

Notice the textbook $2^{\Delta n}$ blowup: adding just 2 characters ($n=24 \to 26$) multiplies wall-clock runtime by **$4.03\times$ in Python `re`** and **$4.33\times$ in V8 Irregexp**, while the pure-Python Thompson NFA finishes $n = 10{,}000$ in `5.2 ms`!

**Cross-Engine Architectural Comparison**:

| Engine (Pinned Revision) | Backrefs / Lookaround | Worst-Case Time Complexity | Execution Strategy & ReDoS Defenses |
| :--- | :--- | :--- | :--- |
| **PCRE2** (`0705b4a3...`) | Both supported | Exponential $O(2^n)$ (bounded by limits) | Heap-allocated frame backtracker (`pcre2_match.c`) with hard caps `mb->match_call_count >= mb->match_limit` (`PCRE2_ERROR_MATCHLIMIT`) and `Frdepth >= mb->match_limit_depth` (`PCRE2_ERROR_DEPTHLIMIT`, `L925–928`); manual atomic groups `(?>...)` / possessive quantifiers `++`; optional `pcre2_dfa_match` without captures |
| **V8 Irregexp + Experimental** (`e88118f6...`) | Both supported in Irregexp; omitted in Experimental | Exponential $O(2^n)$ in Irregexp; **$O(m \cdot n)$** in Experimental | Default JIT-compiled backtracking VM (with `--enable-experimental-regexp-engine-on-excessive-backtracks` fallback to `NfaInterpreter` breadth-first lockstep VM in `experimental-interpreter.cc` L253–268 for linear-eligible patterns) |
| **Google RE2** (`2da00568...`) | **Intentionally unsupported** | **Guaranteed $O(m \cdot n)$** | Multi-tier linear pipeline: (1) **Lazy DFA** (`re2/dfa.cc`) caching powerset states on the fly with bounded RAM (`ResetCache` flush on exhaustion, avoiding $2^m$ compile-time blowup); (2) **BitState** (`re2/bitstate.cc` L42–55) memoized bit-vector backtracker (`ShouldVisit(id, p)`) strictly $O(m \cdot n)$ for small inputs needing captures; (3) **Thompson/PikeVM NFA** (`re2/nfa.cc` L385–485) supporting both leftmost-first and POSIX leftmost-longest (`longest_`) with full submatch captures |
| **Rust `regex` / `regex-automata`** (`fde4946d...`) | **Intentionally unsupported** | **Guaranteed $O(m \cdot n)$** | `meta::strategy::Core` (`strategy.rs` L452–462) orchestrates: literal **Prefilter** (Teddy/Aho-Corasick/memchr) -> **ReverseAnchored/ReverseSuffix** -> **Full/Hybrid Lazy DFA** (`hybrid/dfa.rs` L118–126 with `ByteClasses` alphabet compression & `CacheError` quit-on-thrash) -> **OnePass DFA** (unambiguous capture extraction in $O(n)$) -> **BoundedBacktracker** (memoized bitset, $O(mn)$) -> **PikeVM** (`pikevm.rs` L1040–1085, universal $O(mn)$ capture fallback) |

**Why memoized backtracking (`BitState` / `BoundedBacktracker`) is strictly $O(m \cdot n)$**:
When a pattern has no backreferences and no lookarounds, an execution state is uniquely determined by `(nfa_state_id, input_pos)`. Maintaining a 1-bit `visited[id * (n + 1) + pos]` table (`BitState::ShouldVisit` in `re2/bitstate.cc` L52) guarantees every `(state, position)` pair is explored at most once—preserving exact leftmost-first DFS capture priority with zero exponential blowup, at the cost of $O(m \cdot n)$ bits of RAM (hence gated to small inputs/patterns, falling back to `PikeVM` when the bitset budget is exceeded).

## Boundaries

- **HoTTSQL 3VL `NULL` support (`known not to apply` to core `UnivalentSemantics.v`)**: Direct inspection of `uwdb/Cosette` `hott/library/UnivalentSemantics.v` (L171–181) establishes that the core HoTT formalization evaluates `Pred` into two-valued `hProp` rather than native Kleene 3-valued `NULL`s; verifying 3VL `NULL` rewrites in Cosette/HoTTSQL requires explicit `Option`/3VL encoding extensions outside the core `UnivalentSemantics.v` module.
- **Live PostgreSQL multi-session execution (`not examined`)**: No PostgreSQL server daemon was running locally; `EvalPlanQual`, `ExecBRUpdateTriggers`, `AfterTriggerSaveEvent`, and `SIREAD` SSI findings are established from direct source inspection of `postgres/postgres` @ `2c077c7d...` and peer-reviewed database theory (Berenson 1995, Adya 2000, Cahill 2008) rather than live concurrent psql sessions.
- **Oracle empty-string `NULL` conflation & MySQL InnoDB gap-locking (`not examined`)**: Oracle's non-standard treatment of `'' IS NULL` and MySQL InnoDB's locking `REPEATABLE READ` (which uses next-key gap locks rather than pure Snapshot Isolation) were not directly examined and diverge from PostgreSQL/SQLite behavior.
- **PCRE2, RE2, and Rust `regex` compiled binary benchmarks (`not examined`)**: `pcre2test`, `re2`, and `rustc`/`cargo` were not installed locally; ReDoS timing measurements were collected directly on Python 3 `re`, Node.js `v24.21.0` (V8 Irregexp), and a pure-Python Thompson NFA, while PCRE2/RE2/Rust `regex` engine internals were verified via pinned source inspection.
- **V8 `--enable-experimental-regexp-engine` runtime toggle (`not examined`)**: Node.js `v24.21.0` was benchmarked under its default V8 configuration (Irregexp backtracker) without passing `--enable-experimental-regexp-engine-on-excessive-backtracks`.
- **Stronger conclusion NOT established**: Switching a regex engine to PCRE2 with `match_limit` does **not** eliminate ReDoS—it converts CPU exhaustion into silent match-error denial of service (`PCRE2_ERROR_MATCHLIMIT`) that may bypass WAF/validation filters if callers treat match errors as non-matching! Conversely, switching a database to `REPEATABLE READ` does **not** prevent Write Skew (`A5B`) or cross-row trigger invariant violations under MVCC Snapshot Isolation.

## Evidence

### Peer-Reviewed Papers and Specifications
1. **Shumo Chu, Konstantin Weitz, Alvin Cheung, and Dan Suciu**, *"HoTTSQL: Proving Query Rewrites with Univalent SQL Semantics"*, PLDI 2017, DOI `10.1145/3062341.3062348`.
2. **Hal Berenson, Philip A. Bernstein, Jim Gray, Jim Melton, Elizabeth J. O'Neil, and Patrick E. O'Neil**, *"A Critique of ANSI SQL Isolation Levels"*, ACM SIGMOD 1995, DOI `10.1145/223784.223785`.
3. **Atul Adya, Barbara Liskov, and Patrick O'Neil**, *"Generalized Isolation Level Definitions"*, IEEE ICDE 2000, DOI `10.1109/ICDE.2000.839388`.
4. **Michael J. Cahill, Uwe Röhm, and Alan D. Fekete**, *"Serializable Isolation for Snapshot Databases"*, ACM SIGMOD 2008, DOI `10.1145/1376616.1376715` (extended journal version ACM TODS 2009, DOI `10.1145/1620585.1620587`).
5. **Russ Cox**, *"Regular Expression Matching Can Be Simple And Fast (but is slow in Java, Perl, PHP, Python, Ruby, ...)"*, Jan 2007 (`https://swtch.com/~rsc/regexp/regexp1.html`).

### Pinned Upstream Source Inspections (Observed 2026-11-19)
- **`uwdb/Cosette` @ `7a951aa3b1a70a8b310c676e524740b7114975c3`**:
  - `hott/library/UnivalentSemantics.v`: `Tuple` (L50–56), `Definition Relation s := Tuple s -> Type` (L65), `Inductive SQL` / `Pred` (L115–134), `denoteSQL` (`project` dependent sum `∑`, `distinct` via `merely`, L165–170), `denotePred` (`hProp`, L171–181).
- **`postgres/postgres` @ `2c077c7d602dba034e209227ea04a14b10797c42`**:
  - `src/backend/storage/lmgr/predicate.c`: `SIREAD` predicate lock architecture and escalation (L27–43), `XactReadOnly` safe-snapshot dangerous-structure exemption (L1725–1741).
  - `src/backend/executor/execMain.c`: `EvalPlanQual` recheck entry (L2713–2730), `EvalPlanQualFetchRowMark` (L2869–2885).
  - `src/backend/commands/trigger.c`: `AfterTriggerSaveEvent` (L97–105), `ExecBRUpdateTriggers` (L3017–3032).
- **`tc39/ecma262` @ `b1eaed82fc5e8a511c5b2007f194b16c8f7e5ea6`**:
  - `spec.html`: `RepeatMatcher` (L37975–38011) including `step-repeatmatcher-done` empty-match termination (L37994) and `step-repeatmatcher-clear-captures` per-iteration capture clearing (L37999); ordered alternation `/(aa|aabaac|ba|b|c)*/` note (L38022–38030); unary $\gcd$ backreference note `/^(a+)\1*,\1+$/` (L38031–38033); `CompileAssertion` (L38116–38130).
- **`PCRE2Project/pcre2` @ `0705b4a358eca084a1e6159efa29cbf6d3aea095`**:
  - `src/pcre2_match.c`: `match_call_count >= match_limit` (`PCRE2_ERROR_MATCHLIMIT`) & `Frdepth >= match_limit_depth` (`PCRE2_ERROR_DEPTHLIMIT`) guards (L925–928); `OP_REF`/`OP_DNREF` backreference opcodes (L5933–5948).
- **`v8/v8` @ `e88118f63dd96f24a9acb8bd0665e7880063f5c0`**:
  - `src/regexp/experimental/experimental-interpreter.cc`: `class NfaInterpreter` lockstep breadth-first non-backtracking linear VM matching backtracking priority (L252–268).
- **`google/re2` @ `2da0056814cf180480a19f5cf811e7e1c054bf6d`**:
  - `re2/nfa.cc`: `NFA::Search` Thompson/PikeVM simulation supporting leftmost-first and `longest_` modes (L385–485).
  - `re2/bitstate.cc`: `class BitState` memoized `ShouldVisit` visited-bitset backtracker (L36–55).
- **`rust-lang/regex` @ `fde4946d4a3cb367338a21493ec91ec7106a12b4`**:
  - `regex-automata/src/meta/strategy.rs`: `struct Core` multi-engine dispatcher (`Prefilter`, `PikeVM`, `BoundedBacktracker`, `OnePass`, `Hybrid`, `DFA`, L452–462) and `ReverseAnchored`/`ReverseSuffix` wrappers (L168–179).
  - `regex-automata/src/hybrid/dfa.rs`: `pub struct DFA` lazy DFA with `ByteClasses` and `cache_capacity` (L118–126).
  - `regex-automata/src/nfa/thompson/pikevm.rs`: `PikeVM::search_slots` linear-time capture extraction (L1040–1085).

### Local Execution Probes (Observed 2026-11-19, Linux x86-64)
- **Probe A (`python3` `sqlite3` `3.53.4`)**:
  - `CREATE TABLE items (id INT, grp INT, val INT CHECK (val > 0))` accepted `(3, NULL, NULL)`.
  - `SELECT id, val FROM items WHERE val NOT IN (SELECT val FROM banned)` with `banned = {(10), (NULL)}` returned `[]`; `NOT EXISTS` returned `[(3, None), (4, 20)]`.
  - `SELECT id FROM items WHERE val = 10 OR val != 10` returned `[(1,), (2,), (4,)]` (omitting `id=3`).
  - `SELECT grp, COUNT(*), COUNT(val), SUM(val) FROM items GROUP BY grp` returned `[(None, 2, 1, 20), (1, 2, 2, 20)]`.
  - `CREATE TABLE uq (k INT UNIQUE); INSERT (NULL), (NULL)` succeeded with `COUNT(*) = 2`.
  - Empty table `SELECT COUNT(*), COUNT(val), SUM(val)` returned `[(0, 0, None)]`.
  - Bag duplication: `WHERE val >= 10 OR val <= 20` returned `3` rows vs `UNION ALL` returning `6` rows.
- **Probe B-1 (Capture-group reset inside loops on `^(?:(a)|b)*$` -> `"ab"` and `^(?:(a)?b)*$` -> `"abb"`)**:
  - Python 3 `re`: `group(1) = 'a'` (both cases);
  - Node.js `v24.21.0` (V8): `group[1] = undefined` (both cases);
  - Perl `v5.40.1`: `$1 = undef` (both cases).
- **Probe B-2 (Catastrophic ReDoS on `^(a+)+b$` over `"a"*n + "!"`)**:
  - Python 3 `re`: `n=16: 4.231 ms`, `n=20: 79.352 ms`, `n=24: 1134.028 ms`, `n=26: 4565.703 ms`.
  - Node.js `v24.21.0` V8 Irregexp: `n=16: 3.402 ms`, `n=20: 9.435 ms`, `n=24: 150.276 ms`, `n=26: 650.656 ms`.
  - Pure-Python Thompson NFA: `n=16: 0.048 ms`, `n=26: 0.037 ms`, `n=100: 0.065 ms`, `n=10000: 5.221 ms`.

## Revalidation

1. **SQL 3VL & Bag Semantics check**: Run the 15-line SQL script from Probe A against any target SQL engine (PostgreSQL, MySQL, DuckDB, Oracle, or newer SQLite) to check `CHECK (val > 0)` null acceptance, `NOT IN` null annihilation, `UNIQUE` null handling, and empty `SUM` behavior.
2. **PostgreSQL MVCC `EvalPlanQual` & Write Skew check**: Open two concurrent `psql` sessions on a table `doctors(id INT, on_call BOOL)` with two rows `TRUE`:
   - Under `BEGIN ISOLATION LEVEL REPEATABLE READ;`, have both sessions run `SELECT count(*) FROM doctors WHERE on_call;` (both see `2`), then Session 1 sets `id=1` to `FALSE` and Session 2 sets `id=2` to `FALSE`, and both `COMMIT` -> succeeds under `REPEATABLE READ` (Write Skew!), whereas repeating under `BEGIN ISOLATION LEVEL SERIALIZABLE;` aborts the second committer with `ERROR: could not serialize access due to read/write dependencies among transactions` (`40001`).
   - Under `READ COMMITTED`, attach a `BEFORE UPDATE` trigger logging via `RAISE NOTICE` and run overlapping `UPDATE` statements to observe `EvalPlanQual` re-firing the trigger.
3. **Regex capture-reset & ReDoS check**: Execute `^(?:(a)|b)*$` against `"ab"` and time `^(a+)+b$` on `"a"*24 + "!"` vs `"a"*26 + "!"` under any target regex library (`pcre2`, `re2`, Rust `regex`, Java, Go `regexp`, Node `--enable-experimental-regexp-engine-on-excessive-backtracks`). Exponential $\approx 4\times$ runtime jump from $n=24 \to 26$ discriminates backtracking engines from linear-time Thompson/DFA engines in under one second.
