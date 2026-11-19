# Bounded-Memory Streaming Semantics, Watermarks, and Timely Retraction Liveness

## Summary

Long-running incremental view maintenance (IVM) and streaming engines confront an irreducible tension between **exactness under arbitrary out-of-order updates/retractions**, **bounded resident memory (`O(W)` rather than `Ω(T)`)**, and **progress/compaction liveness** in cyclic dataflows. Across classical stream theory, typed streaming calculi, Timely/Differential Dataflow, and Feldera DBSP, four load-bearing invariants govern correctness and resource boundedness:

1. **The Bounded-Memory Characterization Boundary (`Arasu–Widom`, `StreamQRE`, `Stream Types`, `Flo`):** Unbounded Select-Project-Join (SPJ) queries over infinite streams generally require `Ω(N)` state unless all cross-stream join/inequality predicates satisfy Arasu et al.'s (ACM TODS 2004) **Locally Totally Ordered (`LTO`) / `Max-Subset`** criteria—or are externally bounded by monotonic watermarks, explicit punctuation, or sliding windows. Language-level type systems enforce boundedness statically via complementary disciplines: `StreamQRE` (PLDI 2017) restricts queries to unambiguous quantitative regular expressions yielding `O(1)` per-item space/time; `Stream Types` / `Delta` (`alpha-convert/delta`, PLDI 2024) enforces **ordered bunched contexts (`;` vs. `,`)** plus structural punctuation (`CatPunc`, `PlusPuncA`/`B`) with Brzozowski-style event derivatives so non-streamable operations like list reversal fail to typecheck; and `Flo` / `Hydro` (`hydro-project/hydro`) separates `Bounded` from `Unbounded` live collections so operators that require termination (or sort/build-side materialization) cannot silently block on infinite streams.
2. **Exact Cyclic Progress Tracking & Frontier Liveness (`Timely Dataflow` & Isabelle/HOL `Progress_Tracking`):** `TimelyDataflow/timely-dataflow` tracks exact minimal lower-bound **`Antichain`** frontiers across cyclic multi-dimensional timestamp graphs (`(epoch, iter)`) via `MutableAntichain` pointstamp/implication propagation (`reachability.rs`) and monotone `PathSummary` composition (`timestamp.rs`). Mechanized verification (Brun, Decova, Lattuada, Traytel, ITP 2021) proves safety and liveness *provided* timestamps are well-founded and **every directed cycle strictly advances timestamps**. Direct source inspection confirms that `Builder::build` (`reachability.rs:215-223`) checks `is_acyclic()` for zero-increment cycles but **only prints a warning to stdout without aborting**; executing a `(0, 0)` cycle permanently deadlocks output frontiers at `[(0, 0)]` even after all external capabilities are dropped (`Basis: execution`).
3. **Retraction Compaction vs. Straggler Frontier Freezes (`Differential Dataflow`):** `TimelyDataflow/differential-dataflow` separates **`logical_frontier`** (allowing timestamp coalescing so `+1`/`-1` updates in an `Abelian` difference group cancel to zero and free memory) from **`physical_frontier`** (allowing fuel-amortized geometric `Spine` batch merges with a `4×` work factor while preserving clean-cut `spans_through` boundaries for joins). Because exact capability tracking forbids discarding late data, a single stalled worker or leaked capability at `(0, 0)` freezes `logical_frontier` globally—converting a liveness fault into an **`Ω(T)` uncompacted spine memory leak** (`max_uncompacted_epoch_span = 500` over 500 epochs vs. `0` when healthy, `Basis: execution`).
4. **DBSP $\mathbb{Z}$-Set Algebra, Compiler Monotonicity Analysis, and Waterline GC (`Feldera`):** `DBSP` (Budiu et al., PVLDB 2023; Lean 3.51.1 formalization `tchajed/database-stream-processing-theory`) incrementalizes arbitrary relational and recursive queries via exact $\mathbb{Z}$-set integration $\mathcal{I}$ and differentiation $\mathcal{D}$ ($\mathcal{I}(\mathcal{D}(s)) = s$). To bound $\mathcal{I}$'s trace memory, `feldera/feldera` computes monotonic event-time **`waterline`** bounds (distinct from DBSP logical clock ticks), runs whole-circuit abstract interpretation (`MonotoneAnalyzer` → `InsertLimiters` → `MergeGC` → `CheckRetain`) to synthesize `integrate_trace_retain_keys`/`values` GC predicates (merging multiple consumers by logical `OR`), and guards inputs with **`controlled_key_filter`** to divert late records violating declared `LATENESS` into an error view. Executable probing confirms that **unfiltered late `-1` retractions crossing a compacted waterline produce permanent phantom negative-weight outputs** (`w = -1`, violating $\mathcal{I}(\Delta S) = S$), whereas `controlled_key_filter` eliminates negative-weight corruption at the cost of explicit late-data divergence (`Basis: execution`).

---

## Applicability

This report examines, compares, and cross-checks formal semantics, compiler static analyses, and runtime compaction architectures across 14 durable upstream subjects:

1. **Theoretical Foundations of Bounded-Memory Streaming and Typed Stream Calculi:**
   - Arasu, Babcock, Babu, McAlister, Widom (ACM TODS 2004, `DOI: 10.1145/974750.974756`) — applies to continuous Select-Project-Join (SPJ) queries without explicit window clauses over unbounded relational streams.
   - Mamouras, Raghothaman, Alur, Ives, Khanna (`StreamQRE`, PLDI 2017, `DOI: 10.1145/3062341.3062369`) — applies to quantitative regular expressions over sequential event streams.
   - `alpha-convert/delta` (`20db7e6fd4c0970b04e60abeea2213aaaaba8c31`) and Cutler et al. (`Stream Types`, PLDI 2024, `DOI: 10.1145/3656434`) — applies to functional programs over typed finite/unbounded parallel-and-sequential streams with explicit structural punctuation.
   - `hydro-project/hydro` (`fbaccddb35111327f96922259d60dc1607395545`, `hydro_lang/src/live_collections/boundedness.rs`) and Laddad et al. (`Flo`, `arXiv:2411.08274`) — applies to progressive distributed dataflow collections typed by boundedness (`Bounded` vs. `Unbounded`) and ordering (`TotalOrder` vs. `NoOrder`).

2. **Exact Progress-Tracking and Retraction-Based Incremental Dataflow Engines:**
   - `TimelyDataflow/timely-dataflow` (`5d82cb0bd4e43a6a47c59383fb2475e6842c0a57`), Murray et al. (`Naiad`, SOSP 2013, `DOI: 10.1145/2517349.2522738`), Abadi & Isard (FORTE 2015, `DOI: 10.1007/978-3-319-19195-9_1`), and Brun, Decova, Lattuada, Traytel (ITP 2021, `DOI: 10.4230/LIPIcs.ITP.2021.10`, AFP `Progress_Tracking`) — applies to cyclic, nested-scope, partially-ordered pointstamp progress tracking across multi-worker dataflow graphs.
   - `TimelyDataflow/differential-dataflow` (`e7c24703f4b1935cd6c99779ed0c140b0fea8ac6`) and McSherry et al. (CIDR 2013) — applies to incremental collections with `Abelian` / `Semigroup` difference weights stored in fuel-amortized `Spine` traces.

3. **DBSP Algebra, Monotonicity-Driven Trace Garbage Collection, and Heuristic Watermarks:**
   - `feldera/feldera` (`42a79b1cf0ee86b94335ec87138fb331ed0a8239`), `tchajed/database-stream-processing-theory` (`fb6ff4416108710448ccd87473c5513c1a1179ea`, Lean `3.51.1`), and Budiu, Chajed, McSherry, Ryzhyk, Tannen (PVLDB 2023, `DOI: 10.14778/3587136.3587137`, `arXiv:2203.16684`) — applies to synchronous-clock $\mathbb{Z}$-set streaming circuits with compiler-inferred `LATENESS` / `waterline` trace GC.
   - Akidau et al. (`The Dataflow Model`, PVLDB 2015, `DOI: 10.14778/2824032.2824076`) and Tucker, Maier, Sheard, Fegaras (`Punctuation Semantics`, IEEE TKDE 2003, `DOI: 10.1109/TKDE.2003.1198390`) — contrasted as heuristic event-time watermark and in-band punctuation paradigms.

4. **Executable Micro-Probes:** Probes 2A and 2B execute exact Python 3.13 models of (a) DBSP bilinear join $\mathbb{Z}$-set updates with waterline retention GC and optional `controlled_key_filter`, and (b) Timely Dataflow cyclic `(epoch, iter)` `MutableAntichain` propagation under healthy, stalled-partition, and zero-increment-cycle topologies. Probe conclusions hold for the exact algebraic equations and protocol transitions modeled; physical memory constants (e.g., LSM/Spine spill-to-disk tuning or RocksDB/Storage-engine overhead in Feldera) are outside the probe scope.

---

## Findings

### 1. Static Characterization of Bounded-Memory Stream Computation

#### 1.1 The Arasu–Widom Bounded-Memory SPJ Boundary

`Basis: normative + derived`

Arasu, Babcock, Babu, McAlister, and Widom (ACM TODS 2004, `DOI: 10.1145/974750.974756`) established an exact decidable syntactic characterization of which continuous Select-Project-Join (SPJ) queries over unbounded streams `S_1, …, S_n` with discrete totally ordered domains (without explicit window operators) are computable in **bounded memory `O(1)`** (independent of stream length `N`) versus requiring **`Ω(N)` unbounded memory**:

- **Locally Totally Ordered (`LTO`) Equivalence Decomposition:** Every SPJ query with equality and inequality (`<`, `≤`, `=`, `≠`) predicates over integer attributes decomposes into a finite disjunction of **Locally Totally Ordered** queries (each specifying a total ordering over all attributes and constants). An SPJ query is bounded-memory computable **if and only if** every LTO sub-query is bounded-memory computable.
- **Exact Necessary and Sufficient Conditions (Theorem 4.3, Arasu et al. 2004):** An LTO query `Q` over streams `S_1, …, S_n` is computable in bounded memory iff:
  1. **Bounded-Domain Projections & Joins:** Every attribute appearing in a cross-stream equality join (`S_i.A = S_j.B`) or projected in the output (under duplicate-eliminating `SELECT DISTINCT`) is constrained to a **finite constant interval** `c_1 ≤ A ≤ c_2` by selection predicates! If an unconstrained join attribute can take unboundedly many distinct values, an adversary can feed `N` distinct tuples on `S_1` followed by matching tuples on `S_2`, forcing `Ω(N)` state by a fooling-set / communication-complexity argument.
  2. **Extreme-Value (`Max-Subset` / `Min-Subset`) Reduction for Inequalities:** Cross-stream inequalities like `σ_{S_1.A < S_2.B}(S_1 × S_2)` can remain `O(1)` *only* for **existential / duplicate-eliminated** or extreme-value projections (storing only `min(S_1.A)` and `max(S_2.B)`), whereas emitting all matching pairs `(s_1, s_2)` requires storing all past `S_1` tuples (`Ω(N)`).
- **Engineering Consequence (`derived`):** Any general relational equijoin `S ⋈_{S.k = T.k} T` or `GROUP BY k` over an unbounded key domain `k` is **provably `Ω(N)`** unless augmented with an *external progress contract*: (a) finite sliding/tumbling windows, (b) in-band **punctuation** asserting "no future tuple has `k = v`" (Tucker et al., IEEE TKDE 2003, `DOI: 10.1109/TKDE.2003.1198390`), or (c) **monotonic event-time waterlines** coupled with time-bounded join predicates `|S.ts - T.ts| ≤ W`.

#### 1.2 Quantitative Regular Streaming (`StreamQRE`), Ordered Stream Types (`Delta`), and Progressive Boundedness (`Flo` / `Hydro`)

`Basis: normative + source + documentation`

To avoid ad-hoc runtime TTL heuristics, three PL traditions encode streamability and memory boundedness directly in types or query combinators:

1. **`StreamQRE` (Mamouras et al., PLDI 2017, `DOI: 10.1145/3062341.3062369`):**
   - Combines regular-expression parsing combinators (`atom`, `split` concatenation, `iter` Kleene iteration, `or` choice) with quantitative aggregation operations (`combine` over arbitrary data types).
   - Enforces **unambiguity** (each input prefix parses uniquely) and **rate/register typing** so every well-typed `StreamQRE` compiles to a single-pass streaming evaluator using **`O(1)` memory per item** (or `O(|Q|)` total state independent of stream length) when underlying scalar summaries are constant-size (sums, counts, min/max, running averages).
2. **`Stream Types` & `Delta` (`alpha-convert/delta`, `20db7e6fd4c0970b04e60abeea2213aaaaba8c31`, Cutler et al., PLDI 2024, `DOI: 10.1145/3656434`):**
   - Direct inspection of `src/Types.hs:40-168`, `src/Event.hs:17-88`, and `README.md:1-77` reveals how `Delta` statically rejects non-streamable recursive programs while guaranteeing determinism across parallel interleaved streams:
     - **Regular Stream Types (`Types.hs:40-49`):**
       ```haskell
       data TyF v = TyVar v | TyEps | TyInt | TyBool
                  | TyCat (TyF v) (TyF v)   -- sequential (s . t)
                  | TyPar (TyF v) (TyF v)   -- parallel interleaving (s || t)
                  | TyPlus (TyF v) (TyF v)  -- choice (s + t)
                  | TyStar (TyF v)          -- repetition (s*)
       ```
     - **First-Class Punctuation Events & Brzozowski Derivatives (`Event.hs:17-88`):** Wire events include data (`LitEv`), choice tags (`PlusPuncA`, `PlusPuncB`), parallel routing (`ParEvA`, `ParEvB`), and sequential boundary punctuation **`CatPunc`**. Crucially, `hasType CatPunc (TyCat s t)` checks `guard (isNull s)` (`Event.hs:43`)—enforcing that punctuation closing `s` may arrive *only after* `s` has reduced to a nullable type—and `deriv CatPunc (TyCat _ t) = return t` (`Event.hs:69`) advances the stream type to `t`! Similarly, `TyStar s` unfolds dynamically via `PlusPuncA → TyEps` (end of stream) and `PlusPuncB → TyCat s (TyStar s)` (`Event.hs:85-86`).
     - **Ordered Bunched Contexts (`Types.hs:90-103`, `README.md:44-70`):** Typing contexts are trees with **sequential concatenation (`SemicCtx (g ; g')`)** and **parallel composition (`CommaCtx (g , g')`)**. Variables separated by `;` must be consumed strictly in arrival order: attempting to write list reversal via `fun snoc(x : Int; xs : Int*)` (`README.md:50-66`), which emits elements of `xs` before `x`, is statically rejected because `x` arrives strictly before `xs` and buffering an unbounded `Int*` to emit `x` last breaks bounded-memory streaming!
3. **`Flo` & `Hydro` (`arXiv:2411.08274`, `hydro-project/hydro`, `fbaccddb35111327f96922259d60dc1607395545`):**
   - `Flo` (Laddad, Cheung, Hellerstein, Milano, `arXiv:2411.08274`) formalizes two universal properties across Flink, LVars, and DBSP: **streaming progress** (every finite prefix of input eventually yields its corresponding output prefix without blocking on stream end) and **eager execution** (output is deterministic and fresh as inputs arrive).
   - Direct inspection of `hydro_lang/src/live_collections/boundedness.rs:14-82` shows how `Flo`'s boundedness type system manifests in Rust:
     - Sealed trait `Boundedness` has exactly two uninhabited marker types: `Bounded` (`const BOUNDED: bool = true`) and `Unbounded` (`const BOUNDED: bool = false`).
     - Associated type `PreserveOrderIfBounded<InO>` (`boundedness.rs:39-57, 67`) encodes execution semantics at compile time: joining against a `Bounded` build side materializes it first and preserves left-stream order `InO`; joining against an `Unbounded` right side forces a symmetric hash join yielding `NoOrder`.
     - Associated type `AggregatedOptional` maps `Bounded → Bounded` vs. `Unbounded → InitNone` (persisting across ticks).
     - Blocking operators require `IsBounded` (`impl IsBounded for Bounded {}` only, `boundedness.rs:70-82`), emitting a custom Rust compiler error directing authors either to strengthen boundedness upstream or to enter an explicit non-deterministic `sliced!` batching region.

---

### 2. Timely Dataflow Cyclic Progress Tracking & Frontier Liveness

#### 2.1 Partially Ordered Timestamps, `PathSummary`, and Nested Scope Refinement

`Basis: normative + source`

Direct inspection of `TimelyDataflow/timely-dataflow` (`5d82cb0bd4e43a6a47c59383fb2475e6842c0a57`) shows how Timely generalizes linear watermarks to arbitrary **partially ordered, multi-dimensional timestamps** (e.g., `(outer_epoch, inner_loop_iteration)` for nested iterative dataflows):

- **`Timestamp` and `PathSummary` Contracts (`timely/src/progress/timestamp.rs:14-88`):**
  - `Timestamp: Clone + Eq + PartialOrder + Ord + Debug + Any + ExchangeData` requires a total linear extension `Ord` compatible with `PartialOrder` (`a.less_equal(b) ⇒ a <= b`, `timestamp.rs:12-13`), a unique `minimum()`, and an associated `Summary: PathSummary<Self>`.
  - `PathSummary<T>` defines `results_in(&self, src: &T) -> Option<T>` and associative composition `followed_by(&self, other: &Self) -> Option<Self>`, returning `None` on overflow (e.g., `checked_add` for integers, `timestamp.rs:104-109`, causing `feedback` to drop overflowed messages). Both methods MUST be monotonic in both arguments, and `Default::default()` is the identity/noop summary (`Self::default().results_in(&t) == Some(t)`).
  - **Scope Refinement (`Refines<T>`, `timestamp.rs:140-151`):** Entering a nested loop scope maps outer timestamps via `to_inner` and exits via `to_outer`, requiring `summarize(path)` to conservatively lower-bound the outer effect: `summarize(path).results_in(t) ≤ path.results_in(t.to_inner()).to_outer()`.
- **`Antichain<T>` and `MutableAntichain` (`timely/src/progress/frontier.rs:20-260`):**
  - `Antichain<T>` stores a `SmallVec<[T; 1]>` of mutually incomparable minimal elements: `insert(e)` drops `e` if `∃x ∈ self. x ≤ e`, else removes all `x` with `e ≤ x` and appends `e` (`frontier.rs:38-47`).
  - `MutableAntichain<T>` maintains reference counts `(time → i64)` and emits discrete frontier deltas `(+1 / -1)` only when the minimal antichain of positive-count timestamps actually changes, filtering high-frequency message churn out of global progress broadcasts (`reachability.rs:656-662`).

#### 2.2 Cyclic Pointstamp Reachability Propagation and the Non-Incrementing Cycle Hazard

`Basis: normative + source + execution`

In `timely/src/progress/reachability.rs:650-793`, `Tracker::propagate_all` executes a two-phase reachability update:

1. **Step 1 — Local Pointstamp Filtering (`reachability.rs:656-701`):** Drains batched capability/message count deltas (`target_changes`, `source_changes`) through each port's `pointstamps: MutableAntichain<T>`, projects changes to scope outputs via precompiled `target_summaries` / `source_summaries` (computed backwards by semi-naive fixpoint in `summarize_outputs`, `reachability.rs:858-900`), and pushes frontier changes onto a min-heap `worklist: BinaryHeap<Reverse<(T, Location, i64)>>` ordered by `Ord` (linear extension of `PartialOrder`).
2. **Step 2 — Monotone Layered Propagation (`reachability.rs:703-764`):** Pops the minimum `(time, location)`, coalesces all queued deltas for that exact `(time, location)`, updates `implications: MutableAntichain<T>`, and forwards any net implication delta across operator internal `PathSummary` edges (`summary.results_in(&time)`) or outgoing graph edges back onto `worklist`.
   - Notice the source comment at `reachability.rs:705-708`: *"The argument that this always terminates is subtle, and should be made. The intent is that by moving forward in layers through `time`, we will discover zero-change times when we first visit them..."*
3. **Formal Verification in Isabelle/HOL (`Brun, Decova, Lattuada, Traytel`, ITP 2021, `DOI: 10.4230/LIPIcs.ITP.2021.10`, AFP `Progress_Tracking`):**
   - Formalizes Abadi & Isard's distributed progress-tracking protocol (FORTE 2015, `DOI: 10.1007/978-3-319-19195-9_1`), where multiple workers asynchronously exchange `(location, time, diff)` progress updates while locally maintaining `pointstamps` and `implications`.
   - **Proved Safety Theorem:** If timestamp `t` is not greater than or equal to any element in worker `w`'s local `implications` frontier at input port `l`, then *globally* no in-flight message or held capability anywhere in the distributed graph can ever reach `l` at any timestamp `t' ≤ t`.
   - **Proved Liveness Preconditions:** Termination of propagation and eventual frontier advancement require: (i) **well-foundedness** of the timestamp partial order `(T, <)`, (ii) **strict cycle advancement** (every directed cycle in the dataflow graph composes to a summary `s` with `∀t. s.results_in(t) = Some(t') ⇒ t < t'`), and (iii) **fairness** of progress broadcast delivery and capability release.
4. **Source-Level Safety Gap (`reachability.rs:215-260`) & Executable Micro-Probe 2B (`Basis: source + execution`):**
   - `Builder::build` (`reachability.rs:215-223`) checks `if !self.is_acyclic()` (detecting cycles of default/zero summaries), **prints `"Cycle detected without timestamp increment"` to stdout, and still constructs and runs the `Tracker`!**
   - Executing **Probe 2B** confirms the exact operational consequence on a 4-node cyclic graph `Input(0) → Body(1) → Feedback(2) → Body(1), Body(1) → Output(3)`:
     ```text
     [2B] Cyclic loop with feedback=(0,+1) is_acyclic_zero_summary=True
     [2B] Healthy 2-partition advance (500 epochs): final_output_frontier=[(500, 0)], max_uncompacted_epoch_span=0
     [2B] Stalled-partition capability leak (500 epochs): final_output_frontier=[(0, 0)], max_uncompacted_epoch_span=500 (Omega(T) spine memory growth!)
     [2B] Non-incrementing cycle feedback=(0,0) is_acyclic_zero_summary=False
     [2B] Non-incrementing cycle add_status=OK, drop_status=OK, output_frontier_after_drop=[(0, 0)]
     ```
   - With `feedback = (0, 0)`, even after the *only* external capability `(0, 0)` at `Input(0)` is dropped (`delta = -1`), `Body(1)` and `Feedback(2)` mutually sustain `implications = [(0, 0)]` around the cycle forever, permanently deadlocking `Output(3)` at `[(0, 0)]`!

---

### 3. Differential Dataflow Retractions, Dual Compaction Frontiers, and `Spine` Space Bounds

`Basis: source + normative + execution`

Differential Dataflow (`TimelyDataflow/differential-dataflow`, `e7c24703f4b1935cd6c99779ed0c140b0fea8ac6`) represents every time-varying collection as an append-only multiset trace of `(key, val, time, diff)` updates, where `diff` belongs to a `Semigroup` (or `Abelian` group with additive inverse for retractions, `differential-dataflow/src/difference.rs`) and `time: Timestamp + Lattice` supports join/meet (`∨` / `∧`).

#### 3.1 Logical vs. Physical Compaction (`TraceReader`, `trace/mod.rs:105-153`)

A crucial architectural distinction directly visible in `differential-dataflow/src/trace/mod.rs:105-153` is that **memory reclamation requires advancing TWO distinct monotonic antichain frontiers**:

1. **Logical Compaction Frontier (`set_logical_compaction(frontier)`, `trace/mod.rs:105-128`):**
   - Authorizes the trace to rewrite any historical timestamp `t` not beyond `frontier` (`¬(frontier ≤ t)`) to a coalesced representative `t' = t ⊔ frontier` (for totally ordered times, `max(t, frontier)`) whose comparison against every future query time `q ≥ frontier` is identical.
   - **Why This Reclaims Memory:** When `(k, v, t_1, +1)` and its retraction `(k, v, t_2, -1)` both fall behind `logical_frontier`, logical compaction rewrites both to the same timestamp `t^*`, merges their `Abelian` differences (`+1 + (-1) = 0`), and **physically deletes the cancelled zero-weight record**! Without logical compaction, every historical insertion and retraction must be preserved at its exact original timestamp forever.
2. **Physical Compaction Frontier (`set_physical_compaction(frontier)`, `trace/mod.rs:130-152`):**
   - Authorizes the `Spine` to **merge** immutable batches covering times not beyond `frontier` into logarithmically few larger sorted layers, sacrificing the ability to acquire a clean-cut batch cursor (`spans_through(upper)`) at timestamps behind `physical_frontier` (which `join` needs only for active unmerged times).
   - Advancing `logical_frontier` alone without advancing `physical_frontier` prevents merges from actually running and executing the cancellations; advancing `physical_frontier` without advancing `logical_frontier` merges batches into sorted runs while retaining all distinct historical timestamps (preventing `+1`/`-1` cancellation).

#### 3.2 Fuel-Amortized Geometric `Spine` Merging (`spine_fueled.rs:9-170`)

Direct inspection of `differential-dataflow/src/trace/implementations/spine_fueled.rs:9-70, 156-170` documents the exact amortization invariant that prevents stop-the-world compaction latency spikes:

- The `Spine` maintains geometric layers `0, 1, …, L` where layer `i` holds `MergeState::{Vacant, Single, Double}` of spans up to nominal size `2^i` (crucially, accounting treats a compacted batch at layer `i` as still having nominal size `2^i` so compaction at low levels does not starve fuel propagation to higher levels, `spine_fueled.rs:22-28`).
- **4× Fuel Proportionality Invariant (`spine_fueled.rs:30-56`):** Whenever an in-progress merge exists at level `k`, strictly fewer than `2^k` records exist in layers `< k`. Completing a level-`k` merge initiates at most a level-`k+1` merge needing `≤ 2^{k+2}` work units before `> 2^k` new records can invade from below—so investing **`4` units of merge fuel per arriving update** guarantees every merge completes before the next batch collides with it.
- **Idle-Time Starvation & `ExertionLogic` (`trace/mod.rs:26-27, 201-209`, `spine_fueled.rs:164-169`):** Because merge work is normally fueled by *incoming updates*, if a stream goes idle after advancing `logical_frontier` (e.g., after a bulk deletion burst), retracted data sits uncompacted in RAM until `exert()` is triggered via custom `ExertionLogic` (`Fn(&[(level, count, length)]) -> Option<usize>`).

#### 3.3 The Straggler-Capability Space-Leak Mode

`Basis: execution + derived`

In Timely/Differential Dataflow, `logical_frontier` and `physical_frontier` are driven directly by the Timely `Antichain` progress frontier. Because that frontier is an **exact global lower bound** across all workers and input handles, **one stalled partition or one leaked `Capability` clone freezes compaction for the entire downstream arrangement graph**. As Probe 2B demonstrates, when Partition 0 processes 500 epochs while Partition 1 stalls at `(0, 0)`, `final_output_frontier` remains pinned at `[(0, 0)]` and uncompacted spine span grows linearly (`500` epochs, `Ω(T)` RAM), eventually causing OOM even when 99.9% of keys were retracted!

---

### 4. Feldera DBSP: $\mathbb{Z}$-Set Algebra, Monotonicity Analysis, and Waterline Trace GC

#### 4.1 Exact Algebraic Core (`DBSP`, PVLDB 2023 & Lean 3 Formalization)

`Basis: normative + source`

Direct inspection of Tej Chajed's mechanized Lean `3.51.1` formalization (`tchajed/database-stream-processing-theory`, `fb6ff4416108710448ccd87473c5513c1a1179ea`, `README.md` + `src/{stream,operators,linear,incremental,zset,relational,recursive}.lean`) and Budiu et al. (PVLDB 2023, `DOI: 10.14778/3587136.3587137`) confirms DBSP's algebraic foundation:

- **Streams & $\mathbb{Z}$-Sets:** A stream `s ∈ S_A` is `ℕ → A` over an Abelian group `A` (`ZSet` `ℤ[K]`, finite-support maps `K → ℤ` with pointwise `+` and `-`).
- **Four Primitive Operators:** Pointwise lifting `↑f`, strict unit delay `z⁻¹(s)[0] = 0, z⁻¹(s)[t+1] = s[t]`, differentiation `D(s) = s - z⁻¹(s)`, and integration `I(s)[t] = ∑_{i=0}^t s[i]`, satisfying exact inversion `I ∘ D = D ∘ I = id`.
- **Automatic Incrementalization (`Q^Δ ≜ D ∘ Q ∘ I`):**
  - Chain rule: `(Q_1 ∘ Q_2)^Δ = Q_1^Δ ∘ Q_2^Δ`.
  - Linear time-invariant operators (`filter`, `map`, `flatmap`, `union` bag sum, `neg`): `L^Δ = L` (zero state!).
  - **Bilinear operators (equijoin `⋈`, Cartesian product `×`):**
    $$(A \bowtie B)^\Delta = (\Delta A \bowtie \Delta B) + (\mathcal{I}(z^{-1}(\Delta A)) \bowtie \Delta B) + (\Delta A \bowtie \mathcal{I}(z^{-1}(\Delta B)))$$
  - **Non-linear `distinct`:** Uses `I(z⁻¹(s))` to emit `+1` only when a key's integrated multiplicity crosses `≤ 0 → > 0`, and `-1` when it crosses `> 0 → ≤ 0`.
  - **Stratified & Recursive Queries:** Fixed-point recursion lifts a stream of relations into a **stream of streams** via `δ_0` (injecting at inner iteration `0`) and `∫` (summing inner iterations back to the outer clock, computable strictly when inner streams are zero almost everywhere—requiring termination).

**The Structural Memory Problem:** Every bilinear join, `distinct`, or non-linear aggregate introduces an integrator `I` storing the **complete historical Z-set of its input**. Without garbage collection, a DBSP circuit computing a join or `GROUP BY` over an infinite append-only stream grows monotonically at `Ω(T)` forever!

#### 4.2 Feldera's Waterline + Compiler Monotonicity Analysis + `ControlledFilter` GC Architecture

`Basis: source + documentation`

Direct inspection of `feldera/feldera` (`42a79b1cf0ee86b94335ec87138fb331ed0a8239`) reveals a complete, compiler-verified **decoupled event-time waterline GC architecture**:

1. **Waterline Operators (`crates/dbsp/src/operator/time_series/waterline.rs:15-122`):**
   - Feldera explicitly separates **event-time waterlines** from **DBSP logical clock ticks** (`waterline.rs:16-22`).
   - `waterline_monotonic(init, waterline_func)` computes `W[t] = max(W[t-1], waterline_func(max_key_in_batch[t]))` in `O(1)` per batch when the stream is indexed by a totally ordered timestamp key.
   - `waterline(init, extract_ts, least_upper_bound)` generalizes to arbitrary partial-order lattices (multi-column timestamps) via user-supplied `least_upper_bound`.
   - **Three Compiler Waterline Invariants (`InsertLimiters.java:105-112`):** (i) Every future non-`NULL` value arriving in the stream is `≥` the waterline (`NULL` has no assumed order position); (ii) a waterline is monotonically non-decreasing in every tuple component; (iii) a waterline itself is never `NULL`.
2. **Trace Retention APIs (`crates/dbsp/src/operator/trace.rs:75-250`):**
   - **`integrate_trace_with_bound`:** Zero-cost per-consumer lower bound when keys are ordered by time; effective retention bound is the minimum across consumers.
   - **`integrate_trace_retain_keys(bounds_stream, retain_key_func)` & `integrate_trace_retain_values` / `_last_n`:** Applies a general monotone filter predicate (`retain(ts_1, k) = false ∧ ts_2 ≥ ts_1 ⇒ retain(ts_2, k) = false`, `trace.rs:167-171`) to reclaim expired keys/values even when traces are *not* sorted by timestamp or carry multi-dimensional partial-order timestamps. Because all consumers of an integrated stream share one physical trace (`trace.rs:111-118`), **at most one global key-retention policy and one value-retention policy may attach to a stream**—enforced statically by `CheckRetain.java:18-71` (throwing `InternalCompilerError` on duplicate slots).
3. **Whole-Circuit Compiler Pass Pipeline (`MonotoneAnalyzer.java:90-163`, `InsertLimiters.java:89-160`, `MergeGC.java:43-120`):**
   - `SeparateIntegrators` inserts no-op boundaries between consecutive integrators; `DeltaExpandOperators` expands the SQL circuit into incremental delta form.
   - `Monotonicity` performs abstract interpretation over partially monotone tuple types (`PartiallyMonotoneTuple`, `ScalarMonotoneType`), tracking which output columns are monotone functions of `LATENESS`-annotated source columns using **saturating transfer functions** (`f(w) → MIN` below domain, `MAX` above domain, `InsertLimiters.java:114-127`).
   - `InsertLimiters` synthesizes:
     - `DBSPWaterlineOperator` nodes near `LATENESS`-annotated sources,
     - `DBSPControlledKeyFilterOperator` / `controlled_key_filter` (`controlled_filter.rs:28-138`) gates that **discard late tuples violating the waterline** and emit diagnostic records (`weight = +1`) to the `ERROR_TABLE_NAME` view (`MonotoneAnalyzer.java:69-87, 128-133`),
     - `DBSPIntegrateTraceRetainKeysOperator` and `DBSPIntegrateTraceRetainValuesOperator` nodes pruning integral traces behind the propagated waterline bounds.
   - `MergeGC` (`MergeGC.java:43-120`) reconciles shared integrals across multiple consumers: two retention policies `retain1` and `retain2` on the same trace merge into `retain1 OR retain2` (keeping any row needed by *either* consumer); if *any* consumer requires an unbounded full integral with no retention policy, GC is removed so that consumer never observes prematurely evicted state!

---

### 5. Event-Time Watermarks vs. Out-of-Order Late-Data Corruption

#### 5.1 Executable Micro-Probe 2A: Quantifying Waterline GC Soundness vs. Retraction Corruption

`Basis: execution + derived`

Running **Probe 2A** (`probe_pkg2.py`) compares an uncompacted full-history $\mathbb{Z}$-set equijoin oracle `I(A) ⋈ I(B)` against an incremental DBSP bilinear join engine with waterline `W(t) = max_seen_ts - L` (`L = 5`) and trace retention GC (`ts ≥ W(t)`) across three regimes:

```text
[2A] In-window bounded jitter + retractions (L=5, GC=on):
     peak_trace_entries=12 (uncompacted_oracle=380), final_waterline=195, dropped_late=0
     exact_match=True, mismatches=0, phantom_negative_weights=0
[2A] Late retraction crossing compacted waterline (GC=on, NO filter):
     peak_trace_entries=13 (uncompacted_oracle=98), final_waterline=45, dropped_late=0
     exact_match=False, mismatches=5, phantom_negative_weights=1
     sample_divergence (key -> (oracle_w, inc_w)):
       [((15, 15, 'a15', 48, 'b15_live'), (1, 0)),
        ((12, 12, 'a12', 12, 'b12_late'), (1, 0)),
        ((15, 48, 'a15_live', 15, 'b15'), (1, 0))]
[2A] Late retraction crossing compacted waterline (GC=on, controlled_filter=on):
     peak_trace_entries=13 (uncompacted_oracle=98), final_waterline=45, dropped_late=3
     exact_match=False, mismatches=6, phantom_negative_weights=0
```

**Exact Failure Mechanism Exposed by Probe 2A:**
1. **Within Declared Lateness (`ts ≥ W(t)`):** Trace memory drops by **$31.7\times$** (`12` entries vs. `380`, strictly `O(L)` independent of run duration `T`), while producing **bit-exact** agreement with the full-history oracle even with `-1` retractions inside the active window.
2. **Unfiltered Late Retraction (`ts < W(t)` without `controlled_key_filter`):** Two distinct corruptions occur simultaneously:
   - *Missed joins:* A late insert `(12, ts=12)` misses its already-evicted join partner in `trace_a` (`oracle_w=1, inc_w=0`).
   - ***Non-Idempotent Phantom Negative Weights:*** When a late `-1` retraction on key `15` (`ts=10`) crosses into the bilinear join `(ΔA ⋈ trace_b)` while `trace_b` still holds a *newer* live tuple `(15, ts=48, +1)`, the cross-term produces an output record with **weight `-1`** (`phantom_negative_weights=1`) for a pair that was never positively emitted—permanently violating Z-set positivity and breaking downstream `distinct`, `COUNT`, and `SUM` invariants (`I(ΔS) ≠ S`)!
3. **Filtered Late Retraction (`controlled_key_filter` active, Feldera's actual design):** Dropping tuples with `ts < waterline` into the error stream **eliminates all phantom negative weights (`phantom_negative_weights=0`)** and protects internal trace invariants—while honestly sacrificing exactness relative to an infinite-memory oracle on the `3` late-violating events (`mismatches=6`).

#### 5.2 Comparative Trade-Off Matrix Across Streaming & IVM Paradigms

`Basis: normative + source + execution + derived`

| Engine / Model | Time / Progress Primitive | Memory Bound Mechanism | Behavior on Stalled Partition / Straggler | Behavior on Out-of-Order Late Retraction | Cyclic / Recursive Dataflow Support | Mechanized Formalization |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Apache Beam / Flink (`The Dataflow Model`, PVLDB 2015)** | Heuristic event-time watermarks + `allowed_lateness` + triggers | Window state evicted when `watermark > window_end + allowed_lateness` | Heuristic watermark stalls unless `withIdleness` heuristic advances it (risking false lateness) | Dropped or side-output past `allowed_lateness`; retractions (`accumulatingAndRetracting`) corrupt downstream incremental joins if pre-image evicted | Limited (no general nested-iteration progress frontiers) | Informal / operational |
| **Timely + Differential Dataflow (`TimelyDataflow/*`)** | Exact multi-dimensional `Antichain` capabilities (`PathSummary`, `Refines`) | Dual frontiers: `logical_frontier` (retraction cancellation) + `physical_frontier` (`4×`-fueled `Spine` merges) | **Global `Antichain` freezes → `Ω(T)` spine memory growth (OOM)** (Probe 2B) | **Impossible past frontier** (capability discipline forbids emitting timestamps `< frontier`; zero silent corruption) | **First-class** nested loops `(epoch, iter)` with strict cycle summaries | Isabelle/HOL AFP `Progress_Tracking` (Brun et al., ITP 2021) |
| **Feldera `DBSP` (`feldera/feldera`)** | Logical clock ticks **decoupled** from event-time `waterline` lattice | Whole-circuit `MonotoneAnalyzer` + `InsertLimiters` (`retain_keys`/`values`, `OR`-merged in `MergeGC`) | Waterline advances based on max observed timestamp (does not freeze on idle partitions, risking lateness if straggler resumes!) | `controlled_key_filter` drops tuples `< waterline` to error view (`0` phantom negative weights, explicit late-drop divergence; Probe 2A) | Stratified & recursive circuits via `δ_0` / `∫` (requires finite-support inner termination) | Lean `3.51.1` core algebra (`tchajed/database-stream-processing-theory`) |
| **`Stream Types` / `Delta` (`alpha-convert/delta`)** | Explicit in-band structural punctuation (`CatPunc`, `PlusPuncA/B`) | Static ordered bunched typing (`;` vs. `,`) rejects unbounded buffering at compile time | Blocks only downstream of unpunctuated sequential boundary (`TyCat`) | Must be explicitly typed in stream algebra (no silent out-of-order violations) | Tail-recursive `TyStar` stream automata | Meta-theory proved in Cutler et al. (PLDI 2024) |
| **`Flo` / `Hydro` (`hydro-project/hydro`)** | Type-level `Bounded` / `Unbounded` + `TotalOrder` / `NoOrder` markers | Compile-time rejection of blocking operators on `Unbounded` (`IsBounded`) unless explicitly `sliced!` | `Unbounded` operators remain progressive; `sliced!` batches explicitly mark nondeterministic tick boundaries | Depends on embedded lattice/CRDT or explicit state-management operator | Nested tick scopes & cyclic `defer_tick` graphs | Formal operational semantics (`Flo`, `arXiv:2411.08274`) |

---

## Boundaries

1. **Formal Verification of Feldera's `MonotoneAnalyzer` / `InsertLimiters` Compiler Passes — `unknown` / `not examined` as mechanized proof:** While DBSP's core algebraic incrementalization (`D`, `I`, `z⁻¹`, `ZSet`, relational operators, recursion) is mechanized in Lean `3.51.1` (`tchajed/database-stream-processing-theory`, `fb6ff4416108710448ccd87473c5513c1a1179ea`), that Lean repository does **not** formalize Feldera's Java SQL monotonicity abstract interpretation (`MonotoneAnalyzer.java`, `InsertLimiters.java`, `MergeGC.java`) or `integrate_trace_retain_keys` trace garbage collection. Soundness of `InsertLimiters` saturating transfer functions rests on compiler engineering invariants and tests, not a mechanized proof.
2. **Differential Dataflow `Spine` Memory Bounds Under Non-Abelian Semigroups — `known not to apply`:** Logical compaction cancels opposite weights (`+1 + (-1) = 0`) strictly when the difference type forms an `Abelian` group (or admits zero cancellation). For monotonic max/min semigroups without inverses (or append-only collections with no retractions), `logical_frontier` coalesces timestamps into single records per `(k, v)` (`O(|unique keys|)` rather than `O(T)` update history), but cannot shrink below the number of distinct surviving `(k, v)` pairs without an application-level waterline eviction predicate.
3. **Non-Terminating Recursive Queries in DBSP and Timely — `unsupported` for bounded memory:** In DBSP, stream elimination `∫` (`tchajed/database-stream-processing-theory/src/stream_elim.lean`) is well-defined only for inner streams that become zero almost everywhere; non-monotonic recursive queries (e.g., unstratified negation oscillating between `+1` and `-1` across inner iterations) diverge infinitely in both DBSP and Differential Dataflow (`(epoch, iter)` never drops capabilities at `epoch`, permanently freezing outer frontiers).
4. **Disk-Backed Spill / LSM Compaction Throughput (`Feldera` Storage Engine & `Materialize`) — `not examined`:** This report characterizes **asymptotic state boundedness** (`O(W)` vs. `Ω(T)`) and **algebraic/frontier soundness**. Empirical disk-spill latency, `buffer-cache` eviction policies, and RocksDB/storage-backed spine I/O amplification in `feldera/feldera` (`crates/buffer-cache`) were not benchmarked.
5. **Distributed Clock Skew & Partition-Idle Heuristics in Apache Flink / Beam — `not examined` in source:** While Akidau et al. (PVLDB 2015) defines the normative watermark/trigger/allowed-lateness contract, concrete production implementations of `WatermarkStrategy.withIdleness` in `apache/flink` were not inspected at source level; their exact failure interaction with network partitions is recorded as derived from the heuristic-watermark model.
6. **Runtime Enforcement of Strict Cycle Increment in `TimelyDataflow/timely-dataflow` — `unsupported` as a hard failure:** As verified in `timely/src/progress/reachability.rs:217-220`, `Builder::build` logs `"Cycle detected without timestamp increment"` to stdout and returns a live `Tracker` rather than returning `Result::Err` or panicking; callers requiring fail-closed cycle rejection must invoke `Builder::is_acyclic()` explicitly before `build()`.

---

## Evidence

All upstream Git revisions, source line ranges, and literature DOIs were verified on `2026-11-19`.

### Primary Upstream Source Inspections

- **`TimelyDataflow/timely-dataflow` (`5d82cb0bd4e43a6a47c59383fb2475e6842c0a57`):**
  - `timely/src/progress/timestamp.rs:14-177`: `Timestamp`, `PathSummary<T>` (`results_in`, `followed_by`, monotonicity & overflow contracts), `Refines<T>` (`to_inner`, `to_outer`, `summarize`).
  - `timely/src/progress/frontier.rs:20-260`: `Antichain<T>` (`SmallVec<[T; 1]>`, `insert`, `less_than`, `less_equal`).
  - `timely/src/progress/reachability.rs:146-260, 650-900`: `Builder::build` non-fatal `is_acyclic()` stdout warning (`lines 215-223`), `Tracker::propagate_all` two-phase `MutableAntichain` + `BinaryHeap<Reverse<...>>` loop (`lines 650-764`), `summarize_outputs` reverse semi-naive fixpoint (`lines 858-900`).
- **`TimelyDataflow/differential-dataflow` (`e7c24703f4b1935cd6c99779ed0c140b0fea8ac6`):**
  - `differential-dataflow/src/trace/mod.rs:26-247`: `ExertionLogic`, `Span`, `TraceReader` (`spans_through`, `set_logical_compaction`, `set_physical_compaction`), `Trace::exert`.
  - `differential-dataflow/src/trace/implementations/spine_fueled.rs:1-180`: Geometric `2^i` layer accounting, `4×` fuel proportionality invariant (`lines 38-56`), `Merger` trait (`lines 109-124`), `Spine` struct with separate `logical_frontier` and `physical_frontier` (`lines 156-170`).
- **`feldera/feldera` (`42a79b1cf0ee86b94335ec87138fb331ed0a8239`):**
  - `crates/dbsp/src/operator/time_series/waterline.rs:15-122`: `waterline_monotonic` and general lattice `waterline` API and event-time vs. DBSP logical-time distinction.
  - `crates/dbsp/src/operator/trace.rs:75-250`: `integrate_trace_with_bound`, `integrate_trace_retain_keys`, `integrate_trace_retain_values`, `integrate_trace_retain_values_last_n`, global single-policy contract and monotonicity requirement (`lines 165-171`).
  - `crates/dbsp/src/operator/controlled_filter.rs:12-138`: `controlled_key_filter` and `controlled_value_filter` emitting discarded late records to an error `OrdZSet<E>` stream.
  - `sql-to-dbsp-compiler/SQL-compiler/src/main/java/org/dbsp/sqlCompiler/compiler/visitors/outer/monotonicity/MonotoneAnalyzer.java:30-169`: Full pass order (`SeparateIntegrators` → `DeltaExpandOperators` → `Monotonicity` → `InsertLimiters` → `MergeGC` → `CheckRetain`) and `ERROR_TABLE_NAME` topological ordering.
  - `.../monotonicity/InsertLimiters.java:89-160`: Waterline invariants (`non-NULL`, monotone non-decreasing, lower bound on future arrivals) and saturating transfer table (`MIN`/`MAX`).
  - `.../monotonicity/MergeGC.java:43-120`: Shared-integral `retain1 OR retain2` merging and GC removal when any consumer keeps a full integral.
  - `.../monotonicity/CheckRetain.java:18-71`: Enforcing at most one `Key` and one `Value` retention policy per trace.
- **`tchajed/database-stream-processing-theory` (`fb6ff4416108710448ccd87473c5513c1a1179ea`):**
  - `leanpkg.toml` (`lean:3.51.1`) and `README.md`: Module map of mechanized `stream.lean`, `operators.lean`, `linear.lean`, `incremental.lean`, `circuits.lean`, `zset.lean`, `relational.lean`, `relational_incremental.lean`, `stream_elim.lean`, `recursive.lean`, `aggregation.lean`.
- **`alpha-convert/delta` (`20db7e6fd4c0970b04e60abeea2213aaaaba8c31`):**
  - `README.md:1-91`: `runningSum` example and static rejection of list-reversal `snoc(x : Int; xs : Int*)`.
  - `src/Types.hs:40-250`: `TyF` (`TyCat`, `TyPar`, `TyPlus`, `TyStar`), `CtxStruct` (`SemicCtx`, `CommaCtx`), `isNull`, `ValueLike` (`hasType`, `deriv`).
  - `src/Event.hs:17-88`: `Event` (`PlusPuncA`, `PlusPuncB`, `CatPunc`), `hasType CatPunc (TyCat s _)` requiring `isNull s`, and event derivatives.
- **`hydro-project/hydro` (`fbaccddb35111327f96922259d60dc1607395545`):**
  - `hydro_lang/src/live_collections/boundedness.rs:14-82`: `Boundedness`, `Bounded`, `Unbounded`, `PreserveOrderIfBounded`, `AggregatedOptional`, and `IsBounded` diagnostic gate.

### Peer-Reviewed Literature

- A. Arasu, B. Babcock, S. Babu, J. McAlister, J. Widom, *"Characterizing Memory Requirements for Queries over Continuous Data Streams"*, ACM TODS 29(1), 2004 (`DOI: 10.1145/974750.974756`; preliminary ACM PODS 2002).
- P. A. Tucker, D. Maier, T. Sheard, L. Fegaras, *"Exploiting Punctuation Semantics in Continuous Data Streams"*, IEEE TKDE 15(3), 2003 (`DOI: 10.1109/TKDE.2003.1198390`).
- K. Mamouras, M. Raghothaman, R. Alur, Z. G. Ives, S. Khanna, *"StreamQRE: Modular Specification and Efficient Evaluation of Quantitative Queries over Streaming Data"*, ACM PLDI 2017 (`DOI: 10.1145/3062341.3062369`).
- J. W. Cutler, C. Watson, E. Nkurumeh, P. Hilliard, H. Goldstein, C. Stanford, B. C. Pierce, *"Stream Types"*, PACMPL 8(PLDI), 2024 (`DOI: 10.1145/3656434`).
- S. Laddad, A. Cheung, J. M. Hellerstein, M. Milano, *"Flo: A Semantic Foundation for Progressive Stream Processing"*, `arXiv:2411.08274` (`DOI: 10.48550/arXiv.2411.08274`, 2024).
- D. G. Murray, F. McSherry, R. Isaacs, M. Isard, P. Barham, M. Abadi, *"Naiad: A Timely Dataflow System"*, ACM SOSP 2013 (`DOI: 10.1145/2517349.2522738`).
- M. Abadi & M. Isard, *"Timely Dataflow: A Model"*, IFIP FORTE 2015 (`DOI: 10.1007/978-3-319-19195-9_1`).
- M. Brun, S. Decova, A. Lattuada, D. Traytel, *"Verified Progress Tracking for Timely Dataflow"*, ITP 2021 (`DOI: 10.4230/LIPIcs.ITP.2021.10`) and Isabelle/HOL Archive of Formal Proofs entry `Progress_Tracking` (2021).
- F. McSherry, D. G. Murray, R. Isaacs, M. Isard, *"Differential Dataflow"*, CIDR 2013.
- M. Budiu, T. Chajed, F. McSherry, L. Ryzhyk, V. Tannen, *"DBSP: Automatic Incremental View Maintenance for Rich Query Languages"*, PVLDB 16(7), pp. 1601–1614, 2023 (`DOI: 10.14778/3587136.3587137`; preliminary `arXiv:2203.16684`, 2022).
- T. Akidau et al., *"The Dataflow Model: A Practical Approach to Balancing Correctness, Latency, and Cost in Massive-Scale, Unbounded, Out-of-Order Data Processing"*, PVLDB 8(12), 2015 (`DOI: 10.14778/2824032.2824076`).

### Execution Evidence (`Python 3.13.15`, Linux x86_64, `2026-11-19`)

- **Probe 2A (DBSP Bilinear Join & Waterline Trace GC):**
  - In-window bounded jitter (`L = 5`, 200 ticks, in-window `-1` retractions): `peak_trace_entries = 12` vs. `380` uncompacted, `exact_match = True`, `phantom_negative_weights = 0`.
  - Late retraction crossing compacted waterline (`GC = on`, unfiltered): `mismatches = 5`, `phantom_negative_weights = 1`.
  - Late retraction with `controlled_key_filter`: `dropped_late = 3`, `mismatches = 6`, `phantom_negative_weights = 0`.
- **Probe 2B (Timely Cyclic `(epoch, iter)` Reachability):**
  - Healthy `feedback = (0, +1)` across 500 epochs: `is_acyclic_zero_summary = True`, `final_output_frontier = [(500, 0)]`, `max_uncompacted_epoch_span = 0`.
  - Stalled partition holding `(0, 0)` across 500 epochs: `final_output_frontier = [(0, 0)]`, `max_uncompacted_epoch_span = 500`.
  - Zero-increment cycle `feedback = (0, 0)`: `is_acyclic_zero_summary = False`, `output_frontier_after_drop = [(0, 0)]` (permanent deadlock).

---

## Revalidation

### 1. Cheapest Discriminating Upstream Source Diffs

- **Timely non-incrementing cycle handling:** Diff `timely/src/progress/reachability.rs` (`Builder::build` and `Tracker::propagate_all`) in `TimelyDataflow/timely-dataflow` against `5d82cb0bd4e43a6a47c59383fb2475e6842c0a57` to test whether `!self.is_acyclic()` has been promoted from a stdout warning to a hard panic/`Result::Err`.
- **Differential compaction interface:** Diff `differential-dataflow/src/trace/mod.rs` (`TraceReader::set_logical_compaction`, `set_physical_compaction`) and `spine_fueled.rs` against `e7c24703f4b1935cd6c99779ed0c140b0fea8ac6`.
- **Feldera monotonicity & waterline GC pipeline:** Diff `MonotoneAnalyzer.java`, `InsertLimiters.java`, `MergeGC.java`, and `CheckRetain.java` in `feldera/feldera` against `42a79b1cf0ee86b94335ec87138fb331ed0a8239` to check whether multi-policy retention or mechanized verification of `InsertLimiters` has been introduced.
- **DBSP Lean formalization:** Check `tchajed/database-stream-processing-theory` (`fb6ff4416108710448ccd87473c5513c1a1179ea`) for any Lean 4 port or formalization of `waterline` / `retain_keys` trace garbage collection.

### 2. Self-Contained Executable Revalidation Probe (Python 3.10+, Standard Library Only)

Run the following standalone script to revalidate both the DBSP waterline GC vs. late-retraction phantom-negative-weight hazard (Probe 2A) and Timely Dataflow's stalled-partition leak & zero-increment cycle deadlock (Probe 2B) in under 1 second:

```bash
python3 - <<'PY'
from collections import defaultdict
import heapq

# --- Probe 2A: DBSP Bilinear Join + Waterline GC + Late Retraction ---
def zadd(a, b):
    o = dict(a)
    for k, w in b.items():
        nw = o.get(k, 0) + w
        if nw == 0: o.pop(k, None)
        else: o[k] = nw
    return o

def zjoin(za, zb):
    ib = defaultdict(list)
    for (jk, tsb, vb), wb in zb.items(): ib[jk].append((tsb, vb, wb))
    out = {}
    for (jk, tsa, va), wa in za.items():
        for tsb, vb, wb in ib.get(jk, ()):
            r = (jk, tsa, va, tsb, vb)
            nw = out.get(r, 0) + wa * wb
            if nw == 0: out.pop(r, None)
            else: out[r] = nw
    return out

def run_dbsp(steps, L, filt):
    fa, fb, ta, tb, inc, wl, peak, full_peak, dropped = {}, {}, {}, {}, {}, -10**9, 0, 0, 0
    for da, db in steps:
        fa, fb = zadd(fa, da), zadd(fb, db)
        full_peak = max(full_peak, len(fa) + len(fb))
        ts = [k[1] for k in da] + [k[1] for k in db]
        if ts: wl = max(wl, max(ts) - L)
        if filt:
            dropped += sum(1 for k in da if k[1] < wl) + sum(1 for k in db if k[1] < wl)
            da = {k: w for k, w in da.items() if k[1] >= wl}
            db = {k: w for k, w in db.items() if k[1] >= wl}
        d = zadd(zadd(zjoin(da, db), zjoin(ta, db)), zjoin(da, tb))
        inc = zadd(inc, d)
        ta = {k: w for k, w in zadd(ta, da).items() if k[1] >= wl}
        tb = {k: w for k, w in zadd(tb, db).items() if k[1] >= wl}
        peak = max(peak, len(ta) + len(tb))
    ora = zjoin(fa, fb)
    mis = sum(1 for k in set(ora) | set(inc) if ora.get(k, 0) != inc.get(k, 0))
    neg = sum(1 for w in inc.values() if w < 0)
    return peak, full_peak, mis, neg, dropped

w1 = [({(t, t, f"a{t}"): 1, **({(t-3, t-3, f"a{t-3}"): -1} if t > 3 and t % 10 == 0 else {})}, {(t, t, f"b{t}"): 1}) for t in range(1, 201)]
assert run_dbsp(w1, 5, False) == (12, 380, 0, 0, 0)
w2 = w1[:50] + [({(10, 10, "a10"): -1}, {}), ({}, {(12, 12, "b12_late"): 1}),
                ({(15, 48, "a15_live"): 1}, {(15, 48, "b15_live"): 1}), ({(15, 10, "a15_never"): -1}, {})]
p_unfilt = run_dbsp(w2, 5, False)
p_filt = run_dbsp(w2, 5, True)
assert p_unfilt[3] == 1 and p_filt[3] == 0 and p_filt[4] == 3
print("Probe 2A passed:", {"in_window": (12, 380, 0, 0, 0), "late_unfiltered": p_unfilt, "late_filtered": p_filt})

# --- Probe 2B: Timely Cyclic Antichain Stall & Zero-Increment Deadlock ---
def lt(a, b): return a[0] <= b[0] and a[1] <= b[1] and a != b
class MA:
    def __init__(self): self.c, self.f = defaultdict(int), []
    def upd(self, t, d):
        old = set(self.f); nc = self.c[t] + d
        if nc == 0: self.c.pop(t, None)
        else: self.c[t] = nc
        pos = [x for x, v in self.c.items() if v > 0]
        self.f = [x for x in sorted(pos) if not any(lt(y, x) for y in pos)]
        ns = set(self.f)
        return [(x, 1) for x in sorted(ns - old)] + [(x, -1) for x in sorted(old - ns)]

class Tracker:
    def __init__(self, sums, edges):
        self.s, self.e = sums, defaultdict(list)
        for u, v in edges: self.e[u].append(v)
        self.p, self.imp = {n: MA() for n in sums}, {n: MA() for n in sums}
    def upd(self, n, t, d):
        wl = [(t, n, delta) for t, delta in self.p[n].upd(t, d)]
        heapq.heapify(wl)
        while wl:
            t, u, delta = heapq.heappop(wl)
            while wl and wl[0][0] == t and wl[0][1] == u: delta += heapq.heappop(wl)[2]
            if delta == 0: continue
            for it, idl in self.imp[u].upd(t, delta):
                nt = (it[0] + self.s[u][0], it[1] + self.s[u][1])
                for v in self.e[u]: heapq.heappush(wl, (nt, v, idl))

edges = [(0, 1), (1, 2), (2, 1), (1, 3)]
t_ok = Tracker({0: (0, 0), 1: (0, 0), 2: (0, 1), 3: (0, 0)}, edges)
t_ok.upd(0, (0, 0), 2)
for ep in range(500): t_ok.upd(0, (ep + 1, 0), 1); t_ok.upd(0, (ep, 0), -1)  # P1 stalled at (0,0)!
assert t_ok.imp[3].f == [(0, 0)]
t_bad = Tracker({0: (0, 0), 1: (0, 0), 2: (0, 0), 3: (0, 0)}, edges)
t_bad.upd(0, (0, 0), 1); t_bad.upd(0, (0, 0), -1)
assert t_bad.imp[3].f == [(0, 0)]  # Permanent deadlock despite zero external capabilities!
print("Probe 2B passed: stalled_frontier=", t_ok.imp[3].f, "deadlocked_zero_cycle=", t_bad.imp[3].f)
PY
```
