# Salsa and rustc query systems: when fine granularity earns its complexity

## Summary

Salsa and rustc show why a fine-grained query graph can make repeated compiler work fast, but they also show the price of making that graph trustworthy. The useful unit is not “an item” by default. It is the smallest computation for which the host can give a stable key, expose every semantically relevant input through the query boundary, define result equality, and afford the retained dependency state. Red-green validation and projection queries then let unchanged results stop invalidation from spreading.

That lesson does not transfer automatically to Anneal's opaque tool boundaries. The pinned Aeneas path has function-local translation work, but its public translation entrypoint rebuilds whole-crate context and does not expose an edit/invalidation protocol. Wrapping those calls in item-sized Salsa keys would create a finer cache without creating the missing dependency contract. The conservative Anneal baseline is therefore a coarse query/DAG boundary around whole normalized stage inputs, with finer queries only inside subsystems whose semantic dependencies Anneal or an upstream service actually owns.

Fine-grained queries should be an earned optimization. They are attractive when representative interactive workloads repeatedly ask for overlapping derived facts and measurements show that coarse recomputation dominates latency. They should be rejected or delayed when keys are unstable, dependencies cross an opaque stage, output equality is expensive or misleading, memory retention dominates, or cycle/cancellation semantics are not yet explicit.

## Applicability

The Salsa mechanism is described at `salsa-rs/salsa@a7f8c558555f179ca02f6bdf7397d1317f91aa43`, the default-branch revision observed on 2026-09-30. The report uses the current Salsa book plus selected implementation and repository-history evidence. Salsa is a reusable incremental-computation framework; its guarantees apply only when an application represents inputs and computation through Salsa's model.

The rustc mechanism is described primarily from `rust-lang/rustc-dev-guide@8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85`. That guide documents rustc's query and red-green incremental architecture. This report does not claim that every implementation detail in the guide is a normative promise of the exact 2026 compiler source.

Anneal-specific conclusions are derived against `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`, and against the current reference report on Aeneas incremental translation whose `REPORT.md` blob is `966b5953644d8c9a766ae900e8b137616c501be8`. Those sources constrain the judgment; neither Salsa nor rustc is proposed as an adopted Anneal architecture.

The historical discussion uses first-party Rust project publications from 2016 and 2021 and Salsa Git history. It reconstructs why the mechanisms exist and how their maintenance surface evolved. It does not treat historical implementation details as current behavior unless current documentation or source also supports them.

## Findings

### A query engine is sound only over the inputs it can see

Salsa presents a program as queries from keys to values. Inputs are explicit mutable roots; tracked functions are intended to be pure. When a tracked function runs, Salsa records the other tracked values it reads. A later revision can reuse the memoized result if those dependencies have not changed. If a dependency may have changed, Salsa re-executes and can “backdate” the result when the new value compares equal to the old value.

Rustc's documented model has the same core shape. Query providers are treated as pure functions, query-to-query reads construct the dependency graph, and persistent incremental compilation relies on stable identities for query keys and fingerprints for prior results. This only works because semantically relevant reads pass through mechanisms the compiler can record, or are handled by explicit escape hatches such as always-evaluate queries.

The architectural requirement is therefore stronger than “memoize a function.” A reusable query needs an input closure. Ambient filesystem state, process globals, tool configuration, network state, hidden compiler state, or another untracked effect can invalidate the implication from “recorded dependencies are unchanged” to “the old result is still valid.”

**Anneal implication.** A Salsa-shaped wrapper around Charon, Aeneas, Lean, or another subprocess does not make that subprocess incrementally transparent. Fine-grained reuse is justified only after the boundary exposes, or Anneal otherwise proves, the complete dependency identity relevant to the reused result. Until then, the stage input itself should be coarse enough to contain the hidden dependency surface.

Basis: **documentation** for current Salsa and rustc; **derived** application to Anneal.

### Granularity is valuable because unchanged intermediate values stop invalidation

The first-order benefit of fine granularity is not simply that each unit is small. It is that intermediate equality can stop a change from propagating.

Rustc's guide explains why a naive dependency walk produced too many false positives: small source changes often appear to affect large parts of the compiler graph. Red-green evaluation interleaves validation and recomputation. A dependency whose inputs changed may be recomputed; if its output fingerprint remains equal, it becomes green and its dependents can remain green without executing.

Rustc also uses projection queries as change-propagation firewalls. A coarse query may produce a monolithic value that changes often, while smaller keyed projection queries expose individual pieces. Dependents of unchanged projections remain reusable even when the monolithic producer is red. The variance implementation gives a concrete example: `crate_variances` is whole-crate inference, while `variances_of` projects one item's result. Downstream users depend on the projection, so an unrelated variance change does not force every consumer to rerun.

This is a more useful model for Anneal than the slogan “queries should be per item.” The profitable boundary is where a stable, comparatively cheap equality test separates consumers whose semantic input did not change. Sometimes that is an item. Sometimes it is a whole normalized crate, a declaration group, an obligation set, or a generated module.

Basis: rustc **documentation**; Anneal unit-selection rule is **derived**.

### Fine queries have per-node costs; making everything a query can lose

A finer graph creates more keys, memo entries, dependency edges, equality or fingerprint work, validation walks, and retained identities. Rustc's guide explicitly notes that stable fingerprinting is expensive and can make incremental compilation slower than non-incremental compilation. It also provides `no_hash` and `eval_always` mechanisms for computations where hashing or dependency recording costs more than the reuse they enable.

Salsa exposes the same tradeoff from a reusable-framework angle. Memoized tracked-function values are unbounded by default. Optional LRU limits memoized values for a tracked function, but the current tuning guide states that LRU eviction removes values, not query keys or dependency metadata. Salsa separately reclaims stale tracked outputs and unused low-durability interned values. More fine-grained keys therefore still enlarge retained graph/state even when memo values are capped.

Durability is another optimization rather than a new correctness source. Salsa can skip walking individual dependencies when a query depends only on higher-durability inputs and the current revision changed only lower-durability inputs. The application must still classify those inputs correctly.

**Anneal implication.** Query granularity should be chosen by measured saved work versus the cost of keys, edge tracking, validation, hashing/equality, memory retention, and debugging. A coarse node is not an architectural failure when its inner tool already owns the fine graph or when the cost of reconstructing that graph outside the tool exceeds the work saved.

Basis: Salsa and rustc **documentation**; Anneal cost rule is **derived**.

### Cancellation is part of the revision model, not a substitute for publication fencing

Current Salsa coordinates mutable revisions with concurrent readers. Before mutating an input through a mutable database handle, Salsa cancels parallel handles and waits for them to finish. Its tuning guide states that accesses to intermediate queries are cancellation points; a long-running query that performs no intermediate query reads may need an explicit cancellation check. Cancellation is implemented through unwinding, so the engine must keep its internals panic-safe.

That machinery answers an in-process question: what happens to computations for an older database revision when a writer wants to advance the database? It does not establish that an externally visible result belongs to the latest Anneal source/model generation. A result can be internally consistent for the snapshot it computed and still be stale by the time an editor or API response would publish it.

**Anneal implication.** If Anneal adopts a query engine, cancellation can reduce wasted work and stop old computations from retaining locks or resources. Generation/request identity and a final publication check remain separate. The system must reject a completed result whose source/model generation is no longer authoritative even if the query engine itself completed it correctly.

Basis: Salsa **documentation/source model** plus current Anneal design constraints; publication distinction is **derived**.

### Cycles force semantic choices that coarse orchestration can often avoid

A general query graph cannot treat cycles as an implementation detail. Current Salsa panics by default when a query re-enters an active cycle. It also supports fixed-point iteration, but only under stated semantic preconditions: participating queries should be deterministic and monotone over a finite-height partial order. Salsa caps iteration at 200 and also supports explicit fallback values.

Rustc's developer guide records a more conservative historical choice. Rustc detects query cycles and reports them as errors. The compiler once had a cycle-recovery mechanism, but the guide says it was removed because the theoretical consequences, especially for incremental compilation, were unclear.

This is a useful warning for Anneal. Turning a recursive proof or dependency relation into a query cycle does not define the relation's semantics. A fixed-point engine is appropriate only when the underlying relation actually has fixed-point meaning and the convergence assumptions are stated. Other cycles should remain errors or be broken by a higher-level phase boundary.

Basis: Salsa and rustc **documentation**; Anneal rule is **derived**.

### The maintenance history shows that invalidation machinery is a correctness subsystem

Rust's 2016 incremental-compilation announcement framed the project as a response to edit-compile latency and explicitly warned that extensive regression testing was still needed to ensure incrementally compiled programs were correct. The architecture decomposed compilation into cacheable intermediate computations and tracked the dependency graph among them.

In May 2021, Rust 1.52.1 temporarily disabled incremental compilation by default after newly enabled fingerprint verification exposed longstanding incremental-cache bugs. The Rust compiler team stated that the bugs could cause miscompilations and that some failures came from inconsistencies between cached incremental state and values recomputed in the current invocation. The incident is direct historical evidence that a reuse engine's validation layer is correctness-critical, not merely a performance cache.

Salsa's own repository history shows continuing engineering in the same area. The newer `salsa-2022` implementation coexisted with the older implementation and replaced it in 2024 (`38a44eef879be5eca1ce94c09637b23b3a97a529`). Subsequent history includes a 2025 cycle-handling rewrite for fixed-point iteration (`095d8b2b8115c3cf8bf31914dd9ea74648bb7cf9`), a 2025 LRU change whose commit message says the previous immediate eviction behavior was unsound (`201704c5d185187905d0d8c0a963acd5593b19fe`), and 2026 fixes for out-of-order cycle-head verification (`0946cbd6478cf2bddfc9ac65b3c254c1f1b1bf95`), lost accumulator values when a memoized query skipped execution (`c3d88eb8671d09e1a175aa4d4b391a6242d2d123`), and guarding unvalidated interned/memo state (`c10e4ade12f6196bbda2a3bc76191eb4e176f25a`).

These commits do not show that Salsa is unusually unreliable. They show that once an engine combines memo reuse, retained identities, cycles, cancellation, side-channel outputs, reclamation, persistence, and concurrency, correctness spans interactions among those features. Anneal would inherit that class of maintenance burden if it owned a similarly rich graph.

Basis: first-party Rust **documentation/history** and Salsa **repository history**; maintenance interpretation is **derived**.

### Aeneas demonstrates why compiler item granularity does not transfer across an opaque translator

The current reference report for Aeneas `nightly-2026.06.03` finds declaration-local structure but no incremental translation protocol. `translate_crate_to_pure` creates a fresh whole-crate context, recomputes the crate-wide use graph and analyses, translates the selected declarations, and later extraction performs globally coupled naming and dependency/SCC work. Function translation is individually decomposed and parallelized, but each function is interpreted relative to shared maps and whole-crate context.

That is precisely the situation where a superficial query decomposition is dangerous. An outer engine can assign one key per Aeneas function, but unless it can enumerate every shared input that can change that function's translation, its dependency graph is incomplete. Rustc's success with item-oriented queries does not supply the missing Aeneas invalidation relation because rustc records dependencies inside the compiler operations that compute those items.

The useful near-term combination is layered: Anneal can use coarse stage queries to cache or schedule complete normalized LLBC/Aeneas results, while Aeneas continues to own its internal whole-crate semantics. If Aeneas later exposes a supported incremental service or explicit dependency model, Anneal can move the boundary inward without changing the outer result/publication contract.

Basis: current reference **source-derived report** plus Salsa/rustc **documentation**; cross-system conclusion is **derived**.

### A small hybrid graph captures much of the benefit without claiming universal incrementality

The evidence supports a staged architecture rather than a binary choice between “no query system” and “everything is Salsa.” A minimal Anneal graph can give stable identities to the coarse work that Anneal already owns: acquire a source snapshot, obtain/normalize LLBC, run Aeneas translation, prepare Lean input, check proof obligations, and assemble a result for one generation. Such nodes can support demand-driven execution, in-flight sharing, cancellation routing, and coarse reuse without pretending to know dependencies hidden inside upstream tools.

Finer queries are most defensible inside Anneal-owned transformations where inputs are already explicit. Examples might include indexing a normalized model, mapping a stable source/model subject to obligations, formatting diagnostics from an immutable result, or projecting one small value from a larger host-owned analysis. Each finer boundary should answer four questions before it becomes reusable state:

1. What stable key means “the same logical computation” across the intended revisions?
2. What complete set of semantic inputs can change the result?
3. What equality or fingerprint is strong enough to stop invalidation without hiding a meaningful change?
4. What is the lifecycle of memo values, keys, edges, side outputs, and stale generations?

If the answers require reconstructing an upstream compiler's private semantics, the boundary belongs upstream or should stay coarse.

Basis: **derived synthesis** from Salsa, rustc, Aeneas, and Anneal design authority.

### Conditional judgment

Anneal should not adopt item-granular Salsa-style reuse as an architectural default. It should keep the outer graph coarse enough that every node has an auditable input closure, then split nodes only where measurements and semantic ownership justify the extra machinery.

A finer query boundary earns its complexity when all of the following hold:

- representative interactions repeatedly demand overlapping sub-results;
- the saved recomputation is material compared with dependency tracking, equality/fingerprinting, and retained-memory cost;
- stable keys survive the edits across which reuse is desired;
- every semantically relevant input is explicit or conservatively represented;
- result equality corresponds to the downstream notion of “unchanged”;
- cycles have deliberate semantics or remain errors;
- cancellation and stale-generation rejection are explicit; and
- there is a practical oracle or regression strategy that compares incremental results with clean recomputation.

If any of the semantic conditions fail, recompute at a coarser boundary. If only the performance conditions fail, keep the sound coarse design until profiling shows that finer granularity is worth maintaining.

This is derived architecture guidance, not adopted Anneal policy. `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` remain authoritative.

## Boundaries

- No Salsa, rustc, Charon, Aeneas, Lean, or Anneal benchmark was executed for this report. It does not establish a quantitative threshold where fine-grained queries become worthwhile.
- Current Salsa behavior is described from project documentation plus selected source/history at `a7f8c558...`. The report does not audit every Salsa implementation path or prove the framework's soundness.
- Rustc behavior is described primarily from the rustc developer guide at `8ae6c255...`, not from a complete audit of the corresponding compiler source revision. The guide is treated as first-party documentation, not a normative specification.
- The Rust 1.52.1 incident demonstrates real correctness risk in incremental-cache validation. It does not imply that the same bug class exists in current rustc or current Salsa.
- Selected Salsa bug-fix commits demonstrate maintenance surface. They are not a measured defect rate and should not be used to compare Salsa's reliability with other frameworks.
- Salsa's optional LRU bounds memoized values for configured tracked functions, not all graph metadata. This report does not measure the actual memory footprint of keys, edges, interned values, tracked outputs, or persistence for an Anneal-sized workload.
- The Aeneas conclusion relies on the existing pinned reference report and its source inspection. This run did not independently re-execute Aeneas or derive a new minimal invalidation closure.
- A coarse Anneal query graph can still use a query framework as an implementation technique. The judgment is about semantic granularity and ownership, not a rejection of Salsa as a library.
- A persistent upstream server may expose a sound finer-grained contract that is unavailable in the currently pinned Aeneas API. If that contract appears, the recommendation should be re-evaluated.
- Query reuse does not by itself establish Anneal verification success. Source/model correspondence, complete proof obligations, TCB accounting, and current-generation publication remain separate requirements.

## Evidence

### Salsa current mechanism

Observed 2026-09-30 at `salsa-rs/salsa@a7f8c558555f179ca02f6bdf7397d1317f91aa43`:

- `README.md`, blob `1e4afef11f4e66f16573457b220ec19d495fa742`: Salsa as on-demand incremental computation; inputs versus pure query functions; memoized reuse.
- `book/src/reference/algorithm.md`, blob `2b6d9e5357388e85302e81fa23ff281d62ae62de`: revisions, dependency recording, re-execution, backdating, and durability.
- `book/src/tuning.md`, blob `0353e2c3324806b346cd6b2d6db465b063c598c0`: unbounded default memo values, optional LRU, retained keys/dependency metadata, stale-output reclamation, and cancellation behavior.
- `book/src/cycles.md`, blob `436a716a074dac430ab979991c65cff5060c9f3f`: default cycle panic, fixed-point/fallback recovery, monotonicity/convergence conditions, and iteration cap.
- `book/src/plumbing/database_and_runtime.md`, blob `eb70cab9b21f436133c72134901024c3dc040fb0`: shared storage, per-handle query stacks, cancellation before revision mutation, runtime revision/durability state, and tracked reads.
- `src/function/fetch.rs`: current implementation contains `detailed-trace` debug spans and reports tracked reads; used only as implementation corroboration for the existence of tracing/dependency hooks.

Selected repository-history evidence:

- `38a44eef879be5eca1ce94c09637b23b3a97a529` (2024-06-19), “Remove the old Salsa, rename `salsa-2022` crate to `salsa`.”
- `095d8b2b8115c3cf8bf31914dd9ea74648bb7cf9` (2025-03-10), rewrite cycle handling to support fixed-point iteration.
- `201704c5d185187905d0d8c0a963acd5593b19fe` (2025-02-11), move LRU eviction to revision boundaries; commit message identifies prior immediate eviction as unsound with outstanding references.
- `0946cbd6478cf2bddfc9ac65b3c254c1f1b1bf95` (2026-01-22), fix out-of-order verification of cycle-head dependencies.
- `c3d88eb8671d09e1a175aa4d4b391a6242d2d123` (2026-06-02), preserve accumulated values when a reused tracked function skips execution.
- `c10e4ade12f6196bbda2a3bc76191eb4e176f25a` (2026-09-24), guard unvalidated interned data and memo access.
- `ff0a022a6a2e7e7929a6169f3815a1a67433613e` (2026-09-27), reduce redundant query-completion work and clarify dependency ordering; evidence that hot-path dependency bookkeeping remains an active optimization area.

### rustc mechanism and history

Observed 2026-09-30 at `rust-lang/rustc-dev-guide@8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85`:

- `src/query.md`: demand-driven query interface and links to red-green incremental design.
- `src/queries/incremental-compilation.md`: query DAG and try-mark-green overview.
- `src/queries/incremental-compilation-in-detail.md`, blob `9893edd54b950155da586843baa3319da15dcc4e`: purity/input assumptions, dependency recording, false-positive motivation for red-green validation, stable fingerprints across sessions, old/new dependency graphs, cache promotion, query modifiers, projection-query firewalls, and stated shortcomings.
- `src/queries/query-evaluation-model-in-detail.md`: query context, memoization, immutable inputs, cycle detection, removal of cycle recovery, and controlled “steal” query exception.
- `src/variance.md`, blob `de259d38c3ec08e53dbe99127a8ee41cfa0f37c0`: `crate_variances` plus `variances_of` projection pattern and its dependency-graph rationale.
- `src/solve/caching.md`: dependency tracking makes caching cycle participants non-trivial; used as a concrete example of graph/cycle interaction.

First-party historical publications:

- Michael Woerister, “Incremental Compilation,” Rust Blog, 2016-09-08, `https://blog.rust-lang.org/2016/09/08/incremental/`. The post says implementation began toward the end of 2015, motivates the work with edit-compile latency, describes decomposition into cacheable intermediate computations and dependency graphs, and warns that correctness regression testing was still required.
- Felix Klock and Mark Rousskov on behalf of the compiler team, “Announcing Rust 1.52.1,” Rust Blog, 2021-05-10, `https://blog.rust-lang.org/2021/05/10/Rust-1.52.1/`. The team temporarily disabled incremental compilation by default after fingerprint verification exposed cache inconsistencies that could lead to miscompilation.

### Anneal authority and current upstream-boundary evidence

At `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`:

- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`: Anneal must not fail open and prioritizes promises that remain meaningful as the system evolves.
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: verification success requires precise identity/scope; semantics relevant to a promise cannot be hidden by an abstraction; use the simplest mechanism that faithfully supports the promise; detailed ownership boundaries remain deliberate non-decisions.

Current reference evidence observed from `refs/heads/reference` on 2026-09-30:

- `reports/aeneas-incremental-translation-feasibility-nightly-2026-06-03/REPORT.md`, blob `966b5953644d8c9a766ae900e8b137616c501be8`: Aeneas has declaration-local structure but no supported incremental translation protocol; whole-crate context construction and global extraction dependencies prevent assuming function-local invalidation.
- Adjacent #3732 candidate/reference work on build-system orchestration, Adapton naming, negative dependencies, and dataflow was consulted only to avoid semantic duplication. This report intentionally answers J037's narrower question about when Salsa/rustc-style query granularity earns its complexity.

## Revalidation

For a newer Salsa revision, first re-read `book/src/reference/algorithm.md`, `book/src/tuning.md`, `book/src/cycles.md`, and `book/src/plumbing/database_and_runtime.md`. Check whether the default retention policy, LRU scope, cancellation protocol, or cycle semantics changed. Then inspect recent commits touching memo validation, tracked/interned identity, persistence, eviction, cancellation, and cycles; those areas can change the cost and correctness judgment without changing the high-level API.

For rustc, compare the current developer-guide query and incremental-compilation chapters with `8ae6c255...`. In particular, re-check red-green validation, projection queries, stable-key/fingerprint handling, persistence, and any query modifiers that bypass normal tracking. If the conclusion depends on exact compiler behavior rather than the documented architecture, inspect the corresponding `rust-lang/rust` source revision directly.

For Anneal, revalidate the current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`, then inspect the current Charon/Aeneas integration. If Aeneas or another upstream now exposes a supported incremental API with explicit changed/deleted subjects and dependency closure, repeat the granularity judgment at that new interface boundary.

Before adopting item-level reuse, run a representative edit matrix against a clean-recompute oracle. Include body-only edits, signature/type/trait/global changes, declaration insertion/deletion, naming/SCC changes, configuration changes, cancellation races, and repeated edits that return to an earlier value. Measure wall time, recomputed nodes, dependency-edge count, retained memory after many revisions, cache hit rate, and invalidation-debugging effort. The design earns fine granularity only if those measurements show material latency savings while clean recomputation remains observationally equivalent for every supported case.