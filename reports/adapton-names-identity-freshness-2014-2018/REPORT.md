# Adapton names: stable identity is not unchanged meaning

## Summary

Adapton and its nominal successors separate two questions that cache designs often conflate: **which old computation corresponds to this new one?** and **is the old answer still valid?** A name answers the first question. Dependency repair answers the second.

The original 2014 Adapton system records a demanded computation graph (DCG), dirties nodes when tracked mutable inputs change, and repairs only the portion later demanded. Its default matching is structural. The 2015 Nominal Adapton work adds first-class names because structural identity can destroy reuse after edits that preserve a logical correspondence. A programmer can deliberately give an old allocation or thunk and its new incarnation the same name. That permits reuse across structural change, but it does not declare the cached value fresh: the reused node is still subject to dirtying, dependency checking, and recomputation. The paper's from-scratch-consistency result is precisely about this distinction.

Names also create a new correctness obligation. Reusing one name ambiguously for different live objects can make the nominal correspondence incoherent. Nominal Adapton detects such mistakes dynamically. Follow-up work reframed this as the **precise-name problem** and then used refinement/type-and-effect systems to verify global uniqueness statically. The historical progression is therefore not “find a better cache key.” It is: expose correspondence as a controllable concept, retain a separate change-propagation semantics, then make the correspondence discipline itself checkable.

For Anneal, the direct lesson is to keep at least four concepts distinct:

1. a **subject identity** says which logical thing a request is about;
2. a **generation or snapshot identity** says which observed world produced a value;
3. an **equality/fingerprint** says what selected inputs or outputs compare equal;
4. a **dependency argument** says why reuse remains valid for the requested claim.

A stable subject ID, source position, item name, or worker handle can improve matching without being freshness evidence. A content hash is stronger equality evidence for the bytes it covers, but it says nothing about omitted inputs. A worker epoch is useful as a conservative fence when session state is opaque, but it is deliberately too coarse to be a durable subject identity.

Anneal should therefore use stable names freely for navigation, correspondence, and cache lookup, while making freshness a separate checked property. Fine-grained dependency traces are worth retaining only where Anneal can actually observe the relevant dependencies and the workload benefits from repair. At the current Aeneas boundary, the published source analysis finds whole-crate contexts, global extraction/naming state, and no edit/invalidation protocol. That favors coarse snapshot identities and recomputation there until a stronger dependency contract exists. The same rule applies to other opaque Charon/Aeneas/Lean/native stages: names can nominate a candidate old result; they cannot prove it current.

## Applicability

This report addresses issue #3732 J036: Adapton and names, especially the difference between stable identity and unchanged meaning. It asks what first-class naming actually guarantees, how nominal reuse evolved from the original Adapton design, and how those ideas should influence Anneal's artifact subjects, source positions, content hashes, worker epochs, dependency traces, and recomputation boundaries.

The primary literature is:

- Hammer, Khoo, Hicks, and Foster, *Adapton: Composable, Demand-Driven Incremental Computation*, PLDI 2014, DOI `10.1145/2594291.2594324`;
- Hammer et al., *Incremental Computation with Names*, OOPSLA 2015, DOI `10.1145/2814270.2814305`; the inspected extended version is `arXiv:1503.07792v6`;
- Hammer, Dunfield, Economou, and Narasimhamurthy, *Refinement Types for Precisely Named Cache Locations*, `arXiv:1610.00097`; and
- Hammer et al., *Fungi: Typed Incremental Computation with Names*, `arXiv:1808.07826v1`.

The Anneal-side comparison uses `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` at `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, plus the current reference report `aeneas-incremental-translation-feasibility-nightly-2026-06-03` as evidence about the selected Aeneas revision. That report is evidence about Aeneas's current interface, not an architectural decision for Anneal.

This report does **not** claim that Anneal should implement Adapton, a demanded computation graph, or a general self-adjusting-computation runtime. The transfer is conditional: Adapton's correctness results rely on a language/runtime that observes the relevant mutable inputs and dependencies. Existing external compiler and prover processes do not automatically satisfy those assumptions.

## Findings

### Adapton separates invalidation from demanded repair

The original Adapton design addresses two limitations the authors identify in prior incremental-computation systems: eager recomputation of outputs nobody currently demands, and poor reuse when computations are shared, reordered, or switched between contexts.

Its operational device is a demanded computation graph. Incremental computations record reads and forced subcomputations as dependencies. Updating a tracked mutable reference marks dependent computations dirty. Re-evaluation is delayed until a dirty result is demanded; repair then checks dependencies and recomputes only where needed. The authors prove the incremental semantics sound with respect to from-scratch evaluation: repaired evaluation produces the same terminal result as evaluating afresh under the modeled semantics.

This is the first important boundary for Anneal. A retained graph is useful only if changes enter through inputs the graph knows about. If a compiler, build script, environment variable, filesystem lookup, plugin, or long-lived process state can influence a result without appearing as a dependency, the DCG-style theorem shape does not transfer. The graph can be perfectly repaired relative to an incomplete input model and still produce a stale answer for the real system.

The implication is not “avoid dependency graphs.” It is to treat the **input-closure contract** as part of the incremental architecture. Fine-grained repair becomes trustworthy only after Anneal can say what events or state transitions are guaranteed to dirty the affected nodes.

Basis: **primary literature** for Adapton's mechanism and formal result; **derived** applicability judgment for Anneal.

### Structural matching confuses shape with correspondence

The 2015 names paper starts from a practical weakness in structural matching. Suppose an incremental map over a mutable list inserts a new element in the middle. Structural matching can still recognize the unchanged suffix, but newly allocated tail pointers can make the unchanged prefix fail to match its prior counterpart. Work that is logically “the same mapping of the same old element” is lost because the surrounding representation changed.

Nominal Adapton lets the program assign a first-class name to an allocation or computation and derive related names deterministically. The new run can then say explicitly that a new-looking structural position corresponds to a node from the old run. In the paper's list example, that correspondence prevents an insertion from cascading into needless reallocation and recomputation of the whole prefix.

The key point is what the name means: **reuse this prior identity as the candidate corresponding object**. It does not mean **the old contents are valid without checking**. The paper's example explicitly reuses a named reference whose contents change, dirties it, and relies on change propagation to determine which dependents require repair. Stable identity and changed value coexist by design.

For Anneal, this argues against making any one identifier carry both semantic roles. A durable Rust-item identity may survive an edit. If so, that is useful precisely because the item can be *the same subject while having changed meaning*. Treating the stable identity itself as a cache-validity bit would invert the purpose of nominal matching.

Basis: **primary literature** for the structural-versus-nominal example; **derived** Anneal mapping.

### Names improve reuse by weakening matching, so they need a separate safety discipline

Nominal matching is intentionally less conservative than structural matching. The programmer chooses which allocations correspond, including correspondences that cannot be inferred from current structure. This creates more reuse opportunities and also creates a new class of mistakes.

The OOPSLA paper calls out ambiguous name reuse: associating the same name with distinct objects in a way that makes the nominal heap inconsistent with from-scratch semantics. Nominal Adapton detects an ambiguous match dynamically. The implementation tracks the currently forced nodes; when a nominal match overwrites old graph information and dirties a node on that force stack, it raises an exception rather than silently accepting an inconsistent reuse.

This history matters because it shows the correct architecture for stable IDs is not “trust the ID.” The more aggressively an identifier survives structural change, the more the system needs an independent rule for when two uses are legal and when the old value must be repaired or rejected.

A close Anneal analogue is a stable proof-subject ID. Reusing the ID across edits may make UI state, proof attempts, diagnostics, and caches easier to correlate. But if two simultaneously meaningful subjects can accidentally acquire the same ID, or if a subject's dependency environment changes without invalidating a result, the stable ID becomes a source of aliasing rather than correctness. The identity space needs uniqueness/scoping rules; the cached result needs freshness rules.

Basis: **primary literature** for dynamic ambiguity checks; **derived** Anneal analogy.

### Follow-up work moved name correctness from dynamic checks toward static evidence

The 2016/2017 refinement-type work names the relevant property directly: a cache-location name is **precise** when it identifies at most one value or subcomputation; ambiguous names are imprecise. The paper develops a type-and-effect system for verifying precision.

Fungi generalizes that line. Its type-and-effect system lets programs express local invariants about names and composes them to establish global uniqueness. The historical move is important: once programmers control correspondence, the correctness of naming becomes sufficiently central to deserve machine-checked evidence rather than convention alone.

Anneal does not need Fungi's type system to use this lesson. It can make identity construction boring and mechanically scoped. Examples include namespaced IDs such as `(workspace generation, crate subject, declaration subject)`, explicit parent-child derivation, and collision checks at ingestion boundaries. If a stable cross-generation identity is needed, that should be a distinct field from the per-generation key, not a convention that silently drops the generation component.

The conditional recommendation is to prefer an identity scheme whose uniqueness and scoping can be locally checked. Avoid allowing arbitrary human-readable strings to become global cache authority merely because they are convenient for logs or RPCs.

Basis: **primary literature** for precise names and Fungi; **derived** design guidance.

### Source positions are correspondence evidence, not durable cache authority

A source span is useful for navigation and diagnostics, but ordinary edits can move a declaration without changing its semantics, while edits inside the same span can change semantics without changing its rough location. This makes position a poor sole identity for reuse.

Adapton's nominal lesson suggests a better role: position may help *match* a newly observed declaration to a prior logical subject, alongside stronger evidence such as compiler item identity, declaration path, syntax/semantic fingerprints, or explicit persisted subject IDs. After matching, freshness still has to be checked against the relevant snapshot and dependencies.

This also avoids the reverse problem: a source position can be stable while imported definitions, cfg state, tool versions, or generated inputs change. Position has no vocabulary for those changes.

Basis: **derived** application of the correspondence/freshness split; no claim that Adapton itself studies source spans.

### Content hashes prove equality only over the bytes they cover

Content-addressing is a useful alternative to nominal matching when exact input equality is what matters. If two immutable byte strings have the same collision-resistant digest under the system's trust assumptions, a cache can cheaply recognize the same content without a persistent logical name.

But a hash is not automatically a semantic freshness certificate. A hash of a Rust file does not include transitive dependencies, cfg values, proc-macro behavior, compiler/tool versions, environment variables, or mutable external state unless the cache key explicitly incorporates them. Likewise, a hash of generated Lean bytes proves those bytes match; it does not prove they were generated from the currently intended Rust subject under the currently intended translation environment.

Nominal matching and content addressing therefore solve different parts of the problem. Names are good at correspondence through structural change. Content hashes are good at equality of captured values. Neither establishes the completeness of the captured dependency set.

For Anneal, a strong cache key can combine both: a stable subject name for lookup and a generation/dependency fingerprint for validity. This lets UI and durable records retain identity while execution caches remain conservative.

Basis: **derived** comparison; ordinary cryptographic-hash collision assumptions are outside this report's scope.

### Worker epochs are intentionally conservative freshness fences

A worker or process epoch solves a different problem again. If a long-lived Charon, Aeneas, Lean, or helper process contains state that the host cannot fully enumerate, changing the epoch on restart or reset prevents values created under one hidden state from masquerading as values of another.

An epoch is therefore useful precisely because it is coarse. It says “do not assume cross-epoch reuse” rather than “this logical subject changed.” Making an epoch part of every execution-cache key can be a sensible containment rule for opaque session state. Making it part of the human-facing subject identity would be counterproductive because the same Rust function or proof obligation would appear to become a new logical object on every worker restart.

The nominal lesson is again separation of roles: logical names survive where correspondence is useful; execution-generation identities change where freshness needs a fence.

Basis: **derived** Anneal architecture guidance.

### Dependency traces earn their retention cost only when they can avoid enough recomputation

Adapton retains dependency structure so that it can dirty affected nodes and later repair only demanded paths. This is not free. The system pays to construct and retain graph nodes and edges, perform dirtying/cleaning, match prior computations, and garbage-collect unreachable cached structure. Its own evaluation is workload-dependent: demand-driven repair wins strongly on reuse-heavy patterns, while additional incremental machinery is less compelling when nearly everything is demanded again.

That tradeoff gives Anneal a concrete decision rule. Retain a fine-grained dependency trace when all of the following are reasonably true:

- the stage is expensive enough that avoided recomputation matters;
- edits usually affect a small fraction of the trace;
- later queries demand only a subset of affected outputs, or early cutoff is common;
- the host can observe a dependency set that is conservative for correctness; and
- the retained graph's memory, invalidation, debugging, and versioning costs are lower than the work it saves.

Recompute a coarse stage when one or more of those conditions fail. A stage that takes little time, is usually fully demanded, has hidden dependencies, or changes wholesale under ordinary edits is a poor target for an elaborate retained graph.

This is a conditional cost model, not an empirical conclusion about Anneal latency. No benchmark was run here.

Basis: **primary literature** for demand-driven dependency retention and workload-sensitive benefits; **derived** decision rule.

### Current Aeneas evidence favors coarse generation keys before fine-grained nominal reuse

The current reference report for Aeneas `nightly-2026.06.03` finds declaration-local structure but no public incremental-translation protocol. Every `translate_crate_to_pure` call constructs a fresh whole-crate context. Shared analyses include a crate use graph, declaration groups, type and function analysis, and maps of selected declarations. Pre-passes include crate-wide transformations. Extraction registers globally unique target names and computes dependency/SCC structure.

The same report concludes that a persistent host can reuse the process and in-memory values for lifecycle performance, but a correctness-preserving cache needs stable snapshot identity, dependency tracking, invalidation, deletion/replacement handling, and configuration identity that the current API does not itself provide. Its conservative near-term recommendation is whole-crate semantic recomputation from a normalized LLBC snapshot.

J036 sharpens why. Even if Charon or Aeneas IDs make two declarations look like the “same” declaration across snapshots, that correspondence alone does not establish that an old translation remains valid. It nominates the old result for possible reuse. The missing piece is the dependency/freshness argument over the whole-crate contexts that can affect translation and extraction.

Anneal can still keep a stable subject ID for that declaration in its UI or durable model. It should simply key execution reuse by a stronger generation or validated dependency fingerprint until the upstream boundary exposes enough change information to justify finer repair.

Basis: **current reference source analysis** plus **derived** nominal interpretation.

### The useful Anneal abstraction is a named subject plus a validated observation

A practical data model can make the distinctions explicit. Conceptually, a reusable result should carry fields resembling:

```text
subject        = stable logical identity for correspondence
snapshot       = identity of the observed source/build/tool world
producer       = tool/configuration/version identity
value          = artifact/result identity
inputs         = conservative dependency fingerprint or declared closure
status         = fresh | stale | unknown | failed | partial
```

The exact schema is deliberately not prescribed here. The point is that `subject` should not stand in for `snapshot` or `inputs`.

A lookup by `subject` may return an old candidate. Reuse becomes valid only after Anneal can establish that the candidate's modeled dependencies still agree with the current request. If dependency completeness is unknown, `unknown` should conservatively mean recompute, not “stable name, therefore reuse.” This matches Anneal's current design contract: verification success needs enough identity and scope to make its promise meaningful, and missing evidence cannot silently acquire the meaning of success.

Basis: **derived** synthesis from Adapton's nominal/change-propagation split and Anneal's current design contract.

## Boundaries

- No Adapton, Nominal Adapton, Fungi, Charon, Aeneas, Lean, or Anneal benchmark was executed.
- The report does not reproduce the Adapton or Nominal Adapton metatheory. It relies on the authors' published proof statements and uses them only within their modeled language/runtime assumptions.
- The large speedups reported by the Nominal Adapton paper are workload-specific evaluations, not predictions for Anneal.
- The report does not establish a quantitative memory-versus-recompute threshold for retaining dependency traces. That requires Anneal workload measurements.
- Adapton's demanded computation graph observes dependencies created through its own computation model. The report does not claim arbitrary external processes are automatically capturable by that model.
- Content hashes are discussed as equality/fingerprinting mechanisms, not as a cryptographic-security analysis.
- Stable Rust/LLBC/Lean subject identity is not designed here. The report only establishes why correspondence identity and freshness evidence should remain separate.
- The Aeneas conclusions are inherited from the current reference report at the pinned `nightly-2026.06.03` revision. Revalidate them if Anneal changes the selected Aeneas version or Aeneas adds retained incremental state/edit APIs.
- Worker epochs are a derived integration pattern, not an Adapton mechanism.
- Anneal implications are derived conditional analysis. `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` remain authoritative design constraints.

## Evidence

### Primary literature

**Adapton, PLDI 2014**

- DOI: `10.1145/2594291.2594324`
- Project/paper page: `https://www.cs.umd.edu/~mwh/papers/hammer13adapton.html`
- University of Maryland technical-report record: `https://drum.lib.umd.edu/items/b7401a53-964b-4f78-8b2d-a93ab750bb0a`
- Role: authors' motivation for demand-driven incremental computation; demanded computation graph; inner/outer split; from-scratch-equivalence/soundness result; evaluation of reuse patterns and workload-dependent costs.

**Incremental Computation with Names, OOPSLA 2015**

- DOI: `10.1145/2814270.2814305`
- Extended version: `https://arxiv.org/abs/1503.07792`, inspected as arXiv v6 (2021-03-23), whose publication history retains the 2015 versions.
- Role: structural matching failure after edits; explicit names and namespaces; programmer-controlled correspondence; dynamic detection of ambiguous name use; from-scratch consistency; reported performance effects.

The extended paper states that structural matching is deliberately conservative for immutable inputs, while mutable incremental computation can profit from a weaker correspondence relation. It defines names as first-class values used to identify reusable pointers/computations across runs. Its list-insertion example reuses a named reference even though the reference's contents change, then dirties the reference so dependency repair remains responsible for validity. It also states that ambiguous name use is detected dynamically rather than allowed to silently corrupt from-scratch semantics.

**Refinement Types for Precisely Named Cache Locations**

- `https://arxiv.org/abs/1610.00097`
- Role: identifies precision/uniqueness of cache-location names as a correctness condition and presents a sound refinement type-and-effect system for verifying it.

**Fungi: Typed Incremental Computation with Names**

- `https://arxiv.org/abs/1808.07826`, v1 submitted 2018-08-20.
- Role: extends the nominal line with statically verifiable name invariants and a type-and-effect system establishing global uniqueness in well-typed programs.

### Current Anneal authority

```text
google/zerocopy
cc135f46155b72e4b51188525c2974a3b84acf92
```

- `anneal/PRINCIPLES.md`: verification success is a conditional promise over explicit trusted code and assumptions; Anneal must not fail open.
- `anneal/DESIGN.md`: a successful result needs enough identity and scope to make its promise meaningful; missing evidence cannot silently become success; lower-level mechanisms remain deliberate non-decisions.

These files constrain the derived Anneal recommendation. They do not require a particular incremental engine.

### Current reference evidence about Aeneas

- `reports/aeneas-incremental-translation-feasibility-nightly-2026-06-03`
- Primary subject in that report: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`.
- Role: establishes whole-crate context construction, shared maps/analyses, crate-wide pre-passes, global extraction naming/dependency structure, and absence of a public edit/invalidation protocol at the selected revision. It recommends whole-crate semantic recomputation as the conservative baseline while noting process/in-memory reuse opportunities.

### Derived reasoning chain

1. Nominal Adapton makes identity deliberately stable across some structural changes so that old work can be found.
2. The reused node may still have changed contents; tracked dependency repair, not the name, re-establishes current validity.
3. Therefore a stable name is correspondence evidence, not freshness evidence.
4. Anneal has several candidate identity forms—logical subjects, source positions, hashes, worker epochs—that have different stability/equality properties.
5. None of those forms alone proves that all semantic dependencies of an external stage are unchanged.
6. Anneal should therefore separate logical subject identity from snapshot/generation and from dependency/freshness evidence.
7. Fine-grained retained traces are justified only where the dependency boundary is conservative and the saved work exceeds graph-retention complexity; opaque whole-crate stages should remain coarse until that condition changes.

## Revalidation

Revalidate this report when any of the following changes:

1. Anneal adopts a concrete persistent identity, generation, dependency-fingerprint, or cache-validity schema.
2. Anneal introduces a long-lived orchestration engine whose correctness relies on retained fine-grained dependency traces.
3. Charon, Aeneas, or Lean expose a supported edit/invalidation protocol or stable cross-snapshot dependency identities that Anneal intends to trust.
4. The selected Aeneas revision changes materially from `ac9f1bc5262a5e4ff1e24ca78617121382202727`, especially around `compute_contexts`, pre-passes, extraction naming, or retained state.
5. Empirical Anneal workloads show that a coarse stage dominates latency and usually changes only locally; that is the point to measure whether a retained graph pays for itself.
6. Anneal begins treating source positions, declaration IDs, content hashes, RPC object IDs, or worker/session handles as durable reuse authority rather than merely correspondence or equality evidence.
7. A stronger primary result supersedes the Adapton/Nominal Adapton/Fungi literature on nominal incremental correspondence or substantially changes the known assumptions behind from-scratch consistency.

A useful implementation probe is to pick one candidate stage and record, for a sequence of realistic edits, both a clean recomputation and a proposed incremental result. Persist the exact dependency closure and cache key used for each reuse decision. Include body edits, declaration insert/delete/rename, dependency version changes, cfg/environment changes, tool-version changes, and worker restart. The key failure mode is not merely a value mismatch; it is any reuse decision whose claimed freshness cannot be explained from a conservative dependency argument.