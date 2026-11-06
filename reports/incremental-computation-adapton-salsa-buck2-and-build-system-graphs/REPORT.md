# Incremental Computation, Query Engines, and Build-System Graphs: Adapton, Self-Adjusting Computation, Early Cutoff, Salsa/rustc, Buck2, Build Systems à la Carte, and Make/Ninja

## Summary

Incremental computation and build-system design separate several architectural questions that cache and orchestration designs often conflate: **which prior computation corresponds to a new request**, **what makes a reused result semantically equivalent to a fresh run**, **which downstream consumer observations allow early cutoff**, **when fine-grained query tracking earns its retained-state cost**, and **where project policy should sit relative to a narrow execution or verification core**. Across ten synthesized investigations covering Adapton and nominal incremental computation (2014–2018), self-adjusting computation and from-scratch consistency (2005–2013), early-cutoff equality relations in Jane Street Incremental, `rustc`, and GHC (2010–2026), Salsa and `rustc` query granularity plus current-source verification (2016–2026), the Buck1-to-Buck2 and DICE single-graph rewrite plus current-source verification (2013–2026), *Build Systems à la Carte* orchestration taxonomy (2018–2026), and Make/Ninja narrow build-tool boundaries plus current-source verification (1979–2026), a unified set of engineering invariants emerges for Anneal.

### 1. Adapton, Names, Identity, and Freshness

Adapton and its nominal successors separate two questions that cache designs often conflate: **which old computation corresponds to this new one?** and **is the old answer still valid?** A name answers the first question. Dependency repair answers the second.

The original 2014 Adapton system records a demanded computation graph (DCG), dirties nodes when tracked mutable inputs change, and repairs only the portion later demanded. Its default matching is structural. The 2015 Nominal Adapton work adds first-class names because structural identity can destroy reuse after edits that preserve a logical correspondence. A programmer can deliberately give an old allocation or thunk and its new incarnation the same name. That permits reuse across structural change, but it does not declare the cached value fresh: the reused node is still subject to dirtying, dependency checking, and recomputation. The paper's from-scratch-consistency result is precisely about this distinction.

Names also create a new correctness obligation. Reusing one name ambiguously for different live objects can make the nominal correspondence incoherent. Nominal Adapton detects such mistakes dynamically. Follow-up work reframed this as the **precise-name problem** and then used refinement/type-and-effect systems to verify global uniqueness statically. The historical progression is therefore not "find a better cache key." It is: expose correspondence as a controllable concept, retain a separate change-propagation semantics, then make the correspondence discipline itself checkable.

For Anneal, the direct lesson is to keep at least four concepts distinct:

1. a **subject identity** says which logical thing a request is about;
2. a **generation or snapshot identity** says which observed world produced a value;
3. an **equality/fingerprint** says what selected inputs or outputs compare equal;
4. a **dependency argument** says why reuse remains valid for the requested claim.

A stable subject ID, source position, item name, or worker handle can improve matching without being freshness evidence. A content hash is stronger equality evidence for the bytes it covers, but it says nothing about omitted inputs. A worker epoch is useful as a conservative fence when session state is opaque, but it is deliberately too coarse to be a durable subject identity. Anneal should use stable names freely for navigation, correspondence, and cache lookup, while making freshness a separate checked property. At the current Aeneas boundary, the published source analysis finds whole-crate contexts, global extraction/naming state, and no edit/invalidation protocol, favoring coarse snapshot identities and recomputation there until a stronger dependency contract exists.

### 2. Self-Adjusting Computation and From-Scratch Consistency

Self-adjusting computation gives a precise answer to the central correctness question behind incremental reuse: after the input changes, the adjusted computation should have the same observable meaning as evaluating the program afresh on the changed input. The result is stronger than "we invalidated the nodes we knew about" and weaker than "incrementality is always fast." In the Acar line of work, the equivalence is proved because the language and runtime control the relevant mutable state, record the dependencies created by reads and writes, and constrain how old traces may be reused. Later work extends the model from write-once functional-style modifiables to multiple writes and cyclic stores; it does not turn arbitrary ambient effects into tracked dependencies.

For Anneal, this is most useful as an **acceptance specification for reuse**. A reused or incrementally updated stage may be treated as current only if its observable result is equivalent to a fresh execution for the same source/model/tool environment. Rust source bytes, generated inputs, tool and plugin identities, configuration, relevant environment variables, dependency files, and other ambient reads cannot disappear from that accounting merely because a cache key or worker handle stayed the same. A coarse design can satisfy the same correctness relation by re-running an opaque stage whenever it cannot establish that all semantically relevant inputs are unchanged.

### 3. Early Cutoff and Consumer-Relative Equality

Early cutoff is sound only when "unchanged" means unchanged for the downstream observation that is being skipped. There is no useful global equality relation that simultaneously captures source identity, compiler semantics, generated model semantics, diagnostics, provenance, object code, and verification authority.

Three mature incremental mechanisms make the same architectural point at different scales. Jane Street Incremental lets each node choose the predicate that decides whether a recomputed value should propagate. `rustc`'s red-green query engine reruns a dirty query and can stop invalidation when the query's stable result fingerprint is unchanged; projection queries deliberately create change-propagation firewalls around large changing values. GHC recompiles a module when its own source changes, but can stop *downstream* recompilation when the ABI or the particular imported declarations a client used are unchanged. The cutoff boundary and the equality relation are paired.

For Anneal, this argues against one "workspace hash" or one normalized-source identity governing every kind of reuse. The practical rule is **recompute until reaching a boundary with a checkable equality that is a congruence for the downstream use; then cut off only that downstream path**.

### 4. Salsa and `rustc` Query Granularity and Current-Source Recheck

Salsa and `rustc` show why a fine-grained query graph can make repeated compiler work fast, but they also show the price of making that graph trustworthy. The useful unit is not "an item" by default. It is the smallest computation for which the host can give a stable key, expose every semantically relevant input through the query boundary, define result equality, and afford the retained dependency state. Red-green validation and projection queries then let unchanged results stop invalidation from spreading.

Wrapping opaque Aeneas calls in item-sized Salsa keys would create a finer cache without creating the missing dependency contract. The conservative Anneal baseline is a coarse query/DAG boundary around whole normalized stage inputs, with finer queries only inside subsystems whose semantic dependencies Anneal or an upstream service actually owns.

In the current-source review of Salsa and the `rustc` developer guide (recorded in [`support/salsa-rustc-current-source-review/matrix.json`](support/salsa-rustc-current-source-review/matrix.json)), [`salsa-rs/salsa` `master`](https://github.com/salsa-rs/salsa/commit/30b614d826d697c47bc0f21591fab218f2004032) is three commits ahead and zero behind the baseline pin `a7f8c558555f179ca02f6bdf7397d1317f91aa43`, and [`rust-lang/rustc-dev-guide` `main`](https://github.com/rust-lang/rustc-dev-guide/commit/be8854f66df1b5450349061e45374ac072abd109) is 27 commits ahead and zero behind its pin `8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85`. Four of the five pinned Salsa files and both pinned `rustc` guide blobs remain byte-identical, while `book/src/cycles.md` and adjacent Salsa cycle-execution files updated to document and enforce that `cycle_initial` and an initial `cycle_result` fallback must not directly create tracked structs (though they can return a tracked struct created by another tracked query).

### 5. Buck to Buck2, DICE Single-Graph Rewrite, and Current-Source Recheck

Buck2 is strong evidence for replacing a build system's architectural core when the old core makes important invariants and performance properties difficult to express locally, and weaker evidence for adopting a general incremental-computation engine whenever a workflow has dependencies. Meta's from-scratch rewrite retained Buck1 target compatibility while moving language rules out of the core into Starlark behind a smaller rule API, replacing Buck1's separate target-graph, action-graph, and execution phases with one dynamic incremental dependency graph (DICE), and designing around remote execution from the start. Buck2 simplified the external architectural contract seen by rule authors while concentrating substantial complexity in DICE (which later redesigned its core state from fine-grained shared locking to a single-threaded actor/core-state model and highlighted hazards around cross-transaction equality and untracked data flow).

In the current-source review of Buck2 (recorded in [`support/buck2-current-source-review/matrix.json`](support/buck2-current-source-review/matrix.json)), official `facebook/buck2` `main` at [`b2b7ba58b5188aa35adc784d8ec6425dd93b98df`](https://github.com/facebook/buck2/commit/b2b7ba58b5188aa35adc784d8ec6425dd93b98df) is 29 commits forward of the baseline pin `738e69a6c5f1efb6a015645228e7a19ee9b1d9c0`. All four cited Buck2/DICE documentation blobs are unchanged, while three adjacent DICE source files added a `compute_with_key` API returning the canonical key allocation retained alongside the computed value.

### 6. *Build Systems à la Carte* and Make/Ninja Narrow Executor Boundaries

*Build Systems à la Carte* (2018, 2020) separates what a task may depend on (applicative vs. monadic), how tasks are scheduled (topological, restarting, suspending), how the system decides whether a value must be rebuilt (dirty bits, verifying traces, constructive traces, deep constructive traces), and what persistent information it retains. For Anneal, that decomposition points to starting with coarse explicit DAG orchestration and strong result identity while letting Cargo, Lake, and Lean own their internal dependency graphs and keeping verification acceptance and publication fences distinct from build freshness.

Make (1979; GNU Make 4.4.1) and Ninja (`4e4df1e567eb3c1475a51af261cba2bfff60b4be`; release `v1.13.2` at `3441b633c2fe2c494e958780ba0f4227b1327634`) further clarify the boundary between orchestration policy and a narrow execution engine. While GNU Make interleaved a rich meta-build/configuration language with recipe execution, Ninja displaced project policy into generators (GN, CMake) to achieve sub-second edit-build startup on Chromium, yet retained executor-level mechanisms required for freshness and resource safety: command-line tracking, `depfile`/`deps` logs, `restat`, `dyndep`, `validations`, pools, and GNU jobserver participation. On recheck ([`support/ninja-current-source-review/matrix.json`](support/ninja-current-source-review/matrix.json)), official Ninja `master` remained at `4e4df1e567eb3c1475a51af261cba2bfff60b4be` with an unchanged manual blob `81ecf7d388f899a1481df9f25ec1065710de679d`, while release `v1.13.2` (`3441b633c2fe2c494e958780ba0f4227b1327634`) represents a diverged release history (196 commits behind and 60 ahead from release tag to `master` pin). For Anneal, a narrow batch verification boundary can delegate project discovery and interactive caching to a richer host or daemon, provided exact source/model/environment/tool identity, obligation completeness, trust accounting, and publication fencing remain checked at the authoritative boundary.

## Applicability

This coalesced report synthesizes ten complementary investigations into incremental computation and build-system boundaries and maps their architectural implications to Anneal (`anneal/PRINCIPLES.md` and `anneal/DESIGN.md` at `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`):

1. **Adapton and nominal incremental computation (`adapton-names-identity-freshness-2014-2018`):** Examines what first-class naming guarantees, how nominal reuse evolved from structural Adapton (Hammer et al., PLDI 2014, DOI `10.1145/2594291.2594324`; OOPSLA 2015, DOI `10.1145/2814270.2814305`, `arXiv:1503.07792v6`; refinement types for precise names, `arXiv:1610.00097`; Fungi, `arXiv:1808.07826v1`), and how correspondence versus freshness applies to Anneal subjects, source spans, content hashes, worker epochs, and the Aeneas `nightly-2026.06.03` boundary (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`).
2. **Self-adjusting computation and from-scratch consistency (`self-adjusting-computation-from-scratch-consistency-2005-2013`):** Covers Acar's 2005 thesis (`CMU-CS-05-129`), the 2006 adaptive functional formulation (TOPLAS 28(6), DOI `10.1145/1186632.1186634`), the 2008 imperative extension SAIL (POPL 2008, DOI `10.1145/1328438.1328476`; `TR-2007-18`), and the 2013 consistent memoizing semantics (JFP 23(3), DOI `10.1017/S0956796813000099`). Defines **from-scratch consistency** for a stage `F`, logical input/world `I`, prior state `S`, and observable outcome relation `≈` as `R_inc(S, I) ≈ R_fresh(I)`.
3. **Early-cutoff equality relations (`early-cutoff-equality-relations-2010-2026`):** Compares byte equality, normalized syntax, interface/ABI equality, query/result equality, observational equivalence, and claim-relative equivalence across `rust-lang/rustc-dev-guide@8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85`, `janestreet/incremental@98b5750ec3c006641351bfd858a89136a5dbc52c`, `ghc/ghc@234bab081682018da7d04b22eee4b80f70381d07`, and bounded Charon/Aeneas relocation and comment-provenance execution evidence (`Charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, `Aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `Rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`).
4. **Salsa and `rustc` query granularity and current-source review (`salsa-rustc-query-granularity-2016-2026` and `salsa-rustc-current-source-review`):** Evaluates `salsa-rs/salsa` at `a7f8c558555f179ca02f6bdf7397d1317f91aa43` and selected `master` `30b614d826d697c47bc0f21591fab218f2004032` (plus release `salsa-v0.28.5` at `d434f8805c60ac60dce5f367ca91c5a7cd3e4c86`) alongside `rust-lang/rustc-dev-guide` at `8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85` and selected `main` `be8854f66df1b5450349061e45374ac072abd109`.
5. **Buck to Buck2 one-graph rewrite and current-source review (`buck-to-buck2-one-graph-rewrite-2013-2026` and `buck2-current-source-review`):** Examines archived Buck1 (`facebook/buck@9c7c421e49f4d92d67321f18c6d1cd90974c77c4`), Meta Engineering's 2023-04-06 launch account, and `facebook/buck2` at `738e69a6c5f1efb6a015645228e7a19ee9b1d9c0`, selected `main` `b2b7ba58b5188aa35adc784d8ec6425dd93b98df`, and latest observed date-named tag `2026-09-15` at `6507dd157a6f81a810c48583edf1758dd0c337c5`.
6. **Build Systems à la Carte orchestration (`build-systems-a-la-carte-anneal-orchestration-2018-2026`):** Examines Mokhov, Mitchell, and Peyton Jones's ICFP 2018 (`10.1145/3236774`) and JFP 2020 (`10.1017/S0956796820000088`) papers and executable framework (`snowleopard/build@43b18b9a362d7d27b64679ea4122e4b8c5dfedd9`), alongside bounded Anneal invalidation-graph, Rust-input-snapshot, architecture-contract, and fault-model evidence.
7. **Make and Ninja narrow build-tool boundaries and current-source review (`make-ninja-narrow-build-tool-boundaries-1979-2026` and `ninja-current-source-review`):** Examines Stuart Feldman's 1979 Make paper (`10.1002/spe.4380090402`), GNU Make `4.4.1` (2023-02-26, tarball MD5 `c8469a3713cbbe04d955d4ae4be23eeb`), Evan Martin's 2011 Chromium Ninja origin account, and `ninja-build/ninja` at pinned/observed `master` `4e4df1e567eb3c1475a51af261cba2bfff60b4be` and latest official release `v1.13.2` (`3441b633c2fe2c494e958780ba0f4227b1327634`).

Nothing in this report adopts an execution backend, cache schema, or daemon architecture for Anneal; `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` remain authoritative.

## Findings

### Adapton: Stable Identity versus Unchanged Meaning (`adapton-names-identity-freshness-2014-2018`)

#### Adapton separates invalidation from demanded repair

The original Adapton design addresses two limitations the authors identify in prior incremental-computation systems: eager recomputation of outputs nobody currently demands, and poor reuse when computations are shared, reordered, or switched between contexts.

Its operational device is a demanded computation graph (DCG). Incremental computations record reads and forced subcomputations as dependencies. Updating a tracked mutable reference marks dependent computations dirty. Re-evaluation is delayed until a dirty result is demanded; repair then checks dependencies and recomputes only where needed. The authors prove the incremental semantics sound with respect to from-scratch evaluation: repaired evaluation produces the same terminal result as evaluating afresh under the modeled semantics.

This is the first important boundary for Anneal. A retained graph is useful only if changes enter through inputs the graph knows about. If a compiler, build script, environment variable, filesystem lookup, plugin, or long-lived process state can influence a result without appearing as a dependency, the DCG-style theorem shape does not transfer. The graph can be perfectly repaired relative to an incomplete input model and still produce a stale answer for the real system. The implication is to treat the **input-closure contract** as part of the incremental architecture: fine-grained repair becomes trustworthy only after Anneal can say what events or state transitions are guaranteed to dirty the affected nodes.

Basis: **primary literature** for Adapton's mechanism and formal result; **derived** applicability judgment for Anneal.

#### Structural matching confuses shape with correspondence

The 2015 names paper starts from a practical weakness in structural matching. Suppose an incremental map over a mutable list inserts a new element in the middle. Structural matching can still recognize the unchanged suffix, but newly allocated tail pointers can make the unchanged prefix fail to match its prior counterpart. Work that is logically "the same mapping of the same old element" is lost because the surrounding representation changed.

Nominal Adapton lets the program assign a first-class name to an allocation or computation and derive related names deterministically. The new run can then say explicitly that a new-looking structural position corresponds to a node from the old run. In the paper's list example, that correspondence prevents an insertion from cascading into needless reallocation and recomputation of the whole prefix.

The key point is what the name means: **reuse this prior identity as the candidate corresponding object**. It does not mean **the old contents are valid without checking**. The paper's example explicitly reuses a named reference whose contents change, dirties it, and relies on change propagation to determine which dependents require repair. Stable identity and changed value coexist by design. For Anneal, this argues against making any one identifier carry both semantic roles. A durable Rust-item identity may survive an edit; treating the stable identity itself as a cache-validity bit would invert the purpose of nominal matching.

Basis: **primary literature** for the structural-versus-nominal example; **derived** Anneal mapping.

#### Names improve reuse by weakening matching, so they need a separate safety discipline

Nominal matching is intentionally less conservative than structural matching. The programmer chooses which allocations correspond, including correspondences that cannot be inferred from current structure. The OOPSLA paper calls out ambiguous name reuse: associating the same name with distinct objects in a way that makes the nominal heap inconsistent with from-scratch semantics. Nominal Adapton detects an ambiguous match dynamically: the implementation tracks the currently forced nodes, and when a nominal match overwrites old graph information and dirties a node on that force stack, it raises an exception rather than silently accepting an inconsistent reuse.

A close Anneal analogue is a stable proof-subject ID. Reusing the ID across edits may make UI state, proof attempts, diagnostics, and caches easier to correlate. But if two simultaneously meaningful subjects can accidentally acquire the same ID, or if a subject's dependency environment changes without invalidating a result, the stable ID becomes a source of aliasing rather than correctness. The identity space needs uniqueness/scoping rules; the cached result needs freshness rules.

Basis: **primary literature** for dynamic ambiguity checks; **derived** Anneal analogy.

#### Follow-up work moved name correctness from dynamic checks toward static evidence

The 2016/2017 refinement-type work names the relevant property directly: a cache-location name is **precise** when it identifies at most one value or subcomputation; ambiguous names are imprecise. Fungi generalizes that line with a type-and-effect system that lets programs express local invariants about names and composes them to establish global uniqueness.

Anneal does not need Fungi's type system to use this lesson. It can make identity construction mechanically scoped, using namespaced IDs such as `(workspace generation, crate subject, declaration subject)`, explicit parent-child derivation, and collision checks at ingestion boundaries. If a stable cross-generation identity is needed, that should be a distinct field from the per-generation key, not a convention that silently drops the generation component.

Basis: **primary literature** for precise names and Fungi; **derived** design guidance.

#### Source positions, content hashes, and worker epochs serve distinct roles

- **Source positions are correspondence evidence, not durable cache authority:** Ordinary edits can move a declaration without changing its semantics, while edits inside the same span can change semantics without changing its rough location. Position may help *match* a newly observed declaration to a prior logical subject alongside stronger evidence, after which freshness still has to be checked against the relevant snapshot and dependencies.
- **Content hashes prove equality only over the bytes they cover:** A hash of a Rust file does not include transitive dependencies, `cfg` values, proc-macro behavior, compiler/tool versions, environment variables, or mutable external state unless the cache key explicitly incorporates them. Likewise, a hash of generated Lean bytes proves those bytes match; it does not prove they were generated from the currently intended Rust subject under the currently intended translation environment.
- **Worker epochs are intentionally conservative freshness fences:** If a long-lived Charon, Aeneas, Lean, or helper process contains state that the host cannot fully enumerate, changing the epoch on restart or reset prevents values created under one hidden state from masquerading as values of another. Making an epoch part of every execution-cache key is a sensible containment rule for opaque session state, whereas making it part of the human-facing subject identity would make the same Rust function appear to become a new logical object on every worker restart.

Basis: **derived** application of the correspondence/freshness split.

#### Dependency traces earn their retention cost only when they avoid enough recomputation

Adapton pays to construct and retain graph nodes and edges, perform dirtying/cleaning, match prior computations, and garbage-collect unreachable cached structure. Retain a fine-grained dependency trace when:

- the stage is expensive enough that avoided recomputation matters;
- edits usually affect a small fraction of the trace;
- later queries demand only a subset of affected outputs, or early cutoff is common;
- the host can observe a dependency set that is conservative for correctness; and
- the retained graph's memory, invalidation, debugging, and versioning costs are lower than the work it saves.

At the current Aeneas `nightly-2026.06.03` boundary, every `translate_crate_to_pure` call constructs a fresh whole-crate context, shared analyses include a crate use graph, declaration groups, type and function analysis, crate-wide pre-passes, and global extraction target names and dependency/SCC structure, with no public edit/invalidation protocol. Even if Charon or Aeneas IDs make two declarations look like the "same" declaration across snapshots, that correspondence only nominates the old result for possible reuse. Conceptually, a reusable Anneal result should separate:

```text
subject        = stable logical identity for correspondence
snapshot       = identity of the observed source/build/tool world
producer       = tool/configuration/version identity
value          = artifact/result identity
inputs         = conservative dependency fingerprint or declared closure
status         = fresh | stale | unknown | failed | partial
```

Basis: **primary literature** and **current reference source analysis** plus **derived** synthesis.

---

### Self-Adjusting Computation: From-Scratch Consistency (`self-adjusting-computation-from-scratch-consistency-2005-2013`)

#### 1. The original correctness target is equivalence with a fresh run, not preservation of a cache data structure

Acar's 2005 thesis states the core correctness criterion directly: change propagation is correct when it is semantically equivalent to executing the program from scratch on the changed input. An initial execution records control and data dependencies in a dynamic dependence graph (DDG); memoized DDGs reuse a previously computed call together with its dependency subgraph and adjust it via change propagation. Checking every memory location a function might read would defeat efficient reuse, so self-adjusting computation records and propagates the relevant dependencies. For Anneal, a persistent worker, prepared proof environment, source handle, content hash, or cache key identifies *which saved state is being discussed*; currentness is a separate proposition.

#### 2. Correctness depends on controlling the dependency boundary

In the factorial example discussed in Acar's thesis and the 2006 TOPLAS paper, when an outer read is re-evaluated after an input change, a nested read that is no longer on the fresh control-flow path must be deleted rather than independently re-executed. Re-executing such stale work can produce a different result, raise an exception, or diverge. For Anneal's cancellation and invalidation design, a dependency graph built for one source/model snapshot is not a bag of jobs that can all safely finish and publish after the snapshot changes: stale results must be prevented from crossing the current acceptance boundary unless their correspondence to the new computation is re-established.

#### 3. Supporting mutation required a stronger theorem, not an assertion that effects are harmless

`Imperative Self-Adjusting Computation` (POPL 2008 / `TR-2007-18`) extended the system to modifiables that can be written multiple times and to cyclic stores in SAIL, using a step-indexed logical relation to handle cycles. The 2013 JFP semantics (`A Consistent Semantics of Self-Adjusting Computation`, accompanied by a public Twelf development) tackled nondeterministic memoization choices combined with mutation during change propagation, proving both a consistency theorem (nondeterministic reuse choices do not change the result from the same starting state) and a correctness theorem relating self-adjusting behavior to ordinary functional meaning. For Anneal, an effect can participate in a fresh-equivalence claim only if it is (a) included in the logical input/outcome relation, (b) controlled so that it cannot affect semantic results, or (c) covered by a stronger upstream contract that Anneal can rely on.

#### 4. "Same starting state" is doing real work

For a coarse Anneal stage, a useful logical input may need to include at least:

- exact Rust/source snapshot and the chosen verification subject;
- generated source or model bytes that are inputs rather than mere outputs;
- exact Charon, Aeneas, Lean/Lake, native plugin, and relevant proof-library identities;
- arguments and configuration that affect translation or checking;
- target/toolchain/build configuration that changes semantics;
- the contents or identities of files actually read outside the primary source set;
- environment variables or working-directory facts that upstream tools consult;
- selected imported/prepared artifacts together with the provenance needed to interpret them;
- any persistent worker state that upstream semantics allow to influence the result.

#### 5. From-scratch consistency is orthogonal to update cost

Acar's 2005 thesis and the SPAA 2021 parallel self-adjusting work (`10.1145/3409964.3461799`) separate three claims:

1. **Correctness:** the reused result means what a fresh result would mean for the current logical input.
2. **Reuse effectiveness:** enough unaffected work survives that the mechanism saves material time or resources.
3. **Reuse overhead:** dependency tracking, retained state, invalidation, and memory do not cost more than the work saved.

#### 6. Differential oracle, opaque-stage integration strategies, cancellation, and competing accounts

- **Differential oracle:** Test suites can compare (1) a warm/reused path after a controlled sequence of edits or environment changes and (2) a clean fresh execution from the final explicit input/world. Disagreement falsifies the reuse contract; agreement increases confidence without proving complete dependency capture over unperturbed hidden inputs.
- **Three defensible strategies for an opaque external stage:**
  1. *Conservative rerun:* Treat the external stage as one coarse node and rerun whenever any potentially relevant input changes.
  2. *Hermetic/captured execution:* Restrict or record ambient inputs strongly enough to construct a complete stage identity.
  3. *Upstream incremental contract:* Reuse a library/server API that already defines snapshots, dependency invalidation, and reused-state semantics.
  (Retaining opaque state and inferring freshness from a handle, timestamp, or successful RPC is not a fourth correctness strategy; it is an unproven assumption.)
- **Termination, cancellation, and failures:** Cancellation policy is a liveness/resource decision; the acceptance boundary is a correctness decision. Furthermore, "fresh execution failed" is an outcome, not absence of a value that can be replaced by an old success.
- **Competing account:** Favoring less incrementality (a small scheduler with coarse stages, immutable source/model identities, and aggressive restart) avoids duplicating upstream caches while still obeying the fresh-equivalence specification `R_inc(S, I) ≈ R_fresh(I)`.

---

### Early Cutoff: Equality Relative to a Consumer (`early-cutoff-equality-relations-2010-2026`)

#### Early cutoff is a relation between a value and a downstream observation

For a downstream consumer `C` and a recomputed value `x'` replacing `x`, a sufficient cutoff relation `~C` satisfies:

```text
x ~C x'  =>  C cannot distinguish x from x' in any way material to the reused result
```

A user-configured predicate such as "two floats differ by less than ε" may fail transitivity and intentionally change behavior; thus the general mechanism is a *cutoff predicate*, and "equality" applies only when the predicate preserves the reused observation.

#### Jane Street Incremental, `rustc`, and GHC mechanisms

- **Jane Street Incremental (`janestreet/incremental@98b5750ec3c006641351bfd858a89136a5dbc52c`, `src/incremental_intf.ml` blob `eabce575943287f144a8f66cf342fd9db438a33e`):** Stabilization recomputes a changed node and adds its parents to the recompute heap only when the node's value changes. The default cutoff is physical equality, replaceable via `set_cutoff`. Early cutoff belongs to the produced value rather than the original input, and the application owns the semantic justification for custom predicates and projection nodes.
- **`rustc` red-green and projection queries (`rust-lang/rustc-dev-guide@8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85`, `src/queries/incremental-compilation.md` blob `079a2b2e00a7f2dd088fab5a4d74541a53659ea1` and `src/queries/incremental-compilation-in-detail.md` blob `9893edd54b950155da586843baa3319da15dcc4e`):** `rustc` computes a 128-bit `Fingerprint` using stable hashing (mapping session-local IDs like `DefId` to stable counterparts). A `no_hash` query cannot establish result equality and must be treated as changed for downstream invalidation. Projection queries act as change-propagation firewalls around monolithic queries, paying per-node tracking and hashing costs to stop propagation at narrower semantic boundaries.
- **GHC recompilation checker (`ghc/ghc@234bab081682018da7d04b22eee4b80f70381d07`, `compiler/GHC/Iface/Recomp.hs` blob `cbd1d392ccd3cee37a0c4dd7dc75ec6117a88dc8`):** Distinguishes producer recompilation from downstream invalidation. If the current module's source hash changed, that module must compile. For imported modules, `mi_usages` tracks the module ABI hash for package modules and fine-grained export and per-entity declaration fingerprints (`addAbiHashes`) for home-package modules, plus explicit tracking for inlining, plugins, Template Haskell, orphan instances, bytecode, flags, and dependent files.

#### Byte equality, normalized syntax, interface/ABI equality, and claim-relative equality

- **Byte equality:** Conservative for direct artifact reuse (`same captured inputs + same required environment identity + same exact artifact bytes`), but does not capture unmodeled ambient inputs and is often too strong for trivia changes.
- **Normalized syntax:** In the bounded Charon/Aeneas provenance probe (`Charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, `Aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `Rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), appending an inert comment after a one-function fixture changed Charon's serialized full source contents while leaving generated Aeneas Lean byte-identical; relocating the byte-identical Rust source changed the local source-file path in LLBC and changed only a source-path documentation line in generated Lean. Normalization should therefore produce a named semantic projection while keeping the original source snapshot and mapping as a parallel dependency of diagnostics and source-model correspondence.
- **Claim-relative layered reuse for Anneal:**

```text
source snapshot / build context
        |
        | current translation + correspondence evidence
        v
semantic model / obligations  ---- model equality ----> reusable proof work
        |
        | theorem checking in identified logical environment
        v
proof result / trust facts
        |
        | current source + promise + coverage + trust association
        v
verification acceptance
```

Separating semantic and presentation dependency paths earns its complexity only when (1) semantic/proof recomputation is materially more expensive than updating source mappings, (2) edits preserving the semantic projection are common, (3) the semantic projection has a stable testable contract, (4) presentation/provenance state can be refreshed without invalidating the semantic artifact, and (5) acceptance combines current provenance with reused semantic evidence without confusing either identity.

#### Early-Cutoff Decision Matrix

| Relation | What it establishes | Safe cutoff examples | What it does not establish |
| --- | --- | --- | --- |
| Exact byte equality | Same captured representation | Reuse immutable artifact bytes; avoid reparsing exact artifact | Same ambient environment; semantic equivalence after different bytes; current source correspondence |
| Normalized syntax equality | Same chosen syntax projection | Skip consumers proven insensitive to erased trivia/ordering/locations | Current spans/provenance; safety for macros/plugins/build inputs not represented by the normalization |
| Interface/ABI equality | Same contract-visible projection | Avoid recompiling/reproving clients restricted to that interface | Equality of private implementation, diagnostics, producer source, or unrelated consumers |
| Query/result equality | Same stage result under its stable representation | Stop downstream invalidation for dependents of that query/projection | Correctness if the query omitted dependencies or stable hashing omitted observable state |
| Observational equivalence | Same behavior for a specified observer set | In principle, any consumer inside that set | A practical generic decision procedure or equality for observers outside the set |
| Claim-relative equivalence | Same evidence-relevant state for a named claim | Reuse proof/model work for that claim while refreshing unrelated state | Permission to relabel stale source/provenance or broaden the claim |

---

### Salsa and `rustc` Query Systems: Granularity and Current-Source Recheck (`salsa-rustc-query-granularity-2016-2026` and `salsa-rustc-current-source-review`)

#### 1. Input closure, projection firewalls, and per-node retention costs

- **Input closure:** Salsa (`salsa-rs/salsa@a7f8c558555f179ca02f6bdf7397d1317f91aa43`) models inputs as explicit mutable roots and tracked functions as pure queries whose reads are recorded, supporting memoized reuse and backdating when a recomputed value equals the prior value. `rustc` similarly treats query providers as pure functions over tracked dependencies. Wrapping an opaque subprocess in Salsa keys does not make hidden filesystem, environment, or process-global dependencies visible.
- **Projection firewalls:** In `rustc` (`src/variance.md`, blob `de259d38c3ec08e53dbe99127a8ee41cfa0f37c0`), `crate_variances` computes whole-crate inference while `variances_of` projects one item's result so downstream users depend only on the item projection.
- **Per-node costs and memory retention:** `rustc` notes that stable fingerprinting is expensive enough that `no_hash` and `eval_always` exist for computations where hashing or dependency recording costs more than reuse saves. In Salsa (`book/src/tuning.md`, blob `0353e2c3324806b346cd6b2d6db465b063c598c0`), memoized tracked-function values are unbounded by default; optional LRU eviction removes values, not query keys or dependency metadata, while durability levels skip walking higher-durability dependencies when only lower-durability inputs changed.

#### 2. Cancellation, cycles, and maintenance history as a correctness surface

- **Cancellation vs. publication fencing:** Before mutating an input through a mutable database handle, Salsa cancels parallel reader handles and waits for them to finish, using intermediate query accesses as unwinding cancellation points. However, in-process revision cancellation does not replace an external publication fence that rejects results from superseded Anneal source/model generations.
- **Cycles:** Salsa panics by default on active query cycles and supports fixed-point iteration (capped at 200 iterations or explicit fallback values) only when participating queries are deterministic and monotone over a finite-height partial order (`book/src/cycles.md`, blob `436a716a074dac430ab979991c65cff5060c9f3f`). `rustc` detects query cycles as errors and removed its earlier cycle-recovery mechanism because its theoretical consequences for incremental compilation were unclear (`src/queries/query-evaluation-model-in-detail.md`).
- **Historical correctness incidents and commits:** In May 2021, Rust 1.52.1 temporarily disabled incremental compilation by default after newly enabled fingerprint verification exposed cache inconsistencies that could cause miscompilations. Salsa's repository history similarly demonstrates the ongoing correctness surface of fine-grained engines: replacing the old Salsa with `salsa-2022` (`38a44eef879be5eca1ce94c09637b23b3a97a529`, 2024-06-19), rewriting cycle handling for fixed-point iteration (`095d8b2b8115c3cf8bf31914dd9ea74648bb7cf9`, 2025-03-10), moving LRU eviction to revision boundaries because immediate eviction was unsound with outstanding references (`201704c5d185187905d0d8c0a963acd5593b19fe`, 2025-02-11), fixing out-of-order cycle-head verification (`0946cbd6478cf2bddfc9ac65b3c254c1f1b1bf95`, 2026-01-22), preserving accumulated values when a memoized query skips execution (`c3d88eb8671d09e1a175aa4d4b391a6242d2d123`, 2026-06-02), guarding unvalidated interned/memo state (`c10e4ade12f6196bbda2a3bc76191eb4e176f25a`, 2026-09-24), and reducing redundant query-completion work (`ff0a022a6a2e7e7929a6169f3815a1a67433613e`, 2026-09-27).

#### 3. Hybrid Anneal graph and four-question granularity gate

A minimal Anneal graph can assign coarse nodes to host-owned stages (source snapshot acquisition, LLBC normalization, Aeneas translation, Lean input preparation, proof-obligation checking, and generation result assembly) while requiring any finer Anneal-owned query boundary to answer four questions:

1. What stable key means "the same logical computation" across the intended revisions?
2. What complete set of semantic inputs can change the result?
3. What equality or fingerprint is strong enough to stop invalidation without hiding a meaningful change?
4. What is the lifecycle of memo values, keys, edges, side outputs, and stale generations?

#### 4. Current-source review of Salsa and `rustc-dev-guide` (`salsa-rustc-current-source-review`)

The source review artifact bundle ([`support/salsa-rustc-current-source-review/matrix.json`](support/salsa-rustc-current-source-review/matrix.json), [`support/salsa-rustc-current-source-review/official-source-observation.json`](support/salsa-rustc-current-source-review/official-source-observation.json), [`support/salsa-rustc-current-source-review/salsa-refs.txt`](support/salsa-rustc-current-source-review/salsa-refs.txt), [`support/salsa-rustc-current-source-review/rustc-guide-refs.txt`](support/salsa-rustc-current-source-review/rustc-guide-refs.txt), and [`support/salsa-rustc-current-source-review/salsa-release-tag-refs.txt`](support/salsa-rustc-current-source-review/salsa-release-tag-refs.txt)) compares the baseline pins against observed branch tips:

- `salsa-rs/salsa` `master` at `30b614d826d697c47bc0f21591fab218f2004032` is 3 commits ahead and 0 behind `a7f8c558555f179ca02f6bdf7397d1317f91aa43` (17 changed paths). GitHub's latest release `salsa-v0.28.5` (published 2026-09-24, annotated tag object `96fe729b8b435820ccf1b5a990d4d076352d67ce` peeling to `d434f8805c60ac60dce5f367ca91c5a7cd3e4c86`) is 9 commits behind the original Salsa pin and 12 behind selected `master`.
- Four of the five pinned Salsa files retain identical Git blobs and content hashes at `30b614d826d697c47bc0f21591fab218f2004032`: `README.md`, `book/src/reference/algorithm.md`, `book/src/tuning.md`, and `book/src/plumbing/database_and_runtime.md`.
- `book/src/cycles.md` changed at `30b614d826d697c47bc0f21591fab218f2004032` (snapshots preserved at [`support/salsa-rustc-current-source-review/snapshots/salsa/pinned/book/src/cycles.md`](support/salsa-rustc-current-source-review/snapshots/salsa/pinned/book/src/cycles.md) and [`support/salsa-rustc-current-source-review/snapshots/salsa/current/book/src/cycles.md`](support/salsa-rustc-current-source-review/snapshots/salsa/current/book/src/cycles.md)): it now states that `cycle_initial` and an initial `cycle_result` fallback must not directly create tracked structs, though they can return a tracked struct created by another tracked query.
- Adjacent Salsa implementation files also changed: `src/function/fetch.rs` ([old](support/salsa-rustc-current-source-review/snapshots/salsa/old/src/function/fetch.rs), [new](support/salsa-rustc-current-source-review/snapshots/salsa/new/src/function/fetch.rs)) records initial cycle-query reads and asserts against directly owned tracked structs; `src/function/execute.rs` ([old](support/salsa-rustc-current-source-review/snapshots/salsa/old/src/function/execute.rs), [new](support/salsa-rustc-current-source-review/snapshots/salsa/new/src/function/execute.rs)) records a previous-result read during recovery; `src/active_query.rs` ([old](support/salsa-rustc-current-source-review/snapshots/salsa/old/src/active_query.rs), [new](support/salsa-rustc-current-source-review/snapshots/salsa/new/src/active_query.rs)) adds that dependency record; and [`support/salsa-rustc-current-source-review/snapshots/salsa/new/tests/cycle_initial_tracked_struct.rs`](support/salsa-rustc-current-source-review/snapshots/salsa/new/tests/cycle_initial_tracked_struct.rs) tests the restriction and helper-query case.
- `rust-lang/rustc-dev-guide` `main` at `be8854f66df1b5450349061e45374ac072abd109` is 27 commits ahead and 0 behind `8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85` (11 changed paths). Both pinned guide blobs—[`support/salsa-rustc-current-source-review/snapshots/rustc_dev_guide/current/src/queries/incremental-compilation-in-detail.md`](support/salsa-rustc-current-source-review/snapshots/rustc_dev_guide/current/src/queries/incremental-compilation-in-detail.md) (`9893edd54b950155da586843baa3319da15dcc4e`) and [`support/salsa-rustc-current-source-review/snapshots/rustc_dev_guide/current/src/variance.md`](support/salsa-rustc-current-source-review/snapshots/rustc_dev_guide/current/src/variance.md) (`de259d38c3ec08e53dbe99127a8ee41cfa0f37c0`)—are byte-identical, while unpinned `src/query.md` ([old](support/salsa-rustc-current-source-review/snapshots/rustc_dev_guide/old/src/query.md), [new](support/salsa-rustc-current-source-review/snapshots/rustc_dev_guide/new/src/query.md)) changes only line wrapping and spacing in inspected hunks.

---

### Buck to Buck2: Single-Graph Rewrite, DICE, and Current-Source Recheck (`buck-to-buck2-one-graph-rewrite-2013-2026` and `buck2-current-source-review`)

#### 1. Structural limitations in Buck1 and what Buck2 unified

Buck1 had multiple graph-shaped phases—target-graph construction, action-graph construction, and action execution—plus operations outside tracked graphs (such as running `ocamldep` after parsing a BUCK file without complete dependency tracking, causing spurious build failures on large import changes), and embedded language rules as Java classes inside the Buck executable.

Buck2 (`facebook/buck2@738e69a6c5f1efb6a015645228e7a19ee9b1d9c0`) moved language rules into Starlark behind a smaller, language-agnostic rule API (exposing dep files, incremental actions, dynamic dependencies, anonymous targets, and transitive sets as general APIs) and replaced separate target and action phases with one dynamic incremental dependency graph in DICE. DICE keys identify computations, record requested DICE dependencies, deduplicate concurrent identical requests, and stop invalidation via early cutoff when a recomputed value equals its prior value—while keeping distinct domain APIs for rule evaluation, configuration, artifact execution, remote execution, and materialization.

#### 2. Reported outcomes versus causal isolation and DICE internal complexity

Meta's first-party reports (`docs/about/why.md` blob `6799f38df279cc03f1806b1d0d447fb19570bcfa` and `docs/about/benefits/compared_to_buck1.md` blob `296661b09239357fa870a55192dff6c5d54c25ca`, plus the 2023-04-06 launch account) describe roughly 2x faster internal builds, no-op builds dropping from 23 seconds to 0.1 seconds in a cited benchmark, 5% (10s) to 42% (145s) incremental improvements on header/Thrift edits, 2–4x faster CI projects, and many missing dependencies uncovered during migration. Because Buck2 changed implementation language (Java to Rust), rule architecture, remote execution, caching, VFS integration, and DICE simultaneously, the public evidence supports whole-architecture improvement rather than isolating the single graph alone.

Internally, `dice/dice/docs/index.md` (`46897b9bd66a7bd055bbad8db7f363558347d4f0`) and `docs/insights_and_knowledge/modern_dice.md` (`04a9950e2b077cdfdf91ca3e6e6ede68df508580`) document that DICE moved from fine-grained shared locking to a single-threaded core-state component and highlight two fundamental hazards:

1. **Equality across versions:** A key or value unique during one command may not denote the same semantic object across transactions.
2. **Untracked data flow:** Mutable state behind locks, lazily initialized values, or per-transaction user data can bypass DICE dependency tracking and cause unsound reuse.

#### 3. Threshold for Anneal

Anneal should borrow Buck2's boundary discipline—one authoritative freshness and publication check, domain policy outside the core, and treating hidden input flow as a correctness defect—without building a DICE-like engine unless concrete workloads simultaneously exhibit runtime dependency discovery that cannot be normalized into preparation, expensive cross-request recomputation where early cutoff materially helps, concurrent overlapping client requests, repeated bugs from split invalidation logic, stable cross-generation key/value equality, and profiling showing orchestration/recomputation on the critical path.

#### 4. Current-source review of Buck2 (`buck2-current-source-review`)

The Buck2 source-review artifacts ([`support/buck2-current-source-review/matrix.json`](support/buck2-current-source-review/matrix.json), [`support/buck2-current-source-review/official-source-observation.json`](support/buck2-current-source-review/official-source-observation.json), [`support/buck2-current-source-review/official-tag-refs.txt`](support/buck2-current-source-review/official-tag-refs.txt), and [`support/buck2-current-source-review/official-ref-recheck.txt`](support/buck2-current-source-review/official-ref-recheck.txt)) establish:

- Official `facebook/buck2` `main` at `b2b7ba58b5188aa35adc784d8ec6425dd93b98df` is 29 commits ahead of `738e69a6c5f1efb6a015645228e7a19ee9b1d9c0` (114 changed files). The latest date-named tag `2026-09-15` (`6507dd157a6f81a810c48583edf1758dd0c337c5`) is 514 commits behind the original pin and 543 behind selected `main`, while the floating `latest` tag moved from `0161ff601e2f82af9b8cd431e04e7d9acf9f305c` to `b2b7ba58b5188aa35adc784d8ec6425dd93b98df`.
- All four cited Buck2 documentation blobs (`docs/about/why.md`, `docs/about/benefits/compared_to_buck1.md`, `dice/dice/docs/index.md`, and `docs/insights_and_knowledge/modern_dice.md`) are unchanged in both Git blob SHA-1 and content SHA-256.
- Three adjacent DICE implementation files changed in the 29-commit range:

| Changed source path | Direct source observation |
| --- | --- |
| [`dice/dice/src/api/computations.rs`](https://github.com/facebook/buck2/blob/b2b7ba58b5188aa35adc784d8ec6425dd93b98df/dice/dice/src/api/computations.rs) | Adds a public `compute_with_key` method that returns the key allocation DICE retains alongside the computed value. |
| [`dice/dice/src/epoch/ctx.rs`](https://github.com/facebook/buck2/blob/b2b7ba58b5188aa35adc784d8ec6425dd93b98df/dice/dice/src/epoch/ctx.rs) | Adds the tracked-computation implementation and `canonical_key` lookup from the key index. |
| [`dice/dice/src/epoch/tests/general.rs`](https://github.com/facebook/buck2/blob/b2b7ba58b5188aa35adc784d8ec6425dd93b98df/dice/dice/src/epoch/tests/general.rs) | Adds a source test asserting that equal keys requested through different paths share the retained allocation. The test was not run. |

---

### *Build Systems à la Carte* as a Vocabulary for Anneal Orchestration (`build-systems-a-la-carte-anneal-orchestration-2018-2026`)

#### 1. Decomposition of schedulers, rebuilders, and task purity

Mokhov, Mitchell, and Peyton Jones (ICFP 2018; JFP 2020; `snowleopard/build@43b18b9a362d7d27b64679ea4122e4b8c5dfedd9`, `src/Build/System.hs` blob `dad42cd5b94e0bc51af79987b586e4c1885982c1`) orthogonalize **schedulers** (topological, restarting, suspending), **rebuilders** (dirty bits, verifying traces, constructive traces, deep constructive traces), and **task dependency expression** (applicative/static vs. monadic/dynamic):

- Make is modeled as topological scheduler + modification-time rebuilder;
- Ninja as topological + verifying traces;
- Excel as restarting + dirty bits;
- Shake as suspending + verifying traces;
- Bazel as restarting + constructive traces;
- Nix as suspending + deep constructive traces.

For Anneal, this maps to six distinct architectural dimensions:

| Dimension | Build-systems vocabulary | Anneal question |
| --- | --- | --- |
| Dependency expression | static/applicative, dynamic/monadic, or outside the model | Can Anneal enumerate the semantic inputs to this stage before execution, learn them through an explicit dependency callback, or only observe an opaque tool boundary? |
| Scheduling | topological, restarting, suspending, or delegated | Does Anneal need to order coarse stages itself, or should an upstream tool own the internal graph? |
| Rebuilding | always rebuild, dirty/approximate, verifying trace, constructive trace, deep constructive trace | What evidence is sufficient to reuse a previous stage result? |
| Persistence | no memory, current trace, historical traces, content cache | Which retained state has enough identity to be evidence rather than merely an optimization hint? |
| Effects | pure declared task vs untracked/nondeterministic/volatile behavior | Which environment, daemon, filesystem, plugin, clock, randomness, or external-state effects must be explicit or isolated? |
| Acceptance authority | not the paper's scheduler/rebuilder problem | What proves that a completed result belongs to the current verification request and may become user-visible/current? |

#### 2. Topological baseline, dynamic-discovery limits, interactive buffers, and publication authority

- **Coarse topological scheduler:** Because Anneal's outer pipeline handoffs (Rust/Cargo compilation subject → Charon/LLBC generation → Aeneas translation → prepared Lake/Lean environment) are largely static at the host layer, a topological DAG scheduler can order coarse stages, parallelize independent subjects, deduplicate identical in-flight work, route cancellation, and label generations without duplicating Cargo's, Lake's, or Lean's internal dependency engines.
- **Dynamic scheduling requires a real dependency channel:** Running an opaque subprocess inside a suspending scheduler does not expose unmodeled reads. Untracked inputs must be (1) made explicit in the stage request, (2) delegated to an upstream tool whose output generation is identified, (3) constrained by process reset/isolation, or (4) treated as volatile.
- **Rebuilder progression and "Frankenbuild" hazard:** Deep constructive traces skip intermediate materialization by indexing terminal inputs, which requires deterministic tasks and loses intermediate early cutoff; mixing nondeterministic intermediates under a deep cache causes inconsistent "Frankenbuild" states.
- **Interactive buffers are values, not ambient paths:** Rewriting a `.lean` file on disk does not update an already-open Lean LSP buffer; the store key/value mapping for interactive stages must capture `document-generation -> bytes` and `prepared-environment-id -> environment` rather than `path -> bytes`.
- **Four distinct authority transitions:**
  - *scheduler:* may this task run now?
  - *rebuilder/cache:* may this previous value be reused for this task identity?
  - *verification acceptance:* does this completed output satisfy the requested evidence contract?
  - *publication fence:* is that accepted result still current and authorized to replace the user-visible/current result?

| Concern | Small baseline | What would justify something richer |
| --- | --- | --- |
| Coarse dependency order | Explicit static DAG over host-owned stages | A real Anneal-level dependency that is discovered only after executing another stage |
| Stage scheduling | Topological readiness + bounded worker pool | Measured restart waste from runtime-discovered dependencies large enough to justify suspension/restart machinery |
| Initial rebuilding | Always run opaque stages; rely on upstream-native incremental behavior | Complete stage identity and stable output semantics that permit safe verification/reuse |
| Coarse reuse | Verify exact input/environment/generation identity before keeping prior output | Representative workloads showing substantial wins from multi-generation/history retention |
| Cached output restoration | None by default | Deterministic/equivalent stage semantics, content identity, tool/environment closure, and measured recomputation cost |
| Internal compiler/build graph | Delegate to Cargo/Lake/Lean/native engine | Demonstrated cross-tool optimization that cannot be obtained through coarse composition |
| Interactive source | Immutable buffer/document snapshot in request | Nothing richer is needed merely to represent edits; finer internal queries are a separate question |
| Opaque process state | Fresh/reset/disposable worker where feasible; explicit environment identity | Upstream service contract proving stronger reusable-state semantics |
| Cancellation/publication | Generation/request fencing outside scheduler | Stronger transactional protocol if publication spans several independently visible artifacts |

---

### Make and Ninja: Narrow Execution, Displaced Policy, and Current-Source Recheck (`make-ninja-narrow-build-tool-boundaries-1979-2026` and `ninja-current-source-review`)

#### 1. Make versus Ninja responsibility boundaries

Feldman's 1979 Make paper (`10.1002/spe.4380090402`) separated dependency relationships from opaque shell recipes, while mature GNU Make `4.4.1` accumulated a rich human-authored meta-build language (variables, functions, implicit/pattern rules, conditionals, includes, and recursive Make—whose incomplete-DAG hazards Peter Miller analyzed). Evan Martin created Ninja in 2011 after Chromium's generated non-recursive Makefiles still spent roughly ten seconds deciding what to do after a one-file edit. Ninja (`ninja-build/ninja@4e4df1e567eb3c1475a51af261cba2bfff60b4be`, `doc/manual.asciidoc` blob `81ecf7d388f899a1481df9f25ec1065710de679d`) displaced configuration and policy into generators (GN, CMake) while adding executor mechanisms where correctness, freshness, or resource coordination resisted displacement: command-line recording, compiler `depfile`/`deps` logs, `restat` output-unchanged pruning, bounded `dyndep` (since 1.10), `validations` (since 1.11), resource `pool`s, and GNU Make jobserver client (1.13) and server (post-1.13/1.14 manual) support.

| Responsibility | GNU Make tendency | Ninja tendency | Architectural consequence |
| --- | --- | --- | --- |
| Human-authored graph/policy | Often directly in Makefiles | Expected in separate generator | Ninja makes the generated graph an explicit intermediate interface |
| Command semantics | Opaque recipes | Opaque commands | Both require declared/captured inputs for sound freshness |
| Built-in domain conventions | Many implicit rules/conventional variables | Explicit non-goal | Make trades executor complexity for convenience |
| Configuration decisions | Can occur while reading/evaluating Makefiles | Intended before Ninja runs | Ninja removes repeated decision cost from the hot loop |
| Compiler-discovered dependencies | Commonly generated Make fragments / explicit techniques | First-class depfile/deps support | Runtime facts need a protocol somewhere |
| Command identity | User techniques possible | Recorded by Ninja | Executor owns a freshness fact it can observe cheaply |
| Dynamic graph additions | Expressive Make evaluation/recursive techniques | Constrained `dyndep` protocol | Ninja prefers bounded mutation over a general runtime language |
| Parallel resources | `-j` and GNU jobserver | pools plus jobserver interoperability | Cross-process resources are runtime state, not static project policy |

#### 2. Division between Anneal orchestration and a stable batch verifier

A narrow Anneal batch verification boundary can leave workspace discovery, file watching, user configuration translation, interactive advisory caches, progress presentation, and job scheduling to an outer host or daemon, while retaining or validating at the authoritative boundary all facts that define verification-success meaning: exact source/model/tool identity, complete obligation coverage for the advertised promise, unsupported/assumed semantics classification, TCB/trust accounting, subject-to-evidence association, and publication fencing. If a batch runner blindly trusts a daemon-generated plan without validation, the plan generator becomes part of the TCB for the claim.

#### 3. Current-source review of Ninja (`ninja-current-source-review`)

The Ninja source-review artifacts ([`support/ninja-current-source-review/matrix.json`](support/ninja-current-source-review/matrix.json), [`support/ninja-current-source-review/official-source-observation.json`](support/ninja-current-source-review/official-source-observation.json), [`support/ninja-current-source-review/frozen-cohort.csv`](support/ninja-current-source-review/frozen-cohort.csv), [`support/ninja-current-source-review/version-inventory-ebcdcad-581.csv`](support/ninja-current-source-review/version-inventory-ebcdcad-581.csv), and [`support/ninja-current-source-review/baseline-report-paths.txt`](support/ninja-current-source-review/baseline-report-paths.txt)) verify:

- On 2026-09-30, official `ninja-build/ninja` `master` resolved to the identical commit `4e4df1e567eb3c1475a51af261cba2bfff60b4be` with the identical `doc/manual.asciidoc` Git blob `81ecf7d388f899a1481df9f25ec1065710de679d` (0 commits ahead, 0 changed files).
- The latest official GitHub release is `v1.13.2` at commit `3441b633c2fe2c494e958780ba0f4227b1327634` (published 2025-11-20), whose history is diverged relative to `master` (from release tag to `master` pin: 196 commits ahead and 60 behind, with manual blob `a9b97ee92b67d5d3a246d2e06e94bf44ff70b0c5`).

## Boundaries

### Adapton and Self-Adjusting Computation Boundaries
- No Adapton, Nominal Adapton, Fungi, SAIL, Charon, Aeneas, Lean, or Anneal runtime benchmark was executed, and this report does not reproduce the Adapton, Nominal Adapton, or Twelf/SAIL metatheory outside the authors' published theorems and modeled language assumptions.
- Arbitrary external subprocesses do not obtain DCG or self-adjusting-computation from-scratch consistency merely because an orchestrator caches, names, or restarts them.
- Stable IDs, source positions, content hashes, or worker epochs do not by themselves prove that hidden ambient dependencies are unchanged, nor does from-scratch consistency provide a liveness theorem, resource bound, source/model correspondence proof, or proof of upstream tool correctness.

### Early Cutoff and Salsa/`rustc` Query Boundaries
- Jane Street Incremental's `set_cutoff` permits approximate predicates that are not semantic equivalences; `rustc`'s 128-bit stable fingerprints carry a negligible but nonzero hash-collision assumption; and GHC's ABI/entity fingerprints rely on compiler-specific machinery for inlining, plugins, Template Haskell, and orphan instances rather than exported types alone.
- The Charon/Aeneas comment and relocation fixture is bounded evidence showing that semantic output and source provenance can diverge; it does not prove that arbitrary comments, macros, or workspace relocations are semantically inert.
- In the Salsa/`rustc` current-source review, `runtime_result` is `unexecuted_in_this_review` and `anneal_product_result` is `unassessed`; the review inspected `salsa-rs/salsa` and `rust-lang/rustc-dev-guide` rather than auditing the full `rust-lang/rust` compiler source.

### Buck2, *Build Systems à la Carte*, and Make/Ninja Boundaries
- Performance numbers for Buck2 and historical Chromium Make/Ninja startup are first-party reported figures, not independently reproduced benchmarks, and Buck2's reported gains cannot be attributed to DICE alone given simultaneous changes in language, rule API, remote execution, VFS, and caching.
- *Build Systems à la Carte* executable models capture the conceptual essence of Make, Ninja, Shake, Bazel, Buck, Nix, and Excel rather than serving as 2026 conformance specifications for those production tools.
- Neither Make nor Ninja makes arbitrary recipes hermetic, and build-system up-to-date freshness is weaker than Anneal verification-success authority. In the Buck2 and Ninja current-source reviews, no binaries or tests were executed (`runtime_result: unexecuted_in_this_review`, `anneal_product_result: unassessed`).

## Evidence

### Adapton and Nominal Incremental Computation (`adapton-names-identity-freshness-2014-2018`)
- **Primary publications:**
  - Hammer, Khoo, Hicks, and Foster, *Adapton: Composable, Demand-Driven Incremental Computation*, PLDI 2014, DOI `10.1145/2594291.2594324` (`https://www.cs.umd.edu/~mwh/papers/hammer13adapton.html`, UMD TR `https://drum.lib.umd.edu/items/b7401a53-964b-4f78-8b2d-a93ab750bb0a`).
  - Hammer et al., *Incremental Computation with Names*, OOPSLA 2015, DOI `10.1145/2814270.2814305`, extended version `arXiv:1503.07792v6`.
  - Hammer, Dunfield, Economou, and Narasimhamurthy, *Refinement Types for Precisely Named Cache Locations*, `arXiv:1610.00097`.
  - Hammer et al., *Fungi: Typed Incremental Computation with Names*, `arXiv:1808.07826v1`.
- **Support artifacts:** [`support/adapton-names-identity-freshness-2014-2018/evidence-map.json`](support/adapton-names-identity-freshness-2014-2018/evidence-map.json).

### Self-Adjusting Computation (`self-adjusting-computation-from-scratch-consistency-2005-2013`)
- **Primary publications:**
  - Umut A. Acar, *Self-Adjusting Computation*, PhD thesis, Carnegie Mellon University, `CMU-CS-05-129`, 2005 (`https://www.cs.cmu.edu/~rwh/students/acar.pdf`).
  - Acar, Blelloch, and Harper, *Adaptive Functional Programming*, ACM TOPLAS 28(6), 2006, DOI `10.1145/1186632.1186634` (`https://www.cs.cmu.edu/~rwh/papers/afp/toplas06.pdf`).
  - Acar, Ahmed, and Blume, *Imperative Self-Adjusting Computation*, POPL 2008, DOI `10.1145/1328438.1328476`, University of Chicago `TR-2007-18`.
  - Acar, Blume, and Donham, *A Consistent Semantics of Self-Adjusting Computation*, JFP 23(3), 2013, DOI `10.1017/S0956796813000099` (Twelf proof artifact at `https://www.cs.cmu.edu/~jdonham/aml-proof/`).
  - Anderson, Blelloch, Baweja, and Acar, *Efficient Parallel Self-Adjusting Computation*, SPAA 2021, DOI `10.1145/3409964.3461799`.
- **Support artifacts:** [`support/self-adjusting-computation-from-scratch-consistency-2005-2013/evidence-map.json`](support/self-adjusting-computation-from-scratch-consistency-2005-2013/evidence-map.json).

### Early Cutoff (`early-cutoff-equality-relations-2010-2026`)
- **`rustc` (`rust-lang/rustc-dev-guide@8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85`):** `src/queries/incremental-compilation.md` (`079a2b2e00a7f2dd088fab5a4d74541a53659ea1`), `src/queries/incremental-compilation-in-detail.md` (`9893edd54b950155da586843baa3319da15dcc4e`), and Michael Woerister, "Incremental Compilation," Rust Blog, 2016-09-08.
- **Jane Street Incremental (`janestreet/incremental@98b5750ec3c006641351bfd858a89136a5dbc52c`):** `src/incremental_intf.ml` (`eabce575943287f144a8f66cf342fd9db438a33e`), plus Yaron Minsky, "Introducing Incremental" (2015-07-18) and "Self Adjusting DOM."
- **GHC (`ghc/ghc@234bab081682018da7d04b22eee4b80f70381d07`):** `compiler/GHC/Iface/Recomp.hs` (`cbd1d392ccd3cee37a0c4dd7dc75ec6117a88dc8`) and GHC 7.0 user guide recompilation documentation.
- **Support artifacts:** [`support/early-cutoff-equality-relations-2010-2026/source-map.json`](support/early-cutoff-equality-relations-2010-2026/source-map.json).

### Salsa and `rustc` Query Granularity and Current-Source Recheck (`salsa-rustc-query-granularity-2016-2026` and `salsa-rustc-current-source-review`)
- **Salsa (`salsa-rs/salsa@a7f8c558555f179ca02f6bdf7397d1317f91aa43` and `30b614d826d697c47bc0f21591fab218f2004032`, plus tag `salsa-v0.28.5` at `d434f8805c60ac60dce5f367ca91c5a7cd3e4c86`):** `README.md` (`1e4afef11f4e66f16573457b220ec19d495fa742`), `book/src/reference/algorithm.md` (`2b6d9e5357388e85302e81fa23ff281d62ae62de`), `book/src/tuning.md` (`0353e2c3324806b346cd6b2d6db465b063c598c0`), `book/src/cycles.md` (pinned `436a716a074dac430ab979991c65cff5060c9f3f` and current `master`), `book/src/plumbing/database_and_runtime.md` (`eb70cab9b21f436133c72134901024c3dc040fb0`), `src/function/fetch.rs`, `src/function/execute.rs`, `src/active_query.rs`, `tests/cycle_initial_tracked_struct.rs`, and history commits `38a44eef879be5eca1ce94c09637b23b3a97a529`, `201704c5d185187905d0d8c0a963acd5593b19fe`, `095d8b2b8115c3cf8bf31914dd9ea74648bb7cf9`, `0946cbd6478cf2bddfc9ac65b3c254c1f1b1bf95`, `c3d88eb8671d09e1a175aa4d4b391a6242d2d123`, `c10e4ade12f6196bbda2a3bc76191eb4e176f25a`, and `ff0a022a6a2e7e7929a6169f3815a1a67433613e`.
- **`rustc-dev-guide` (`8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85` and `be8854f66df1b5450349061e45374ac072abd109`):** `src/query.md`, `src/queries/incremental-compilation.md`, `src/queries/incremental-compilation-in-detail.md` (`9893edd54b950155da586843baa3319da15dcc4e`), `src/queries/query-evaluation-model-in-detail.md`, `src/variance.md` (`de259d38c3ec08e53dbe99127a8ee41cfa0f37c0`), `src/solve/caching.md`, plus the Rust 1.52.1 announcement (`https://blog.rust-lang.org/2021/05/10/Rust-1.52.1/`).
- **Support artifacts:** [`support/salsa-rustc-query-granularity-2016-2026/evidence.json`](support/salsa-rustc-query-granularity-2016-2026/evidence.json), [`support/salsa-rustc-current-source-review/matrix.json`](support/salsa-rustc-current-source-review/matrix.json), [`support/salsa-rustc-current-source-review/official-source-observation.json`](support/salsa-rustc-current-source-review/official-source-observation.json), [`support/salsa-rustc-current-source-review/check_matrix.py`](support/salsa-rustc-current-source-review/check_matrix.py), [`support/salsa-rustc-current-source-review/frozen-cohort.csv`](support/salsa-rustc-current-source-review/frozen-cohort.csv), [`support/salsa-rustc-current-source-review/version-inventory-ebcdcad-581.csv`](support/salsa-rustc-current-source-review/version-inventory-ebcdcad-581.csv), and [`support/salsa-rustc-current-source-review/baseline-report-paths.txt`](support/salsa-rustc-current-source-review/baseline-report-paths.txt).

### Buck to Buck2 and Current-Source Recheck (`buck-to-buck2-one-graph-rewrite-2013-2026` and `buck2-current-source-review`)
- **Buck1 (`facebook/buck@9c7c421e49f4d92d67321f18c6d1cd90974c77c4`):** `README.md` (`59e9fda6c885670ebb3e0ce1b799ea8f9e97cf9c`).
- **Buck2 (`facebook/buck2@738e69a6c5f1efb6a015645228e7a19ee9b1d9c0`, `b2b7ba58b5188aa35adc784d8ec6425dd93b98df`, and tag `2026-09-15` at `6507dd157a6f81a810c48583edf1758dd0c337c5`):** `docs/about/why.md` (`6799f38df279cc03f1806b1d0d447fb19570bcfa`), `docs/about/benefits/compared_to_buck1.md` (`296661b09239357fa870a55192dff6c5d54c25ca`), `dice/dice/docs/index.md` (`46897b9bd66a7bd055bbad8db7f363558347d4f0`), `docs/insights_and_knowledge/modern_dice.md` (`04a9950e2b077cdfdf91ca3e6e6ede68df508580`), plus Meta Engineering launch post (`https://engineering.fb.com/2023/04/06/open-source/buck2-open-source-large-scale-build-system/`).
- **Support artifacts:** [`support/buck2-current-source-review/matrix.json`](support/buck2-current-source-review/matrix.json), [`support/buck2-current-source-review/official-source-observation.json`](support/buck2-current-source-review/official-source-observation.json), [`support/buck2-current-source-review/official-tag-refs.txt`](support/buck2-current-source-review/official-tag-refs.txt), [`support/buck2-current-source-review/official-ref-recheck.txt`](support/buck2-current-source-review/official-ref-recheck.txt), [`support/buck2-current-source-review/check_matrix.py`](support/buck2-current-source-review/check_matrix.py), [`support/buck2-current-source-review/frozen-cohort.csv`](support/buck2-current-source-review/frozen-cohort.csv), [`support/buck2-current-source-review/version-inventory-ebcdcad-581.csv`](support/buck2-current-source-review/version-inventory-ebcdcad-581.csv), and [`support/buck2-current-source-review/baseline-report-paths.txt`](support/buck2-current-source-review/baseline-report-paths.txt).

### *Build Systems à la Carte* (`build-systems-a-la-carte-anneal-orchestration-2018-2026`)
- **Primary publications and source (`snowleopard/build@43b18b9a362d7d27b64679ea4122e4b8c5dfedd9`):** ICFP 2018 (`10.1145/3236774`), JFP 2020 (`10.1017/S0956796820000088`), `papers/jfp/1-intro.tex` (`6f38ee9da5913e526367084c2a32e327e9d683f0`), `papers/jfp/3-abstractions.tex` (`c2f6b35e642e410c15c28fb7b641b9d13285d5e3`), `papers/jfp/4-schedulers.tex` (`6e78793e8035fc21d1e3b237dea37f4ee5e8398c`), `papers/jfp/5-rebuilders.tex` (`e08d004c04f3114b9213f509861cb4a824edc89a`), `papers/jfp/7-experience.tex` (`cb07bc7992dc84fe91ccafc11f9d1292d2d1b0b1`), `papers/jfp/8-engineering.tex` (`d4da065f2c762ad7046ac85df0aef3f744fb5ed5`), `papers/jfp/10-conclusions.tex` (`4da36d2b2df586d336a34555487193238c056e9b`), `src/Build/System.hs` (`dad42cd5b94e0bc51af79987b586e4c1885982c1`), `src/Build/Scheduler.hs` (`57fc2578aef538e065e361223206439bec883851`), `src/Build/Rebuilder.hs` (`45233a9fb46ef7e3b7956cd61d2c7a8ce3ca5f15`), and `README.md` (`ac3242ba441be71effbd935edd8041f01c651bd6`).
- **Support artifacts:** [`support/build-systems-a-la-carte-anneal-orchestration-2018-2026/evidence-map.json`](support/build-systems-a-la-carte-anneal-orchestration-2018-2026/evidence-map.json).

### Make and Ninja and Current-Source Recheck (`make-ninja-narrow-build-tool-boundaries-1979-2026` and `ninja-current-source-review`)
- **Make:** Stuart I. Feldman, "Make — a program for maintaining computer programs," *Software: Practice and Experience* 9(4):255–265, 1979, DOI `10.1002/spe.4380090402`; GNU Make `4.4.1` manual and release (2023-02-26, tarball MD5 `c8469a3713cbbe04d955d4ae4be23eeb`); Peter Miller, "Recursive Make Considered Harmful."
- **Ninja:** Evan Martin, "Ninja, a new build system" (2011-02-06); early Chromium Ninja manual (`a9071772ead9522d7ebb21048da08c8ea22cec21`); `ninja-build/ninja` `master` at `4e4df1e567eb3c1475a51af261cba2bfff60b4be` (`doc/manual.asciidoc` blob `81ecf7d388f899a1481df9f25ec1065710de679d`); and release `v1.13.2` at `3441b633c2fe2c494e958780ba0f4227b1327634` (manual blob `a9b97ee92b67d5d3a246d2e06e94bf44ff70b0c5`).
- **Support artifacts:** [`support/make-ninja-narrow-build-tool-boundaries-1979-2026/evidence-map.json`](support/make-ninja-narrow-build-tool-boundaries-1979-2026/evidence-map.json), [`support/ninja-current-source-review/matrix.json`](support/ninja-current-source-review/matrix.json), [`support/ninja-current-source-review/official-source-observation.json`](support/ninja-current-source-review/official-source-observation.json), [`support/ninja-current-source-review/check_matrix.py`](support/ninja-current-source-review/check_matrix.py), [`support/ninja-current-source-review/frozen-cohort.csv`](support/ninja-current-source-review/frozen-cohort.csv), [`support/ninja-current-source-review/version-inventory-ebcdcad-581.csv`](support/ninja-current-source-review/version-inventory-ebcdcad-581.csv), and [`support/ninja-current-source-review/baseline-report-paths.txt`](support/ninja-current-source-review/baseline-report-paths.txt).

### Anneal Design Authority
- `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`: `anneal/PRINCIPLES.md` (`d5339a95254eae14ac201139d07d9d36d48a19fb`), `anneal/DESIGN.md` (`0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`), and `anneal/README.md` (`bf22d554437659f38d8918c1e7c3480f4f62b126`).

## Revalidation

1. **Adapton, Self-Adjusting Computation, and Warm-vs-Fresh Oracles:** Revalidate when Anneal adopts a concrete persistent identity, generation, dependency-fingerprint, or cache-validity schema, or when Charon, Aeneas (`ac9f1bc5262a5e4ff1e24ca78617121382202727`), or Lean expose a supported edit/invalidation protocol. Test candidate stages with a warm-versus-fresh edit matrix covering body edits, declaration insert/delete/rename, file deletion/recreation, dependency/config changes, `cfg`/environment changes, tool/plugin revisions, prepared-environment replacement, and worker restart. Any reuse decision whose claimed freshness cannot be explained from a conservative dependency closure or that diverges from `R_fresh(I)` falsifies the reuse contract.
2. **Early Cutoff and Claim-Relative Projections:** Revalidate against the seven-cell edit matrix (exact no-op rewrite, span-preserving comment/whitespace edit, source relocation, private edit preserving exported proof obligations, obligation-changing edit, trust/environment change with unchanged source, and presentation-only source-map change), verifying that every skipped downstream stage consumed a projection proven equal under its declared cutoff while diagnostics and final verification acceptance refer to the current source identity.
3. **Salsa and `rustc` Query Granularity and Source Rechecks:** Re-read `book/src/reference/algorithm.md`, `book/src/tuning.md`, `book/src/cycles.md`, and `book/src/plumbing/database_and_runtime.md` in `salsa-rs/salsa` and the query chapters in `rust-lang/rustc-dev-guide`, and run `python3 support/salsa-rustc-current-source-review/check_matrix.py` to verify the frozen matrix and snapshots. Before adopting item-level reuse in Anneal, measure wall time, recomputed nodes, dependency-edge count, retained memory after many revisions, and cache hit rate against a clean-recompute oracle.
4. **Buck2, *Build Systems à la Carte*, and Make/Ninja Boundaries:** Diff `facebook/buck2` DICE documentation and source (`python3 support/buck2-current-source-review/check_matrix.py`), `snowleopard/build` scheduler/rebuilder definitions, GNU Make's manual, and `ninja-build/ninja`'s `doc/manual.asciidoc` (`python3 support/ninja-current-source-review/check_matrix.py`). Re-evaluate Anneal's coarse topological DAG and batch/daemon split if Anneal exposes stage-level dynamic dependency callbacks, adopts an upstream cross-request incremental contract, demonstrates that coarse recomputation dominates interactive latency, or establishes deterministic content-addressed reuse closures.
