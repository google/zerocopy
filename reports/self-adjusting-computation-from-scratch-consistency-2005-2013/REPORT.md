# From-scratch consistency is a specification, not a property of reuse by itself

## Summary

Self-adjusting computation gives a precise answer to the central correctness question behind incremental reuse: after the input changes, the adjusted computation should have the same observable meaning as evaluating the program afresh on the changed input. The result is stronger than “we invalidated the nodes we knew about” and weaker than “incrementality is always fast.” In the Acar line of work, the equivalence is proved because the language and runtime control the relevant mutable state, record the dependencies created by reads and writes, and constrain how old traces may be reused. Later work extends the model from write-once functional-style modifiables to multiple writes and cyclic stores; it does not turn arbitrary ambient effects into tracked dependencies.

For Anneal, this is most useful as an **acceptance specification for reuse**. A reused or incrementally updated stage may be treated as current only if its observable result is equivalent to a fresh execution for the same source/model/tool environment. That statement is meaningful only after defining the complete logical input and observable outcome. Rust source bytes, generated inputs, tool and plugin identities, configuration, relevant environment variables, dependency files, and other ambient reads cannot disappear from that accounting merely because a cache key or worker handle stayed the same.

The literature therefore does **not** imply that Anneal should implement a self-adjusting-computation runtime, instrument Aeneas or Lean with dynamic dependence graphs, or retain fine-grained traces. A coarse design can satisfy the same correctness relation by re-running an opaque stage whenever it cannot establish that all semantically relevant inputs are unchanged. Fine-grained incrementality becomes justified only when a stage exposes a trustworthy dependency/snapshot contract and the saved work is worth its additional state and invalidation burden.

This distinction matches Anneal's current authority. Verification success needs exact identity and scope, unsupported or missing evidence cannot silently become success, and effects that matter to the promise must remain represented. From-scratch equivalence can sharpen those requirements for reused computation; it does not itself prove source/model correspondence, tool correctness, termination, or acceptable latency.

## Applicability

The historical account covers the self-adjusting-computation line from Acar's 2005 thesis through the 2006 adaptive-functional formulation, the 2008 imperative extension, and the 2013 consistent memoizing semantics. These works use language/runtime mechanisms specifically designed to expose changing data and record dependencies. Their theorems apply to those formal languages and semantics, not directly to arbitrary subprocesses, build systems, compilers, proof assistants, filesystems, plugins, clocks, networks, or OS process state.

The Anneal application is derived analysis against `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Those documents are authoritative over this report. They deliberately do not choose an execution backend, cache design, result schema, tool boundary, or atomic verification subject. Nothing here adopts such a mechanism.

In this report, **from-scratch consistency** means the following specification shape. For a stage or operation `F`, define a logical input/world `I` and an observable outcome relation `≈`. If an incremental or reused execution starts from prior state `S` and is updated to `I`, then a completed reusable outcome `R_inc(S, I)` is current only when it is observationally equivalent to a fresh execution `R_fresh(I)`:

`R_inc(S, I) ≈ R_fresh(I)`.

The equality relation need not mean byte-for-byte identity. For Anneal it may need to abstract from irrelevant timestamps, cache paths, process IDs, diagnostic ordering, or other non-semantic differences while preserving anything that affects verification-success meaning: accepted obligations, source/model correspondence, trusted assumptions, generated theorem content, relevant diagnostics, and declared failure/partial-result state. Defining `I` and `≈` is part of the engineering work; neither is supplied by the literature.

The report does not claim that every Anneal operation needs this relation. Best-effort editor hints may intentionally have weaker freshness semantics if they are clearly distinguished from accepted results. The relation matters wherever reuse can contribute evidence to an ordinary verification result or otherwise be represented as current authoritative state.

## Findings

### 1. The original correctness target is equivalence with a fresh run, not preservation of a cache data structure

Acar's 2005 thesis states the core correctness criterion directly: change propagation is correct when it is semantically equivalent to executing the program from scratch on the changed input. The thesis separates this from performance. It can then ask a second question: how much of the old execution can be reused, and how much faster is propagation than recomputation?

The mechanism is a dynamic dependence graph (DDG). An initial execution records control and data dependencies. When an explicitly changeable input is updated, change propagation re-executes affected computations and updates the DDG. Memoized DDGs add reuse: a previously computed call can be reused together with its dependency subgraph, after which change propagation adjusts that reused computation to intervening mutations.

The important architectural point is what justifies reuse. A location's identity or a memo match does not by itself establish that the old answer is current. Reuse is paired with the trace/dependency machinery that knows what must be reconsidered. The thesis explicitly notes the difficulty of ordinary memoization under side effects: checking every memory location a function might read would defeat efficient reuse, so self-adjusting computation instead records and propagates the relevant dependencies.

Basis: primary thesis + derived architectural interpretation.

For Anneal, a persistent worker, prepared proof environment, source handle, content hash, or cache key can identify *which saved state is being discussed*. Currentness is a separate proposition. If the saved state can have been affected by an unmodeled file, environment variable, plugin, imported artifact, mutable server state, or tool version, identity does not close the proof obligation.

### 2. Correctness depends on controlling the dependency boundary

The functional formulation makes changing data explicit through modifiable references and records the reads that create dependencies. Change propagation has rules for re-executing affected reads and discarding obsolete subtraces. The machinery is not merely a clever scheduler layered over arbitrary code; the programming model is shaped so that the runtime can know which changes matter.

This distinction becomes concrete in the factorial example discussed in the thesis and the 2006 TOPLAS paper. When an outer read is re-evaluated after an input change, a nested read that is no longer on the fresh control-flow path must be deleted rather than independently re-executed. Re-executing such stale work can produce a different result, raise an exception, or even diverge. The semantic rule is therefore not “rerun every node touched before.” It is “maintain a trace consistent with the computation that would exist for the new input.”

Basis: primary thesis + primary TOPLAS paper.

This matters to Anneal's cancellation and invalidation design. A dependency graph built for one source/model snapshot is not a bag of jobs that can all safely finish and publish after the snapshot changes. Some jobs may cease to exist in the fresh computation. The safe default for an opaque stage is not to let every old child finish and merge its artifacts; it is to prevent stale results from crossing the current acceptance boundary unless their correspondence to the new computation is re-established.

### 3. Supporting mutation required a stronger theorem, not an assertion that effects are harmless

Early self-adjusting work imposed restrictions that made the model close to purely functional computation. `Imperative Self-Adjusting Computation` extended the system to modifiables that can be written multiple times and to cyclic stores. Its stated consistency theorem is observational equivalence between change propagation and from-scratch execution in the SAIL language. The proof uses a step-indexed logical relation to handle cycles.

That result is evidence **against** a common overgeneralization. The move from pure/write-once state to richer mutation was a research contribution requiring a new semantics and proof. It was not obtained by saying “the incremental engine will notice side effects.” The theorem accounts for the particular mutable store operations represented by SAIL.

The 2013 JFP semantics tackles another complication: nondeterministic memoization choices combined with mutation during change propagation. Its consistency theorem says the nondeterministic reuse choices do not change the result for evaluations of the same program from the same state. Its correctness theorem relates self-adjusting behavior to ordinary functional meaning. The accompanying Twelf development machine-checks the metatheory.

Basis: primary technical-report abstract + JFP article/proof artifact.

The corresponding Anneal rule is conditional: an effect can participate in a fresh-equivalence claim only if it is either (a) included in the logical input/outcome relation, (b) controlled so that it cannot affect semantic results, or (c) covered by a stronger upstream contract that Anneal can rely on. An uninstrumented process reading ambient files does not inherit the SAIL theorem merely because Anneal launched it from an incremental scheduler.

### 4. “Same starting state” is doing real work

The JFP consistency statement quantifies over evaluations of the same program starting from the same state. That premise is easy to understate when borrowing the result as a systems slogan. In an orchestration setting, “state” expands into whatever the external computation can observe and whatever persistent state can influence its behavior.

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

This is not a demand to hash the universe. It is a statement about the proof obligation. Anneal may instead make the stage hermetic, conservatively restart it when the dependency boundary is uncertain, or obtain an upstream snapshot/dependency contract. What it cannot do is omit a semantically relevant input and then cite from-scratch consistency as support for reuse.

Basis: JFP theorem premise + Anneal design contract + derived systems application.

### 5. From-scratch consistency is orthogonal to update cost

Acar's work explicitly separates semantic correctness from efficiency. The 2005 thesis develops trace-stability analysis and reports large speedups for some applications, but also discusses cases where a change can force recomputation of most or all of a computation. The later parallel self-adjusting work likewise describes suitability and stability as workload/algorithm properties rather than guaranteed benefits of the framework.

A correct incremental engine can therefore be uselessly slow, and an extremely fast cache can be semantically wrong. These are separate claims:

1. **Correctness:** the reused result means what a fresh result would mean for the current logical input.
2. **Reuse effectiveness:** enough unaffected work survives that the mechanism saves material time or resources.
3. **Reuse overhead:** dependency tracking, retained state, invalidation, and memory do not cost more than the work saved.

Basis: primary thesis + SPAA 2021 paper + derived decomposition.

Anneal should preserve this separation in its design and measurements. A freshness/version protocol belongs to correctness. Whether to retain an Aeneas process, cache generated Lean, retain elaboration state, or share a prepared environment is a performance decision after the relevant freshness contract is known.

### 6. The strongest practical use for Anneal is as a differential oracle

Anneal can use the fresh path as an oracle even when it cannot prove a theorem about an external incremental implementation. For an operation whose outcomes can be normalized, test suites can compare:

1. a warm/reused path after a controlled sequence of edits or environment changes; and
2. a clean fresh execution from the final explicit input/world.

Disagreement falsifies the reuse contract for that case. Agreement increases confidence but does not prove complete dependency capture, especially when the test suite does not perturb hidden inputs.

This oracle is particularly useful around lifecycle changes that are easy to get subtly wrong: file deletion/recreation, config changes, dependency revisions, prepared-environment replacement, plugin changes, worker restart, and changes that remove earlier work from the fresh control-flow/dependency graph.

Basis: derived application of the literature's fresh-equivalence specification. This report does not claim an existing #3731 probe establishes the unrestricted property.

### 7. An opaque external stage has three defensible integration strategies

The literature suggests a decision framework rather than one mandatory mechanism.

**Conservative rerun.** Treat the external stage as one coarse node. Re-run it whenever any input that might matter changes. This gives up reuse inside the stage but minimizes the dependency-accounting surface. For an early Anneal architecture, this is the default competitor that finer incrementality must beat.

**Hermetic/captured execution.** Restrict or record ambient inputs strongly enough that a complete stage identity can be constructed. This may be viable for subprocess translation/checking if filesystem, environment, toolchain, and plugin access can be made explicit. The cost moves into sandboxing, manifests, capture, and revalidation.

**Upstream incremental contract.** Reuse a library/server API that already defines snapshots, dependency invalidation, and the semantics of reused state. This can support finer updates without Anneal reimplementing a DDG, but only if the upstream contract actually covers the state Anneal relies on. An API being persistent or query-oriented is not sufficient.

Basis: derived analysis from the theorem boundary and Anneal's “prefer general, minimally sufficient mechanisms” requirement.

A fourth option—retain opaque state and infer freshness from a handle, timestamp, or successful RPC—is not a distinct correctness strategy. It is an unproven assumption about hidden dependencies and should remain trust/partial-evidence rather than silently acquiring verification-success meaning.

### 8. Termination, cancellation, and failures need separate semantics

Fresh equivalence does not guarantee that a computation terminates quickly, or at all. The stale-read example is useful precisely because an invalid change-propagation rule can introduce divergence where the fresh path would not execute that code. But even a correct incremental semantics does not turn a diverging fresh computation into a terminating one.

Anneal therefore needs separate rules for cancellation and incomplete work. If the current source changes while a stage is running, it can be sound to let that stage finish for possible speculative reuse, or sound to cancel it for resource reasons, provided its result cannot be accepted as current without the appropriate correspondence check. Cancellation policy is a liveness/resource decision; the acceptance boundary is a correctness decision.

Likewise, “fresh execution failed” is an outcome, not absence of a value that can be replaced by an old success. A reused success is not from-scratch-consistent with a current fresh failure merely because the old proof object still checks in isolation. The input/model identity that made the old proof relevant has changed.

Basis: primary stale-trace example + Anneal success semantics + derived lifecycle analysis.

### 9. The serious competing account favors less incrementality, not a weaker correctness rule

The strongest alternative is that Anneal should avoid importing self-adjusting-computation machinery almost entirely. Charon, Aeneas, Lean, and Lake are evolving upstream systems with their own caches and state. Attempting to discover every ambient dependency or maintain an Anneal-level fine-grained trace may duplicate upstream work, increase retained memory, and create a second invalidation system whose bugs are hard to detect.

This report agrees with that criticism on mechanism. The fresh-equivalence relation survives it. Anneal can use a small scheduler with coarse stages, immutable source/model identities, and aggressive restart. The result may be less incremental but easier to justify. Only observed latency pressure plus a trustworthy finer-grained upstream contract should move the boundary inward.

This is why the literature should be used as a **specification vocabulary**, not as a framework-selection argument. The right lesson is “say what reuse must preserve, then choose the cheapest mechanism that can establish it,” not “build a DDG because self-adjusting computation proved DDGs correct.”

Basis: derived judgment, with Anneal's minimally-sufficient-mechanism constraint as authority.

### Conditional judgment for Anneal

Use fresh execution as the semantic reference for any reused computation that contributes to authoritative verification. Define the stage's logical input and observable outcome narrowly but completely enough to preserve Anneal's promise. When the dependency closure of an external tool is not established, invalidate conservatively at that tool boundary. Treat fine-grained tracking, persistent processes, and retained dependency traces as performance optimizations whose permission to publish results depends on a separate freshness contract.

Do **not** require byte-identical outputs, a universal global version counter, or a self-adjusting-computation runtime. Do require a checkable answer to: “Why would executing this operation from scratch against the current identified world not change the meaning of the result we are about to accept?”

Evidence that would change this judgment includes an upstream Aeneas/Lean interface with a documented, tested snapshot/dependency closure strong enough to make a finer unit authoritative; measured workloads showing coarse re-execution dominates interactive latency; or counterexamples showing that the proposed logical input/outcome relation misses semantically relevant state. Conversely, repeated warm/fresh disagreement caused by ambient dependencies would strengthen the case for coarser invalidation or hermetic execution.

## Boundaries

- **Not examined:** This report does not evaluate Salsa, Adapton, build-system frameworks, Nix/Bazel hermeticity, or Lean's particular incremental elaboration contracts. Neighboring #3732 questions cover those subjects.
- **Not examined:** No Anneal, Charon, Aeneas, Lean, or Lake execution was run for this literature review. Proposed warm-vs-fresh differential checks remain probes, not findings.
- **Known not to follow from the cited theorems:** Arbitrary external subprocesses do not obtain self-adjusting-computation correctness merely because an orchestrator caches or restarts them. The formal models represent specific state and operations.
- **Unknown:** This report does not establish the complete ambient dependency set of Anneal's current upstream toolchain or whether it can be made hermetic cheaply.
- **Unknown:** The cheapest useful granularity for Anneal reuse depends on latency/memory measurements and upstream contracts not established here.
- **Unsupported stronger conclusion:** Stable IDs, hashes, epochs, or worker handles identify artifacts/state but do not by themselves prove that hidden dependencies are unchanged.
- **Unsupported stronger conclusion:** A finite warm-vs-fresh test suite proves the unrestricted equivalence relation. It can falsify and increase confidence, not replace a theorem or complete dependency argument.
- **Unsupported stronger conclusion:** From-scratch consistency provides a liveness theorem, resource bound, source/model correspondence proof, or proof of upstream tool correctness.
- **Scope distinction:** Anneal implications are derived conditional analysis. `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` remain authoritative.

## Evidence

### Acar, *Self-Adjusting Computation*, CMU-CS-05-129 (2005)

Primary source: https://www.cs.cmu.edu/~rwh/students/acar.pdf

The thesis describes correctness as semantic equivalence between change propagation and from-scratch execution, develops dynamic and memoized dynamic dependence graphs, and keeps correctness separate from trace-stability/performance analysis. Chapter 5's discussion of memoization under side effects is especially relevant: reuse works because the dependency graph for the reused call is retained and change-propagated, not because the call's identity proves its result is unchanged. Chapter 11's obsolete-read example shows why trace maintenance follows the *fresh* control-flow meaning rather than blindly replaying old dependencies.

Basis: primary publication.

### Acar, Blelloch, Harper, *Adaptive Functional Programming*, TOPLAS 28(6) (2006)

DOI: 10.1145/1186632.1186634  
Primary author-hosted PDF: https://www.cs.cmu.edu/~rwh/papers/afp/toplas06.pdf

The paper formalizes an adaptive functional language, a modal type discipline for correct use of adaptivity, and DDG change propagation. Its stale-contained-read discussion explicitly identifies incorrect results, nontermination, and exceptions as consequences of retaining work that is inconsistent with fresh evaluation.

Basis: primary publication.

### Acar, Ahmed, Blume, *Imperative Self-Adjusting Computation*, POPL 2008

DOI: 10.1145/1328438.1328476  
Full technical report: University of Chicago TR-2007-18, published 2007-11-09: https://newtraell.cs.uchicago.edu/research/publications/techreports/TR-2007-18

The work removes an earlier write-once limitation, permits multiple writes and cyclic structures in SAIL, and proves observational equivalence between change propagation and from-scratch execution. The extension matters historically because richer effects required a richer model and proof.

Basis: primary technical report/publication metadata.

### Acar, Blume, Donham, *A Consistent Semantics of Self-Adjusting Computation*, JFP 23(3) (2013)

DOI: 10.1017/S0956796813000099  
Proof artifact landing page: https://www.cs.cmu.edu/~jdonham/aml-proof/

The article presents memoizing change propagation in the presence of nondeterministic memo choices and mutation. Its abstract distinguishes a consistency theorem—same program and starting state does not obtain different results merely because of nondeterministic reuse—from a correctness theorem connecting the self-adjusting semantics to ordinary functional meaning. The Twelf proof artifact is public.

Basis: primary journal publication + proof artifact.

### Anderson, Blelloch, Baweja, Acar, *Efficient Parallel Self-Adjusting Computation*, SPAA 2021

DOI: 10.1145/3409964.3461799  
Author-hosted PDF: https://www.cs.cmu.edu/~blelloch/papers/3409964.3461799.pdf

The later work continues to distinguish correctness machinery from the algorithm/workload property that determines how much update work is saved. It explicitly notes that not all algorithms are suitable for self-adjusting computation because a small input change may affect most of the computation.

Basis: primary publication.

### Anneal authority at `cc135f46155b72e4b51188525c2974a3b84acf92`

- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`
- `anneal/README.md`, blob `bf22d554437659f38d8918c1e7c3480f4f62b126`

The design contract requires precise identity/scope for successful verification, prevents missing evidence or failed tools from silently becoming success, requires source/model justification for Rust-level claims, preserves semantically relevant effects at abstraction boundaries, makes trust explicit, and prefers the simplest sufficient mechanism. It deliberately does not choose the execution/tool ownership boundaries that this report discusses.

Basis: authoritative project documentation for Anneal; the architecture recommendations above are derived from it, not adopted by it.

## Revalidation

For the literature claims, first check the cited editions rather than later summaries. The cheapest discriminating sources are the 2005 thesis sections defining from-scratch equivalence and stale-trace behavior, the TR-2007-18 abstract/theorem statement for the imperative extension, and the 2013 JFP abstract plus Twelf artifact for consistency under memoizing change propagation. A later paper using the phrase “from-scratch consistency” is not evidence that it has the same state/effect model.

For application to a newer Anneal design, diff `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` from `cc135f46155b72e4b51188525c2974a3b84acf92`. Reconsider the judgment if Anneal adopts an authoritative upstream snapshot/dependency contract, a hermetic stage model, or a distinct freshness policy for accepted results.

For a concrete reuse mechanism, the cheapest behavioral discriminator is a warm-versus-fresh matrix over changes that are likely to expose hidden dependencies: source edit/revert, file deletion and recreation, dependency/config changes, tool/plugin revisions, environment changes, prepared-environment replacement, and worker restart. Normalize only differences already argued irrelevant to verification-success meaning. A mismatch falsifies the proposed reuse relation for that case. A match is evidence, not a proof of complete dependency capture.