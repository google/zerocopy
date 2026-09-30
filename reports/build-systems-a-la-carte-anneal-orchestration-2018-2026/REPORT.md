# Build Systems à la Carte as a vocabulary for Anneal orchestration

## Summary

*Build Systems à la Carte* is most useful to Anneal as a vocabulary for separating decisions that are easy to conflate, not as an argument to adopt Shake, Bazel, Nix, or another build-system framework. The 2018 paper and its expanded 2020 treatment separate at least four questions that matter independently: what a task may depend on, how tasks are scheduled, how the system decides whether a value must be rebuilt, and what persistent information it retains to support that decision. The 2020 paper then makes explicit where the clean model stops: real tasks can depend on untracked state, behave nondeterministically, fail, mutate shared state, and incur resource costs that the abstract scheduler does not remove.

For Anneal, that decomposition points to a deliberately modest baseline. At the orchestration layer, the large pipeline edges are already mostly known: a Rust compilation subject feeds extraction/model production, which feeds translation/generated Lean, which feeds Lean/Lake elaboration and proof checking. A small topological DAG scheduler can order those coarse stages, run independent subjects in parallel, deduplicate identical in-flight work, propagate cancellation, and associate work with a captured generation. It does not need to reproduce Cargo's, Lake's, or Lean's internal dependency engines. Where Anneal can compute a complete identity for a stage's semantic inputs, a verifying-trace-like record can also support coarse reuse or early cutoff. Where it cannot, always rebuilding that stage or delegating reuse to the upstream tool is safer than pretending an incomplete key is a cache key.

Dynamic scheduling is valuable only for dependencies visible to the scheduler. Wrapping an opaque compiler, translator, or prover process in a Shake-like suspending scheduler does not reveal files, environment variables, plugin state, loaded imports, working-directory assumptions, daemon caches, or other state that the process never reports through Anneal's dependency interface. Those inputs must instead be made explicit, constrained by isolation/reset, delegated to an upstream system whose result Anneal can identify, or conservatively treated as volatile. This is the largest limit on transferring the paper's pure task model directly to Anneal.

Interactive buffers create the same problem in a more obvious form. An open LSP document is a distinct value from the file currently on disk. A correct orchestration model therefore needs to name the buffer snapshot or document version that a job consumed instead of treating a pathname as the value. Similarly, a persistent compiler or Lean worker is an execution resource, not the authority for what source/model/environment is current. Process reuse can be an optimization over an explicit request identity; it should not become an implicit source of semantic identity.

Finally, build-system correctness and Anneal verification success are different properties. In the paper, a build is correct relative to its declared task/store semantics when the target and dependencies are up to date. Anneal must additionally establish that the accepted result belongs to the intended Rust/model/environment snapshot, that required obligations were actually checked, and that late or stale work cannot acquire publication authority. Generation, request-echo, completeness, trust, and final publication fences therefore sit outside the scheduler/rebuilder decomposition even when the scheduler is otherwise correct.

The conditional judgment is: **start with coarse explicit DAG orchestration and strong result identity; let richer incremental machinery earn its complexity.** Add dynamic dependency tracking only if Anneal itself needs to discover dependencies during execution. Add constructive/content-addressed caching only where task identity and determinism are strong enough to make reuse sound. Add fine-grained self-adjusting or query infrastructure only after representative measurements show that coarse recomputation or upstream-native reuse is the limiting cost. This report does not adopt that design for Anneal; it states the design consequence supported by the examined literature and current Anneal evidence.

## Applicability

This report directly examines the 2018 ICFP paper *Build Systems à la Carte* (DOI `10.1145/3236774`), the substantially expanded 2020 JFP paper *Build systems à la carte: Theory and practice* (DOI `10.1017/S0956796820000088`), and the maintained executable framework at `snowleopard/build@43b18b9a362d7d27b64679ea4122e4b8c5dfedd9`. The source revision contains both the ICFP and JFP paper source as well as the executable scheduler, rebuilder, store, trace, and system models.

The 2020 paper is not merely a republished copy. Its introduction identifies the main changes from 2018: expanded task/scheduler/rebuilder explanations; new material on step traces; an entirely new experience section; and mostly new treatment of failures, polymorphism, and file watching, with revised treatment of nondeterminism. This report therefore uses the 2018 paper to establish the original decomposition and the 2020 paper as the strongest primary account of the practical limits and costs of that decomposition.

The Anneal side is bounded by `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, whose `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` were unchanged from the pinned revision when reread on 2026-09-30. Those documents require precise verification identity and scope, fail-closed acceptance, explicit and shrinkable trust, and minimally sufficient mechanisms while deliberately leaving component boundaries, the atomic verification subject, build matrices, generated artifacts, and source/model correspondence mechanisms undecided.

The report also uses four current `reference` packages as bounded Anneal evidence at `refs/heads/reference` commit `87bbe2425ed749ba4eff9e729ad6799313124cb2`: `anneal-interactive-pipeline-invalidation-graph-main-41f5b37`, `anneal-3730-rust-input-snapshot-2026-09-29`, `anneal-3730-architecture-contracts-2026-09-29`, and `anneal-3730-fault-model-2026-09-29`. They establish concrete counterexamples and orchestration constraints for the currently examined Anneal stack; they do not turn this literature analysis into an adopted product architecture.

No build-system implementation, Anneal pipeline, compiler, language server, or proof backend was executed for this report. The Build Systems à la Carte mechanisms come from the published papers and exact source. Anneal implications are derived by comparing those mechanisms with current Anneal design authority and the bounded execution/source reports already in the reference corpus.

## Findings

### The paper separates choices that framework selection tends to collapse

The central contribution is a decomposition. A build system takes a task description, a target key, and a store, then updates the store so that the target is current. The task description says how to compute a value by fetching dependencies. Persistent build information gives the system memory across builds. The 2018 and 2020 papers then separate two implementation choices that are often entangled in real systems:

1. **Scheduler:** in what order should tasks be executed so dependencies are ready when needed?
2. **Rebuilder:** once a task is eligible to run, how does the system decide whether its current value can be kept, restored from cache, or must be recomputed?

The task language adds an earlier distinction. Applicative tasks expose their dependency structure independently of dependency values, so a scheduler can know the graph before executing tasks. Monadic tasks may choose later dependencies from earlier dependency values, so the graph can be discovered only while the task runs. The store and retained build information add another axis: the system may remember dirty bits, verifying traces, constructive traces, previous order, cached values, or other summaries.

The maintained source makes the orthogonality concrete. `src/Build/System.hs` composes scheduler and rebuilder functions: Make is modeled as a topological scheduler plus modification-time rebuilding; Ninja as topological plus verifying traces; Excel as restarting plus dirty bits; Shake as suspending plus verifying traces; the paper's Bazel model as restarting plus constructive traces; and its Nix model as suspending plus deep constructive traces. These are executable models of design points, not claims that current production versions of those systems remain byte-for-byte implementations of the model.

**Basis:** primary publications + exact source. `papers/jfp/1-intro.tex`, `papers/jfp/3-abstractions.tex`, and `src/Build/System.hs` at `snowleopard/build@43b18b9a362d7d27b64679ea4122e4b8c5dfedd9`.

For Anneal, the useful transfer is therefore a question set, not a brand name:

| Dimension | Build-systems vocabulary | Anneal question |
| --- | --- | --- |
| Dependency expression | static/applicative, dynamic/monadic, or outside the model | Can Anneal enumerate the semantic inputs to this stage before execution, learn them through an explicit dependency callback, or only observe an opaque tool boundary? |
| Scheduling | topological, restarting, suspending, or delegated | Does Anneal need to order coarse stages itself, or should an upstream tool own the internal graph? |
| Rebuilding | always rebuild, dirty/approximate, verifying trace, constructive trace, deep constructive trace | What evidence is sufficient to reuse a previous stage result? |
| Persistence | no memory, current trace, historical traces, content cache | Which retained state has enough identity to be evidence rather than merely an optimization hint? |
| Effects | pure declared task vs untracked/nondeterministic/volatile behavior | Which environment, daemon, filesystem, plugin, clock, randomness, or external-state effects must be explicit or isolated? |
| Acceptance authority | not the paper's scheduler/rebuilder problem | What proves that a completed result belongs to the current verification request and may become user-visible/current? |

The final row is intentionally outside the original decomposition. Treating it as just another rebuild policy would obscure Anneal's fail-closed verification semantics.

### A topological scheduler buys useful structure before Anneal buys a build system

The paper's topological scheduler is deliberately simple: compute the dependency graph, topologically order it, then execute tasks in that order. Its main advantages are simplicity and the ability to detect cycles or missing dependencies before work starts. Its main restriction is equally clear: it requires task dependencies in advance, so it cannot directly schedule genuinely dynamic monadic dependencies.

At Anneal's orchestration layer, that restriction is less severe than it first appears. The current reference evidence already identifies a conservative sequence of coarse semantic handoffs: a Rust/Cargo compilation subject produces a complete Charon/LLBC generation; Aeneas consumes that generation to produce generated Lean; Lake/Lean then consume a prepared source/import environment; open LSP document text forms a separate live-state path. The exact future product boundaries remain undecided, but these large edges are not hidden from the host in the same way that an individual compiler's internal query graph is hidden.

A small DAG scheduler over such coarse nodes can therefore provide several properties without adopting a general-purpose incremental framework:

- dependency-respecting execution of coarse stages;
- parallel execution of independent subjects or branches;
- one in-flight computation per exact stage request when sharing is safe;
- cancellation routing and subscriber ownership;
- explicit stage status and error propagation;
- generation labels that keep outputs from different requests distinct; and
- a place to apply a final current-generation check before results are exposed.

None of these requires the scheduler to understand rustc queries, Cargo units, Aeneas internal passes, Lake module traces, or Lean command snapshots. Those systems can remain nested engines that receive one explicit Anneal request and return one identified result.

This is a **derived** judgment, not a claim that current Anneal implements the DAG. The current `anneal-interactive-pipeline-invalidation-graph-main-41f5b37` report explicitly says the examined V2 source did not yet implement the full interactive pipeline. The judgment is that the known *coarse* edges are sufficient to justify starting with ordinary orchestration when an implementation is built.

### Dynamic scheduling helps only when the dependency channel is real

The paper offers two approaches when dependencies are learned during task execution. A restarting scheduler begins work, aborts if it discovers an out-of-date dependency, builds that dependency, and later retries the original task. A suspending scheduler pauses the task, computes the newly requested dependency, and resumes the suspended computation. The suspending scheduler can avoid repeated work, but the 2020 paper is explicit about its engineering cost: real suspension needs threads/processes or continuations, and its theoretical optimality pays only when avoided duplicate work is more expensive than suspension machinery.

That tradeoff matters to Anneal, but there is a more basic applicability test: **can the task actually tell Anneal which dependency it is fetching?** In the paper, dynamic discovery works because the task calls the scheduler-provided `fetch`. An opaque `charon`, `aeneas`, `lake`, `lean`, `rustc`, or plugin execution does not become dependency-transparent merely because Anneal runs it from a dynamic build framework. If it reads an environment variable, follows a config file, loads a native plugin, consults process-global state, or reaches another file through an internal compiler graph without reporting that access through Anneal's dependency interface, a Shake-style outer scheduler does not learn the dependency.

Anneal therefore has four materially different strategies for such inputs:

1. **Make the input explicit.** Put its identity in the stage request and therefore in the stage's reuse key.
2. **Delegate dependency ownership.** Let Cargo, Lake, or another upstream system decide its own internal freshness, then identify the resulting upstream artifact or generation at the Anneal boundary.
3. **Constrain the execution environment.** Use a fresh/reset process, controlled environment, sandbox, or other boundary that makes otherwise ambient state unable to change the result outside the declared request.
4. **Treat the stage as volatile.** Recompute rather than reusing when the dependency closure is unknown.

The 2020 paper itself supplies the conceptual precedent for the last choice. It models untracked dependencies as a form of impurity and notes that a task with unknown dependencies can be made volatile, sacrificing minimality to preserve correctness. Its `RealWorld` device is an explanatory model, not a recommendation that Anneal literally create such a key.

**Basis:** primary paper/source for scheduler mechanics and impurity; **derived** transfer to Anneal's opaque upstream tools.

### Rebuilder choice is an evidence choice

The rebuilder taxonomy is directly useful because each strategy answers a different evidentiary question.

A dirty-bit scheme says some external mechanism tells us what changed. It can be compact, but correctness depends on dirty propagation being conservative. The paper's examples show how this can compromise early cutoff or require over-approximation. For Anneal, a file watcher or “this path changed” event is therefore useful scheduling information but weak verification evidence. Missed events, generated inputs, feature/config changes, or same-path replacement can invalidate the result without a trustworthy dirty bit.

A verifying trace records the dependency identities or hashes used to produce a value and later checks whether they still match. This is a closer fit for a coarse Anneal stage whose semantic inputs can be enumerated. The trace need not prove the compiler or prover correct; it only supports the narrower claim that a previous output was produced from the same declared inputs. Existing Anneal evidence already shows why a single source pathname or source-file hash is too small a trace: a Cargo compilation subject can change through included files, features, manifests, procedural macros, build-script effects, or related inputs while one `.rs` file remains unchanged.

A constructive trace additionally stores the produced value, so another build can restore it instead of recomputing it. This is the conceptual basis for content-addressed or remote result caches. It buys more reuse but also raises the cost of a wrong key: stale or context-mismatched output can be reintroduced without rerunning the task that might otherwise expose the mismatch.

Deep constructive traces go further by indexing through terminal inputs and skipping intermediate materialization. The paper requires deterministic tasks for this optimization and gives a concrete “Frankenbuild” failure when nondeterministic intermediate results are mixed under a deep cache. It also loses ordinary early cutoff because intermediate values no longer participate in validation.

For Anneal, this yields a conservative progression:

- **always rebuild** when stage inputs/effects are not yet understood;
- **verify a previous result** once a complete enough input/environment identity exists;
- **restore cached results** only when output identity, tool/model/environment identity, and determinism/equivalence assumptions justify it; and
- **skip intermediate semantics through deep caches** only after those stronger assumptions are demonstrated for the actual stage.

This progression is about the strength of reuse evidence, not about adopting the paper's exact data structures. A generation tuple, artifact digest, upstream trace, or task-specific witness may encode the same evidence more appropriately than a generic `Trace` object.

### Persistent state has a retention cost and an invalidation-debugging cost

The paper does not treat “more history” as automatically better. A verifying-trace implementation may keep only one trace per key, bounding memory by the number of keys but missing reuse when a task's dependencies change A→B→A. A historical trace set can recover more prior states at the cost of larger storage and lookup. Constructive traces retain complete outputs or content-addressed references and therefore have still larger persistence and eviction concerns.

The same tradeoff applies to Anneal. A coarse scheduler can retain only the current successful generation and recompute after relevant change. It can retain per-stage input/output digests to gain coarse early cutoff. It can retain several generations for edit/revert workflows. Or it can retain a large cross-session cache. Each step can save work, but each also increases the surface for stale-key bugs, version migration, garbage collection, storage pressure, and “why did this result reuse?” debugging.

There is no evidence in the examined Anneal corpus that the richer end of this spectrum is currently the limiting requirement. The architecture-contract report treats process reuse, narrow dependency invalidation, shared brokers, historical snapshots, and remote execution as mechanisms that need measured wins and additional invariant gates. That evidence is compatible with the à-la-carte lesson: choose persistence separately from scheduling and add it where the measured workload earns it.

**Basis:** primary trace design + current Anneal architecture-gate report; **derived** cost judgment. No representative end-to-end Anneal retention benchmark was run here.

### Interactive buffers must be values, not ambient paths

The Build Systems à la Carte store maps keys to values. A software-build example often uses pathname→file-contents, but the abstraction does not require a path to be the value. That distinction is important for an interactive Anneal host.

The current invalidation report establishes that an open Lean LSP document is client-owned text. Rewriting the corresponding file on disk does not update the already-open document that the Lean worker is elaborating. A pathname is therefore only a locator. At minimum, the semantic input is the actual document text plus the version/generation under which the worker accepted it, along with the prepared import/environment identity relevant to that document.

A coarse Anneal task can model this cleanly: the stage request captures an immutable buffer snapshot (or digest plus exact retained bytes) and passes that value to the worker. A later edit creates a new request/generation. The scheduler may cancel the old job for latency, but even if cancellation loses the race, the old result remains tied to the old input key and cannot become current under a newer generation.

This is one place where the paper's abstract store is more useful than the common “build system equals files on disk” intuition. The correct mapping for a live tool need not be `path -> bytes`; it can be `document-generation -> bytes`, `prepared-environment-id -> environment`, or another key/value pair that reflects the actual semantic subject.

**Basis:** primary build-store abstraction + current Anneal/Lean invalidation evidence; **derived** host modeling judgment.

### Opaque compiler and server state is outside the pure-task theorem until represented or controlled

The paper's clean task model treats a task as a function: the same declared inputs produce the same output. Section 8 of the 2020 paper then names the real-world exceptions. A C compilation may depend on an unrecorded compiler version. Tasks may produce nondeterministic but semantically acceptable outputs. Volatile rules intentionally change on every build. Sandboxing can catch or exclude many undeclared effects, but the authors explicitly reject the idea that it necessarily captures every dependency down to CPU model or microcode.

Anneal has additional forms of potentially hidden state because several candidate architectures use long-lived language/compiler processes. Relevant state can include:

- executable/toolchain and linked native-library identity;
- current working directory, environment variables, search paths, and plugin configuration;
- Cargo feature/target/build-script state;
- loaded Lean imports and prepared Lake workspace;
- open document text and LSP document version;
- compiler/prover caches whose reset contract is not part of the request;
- server, worker, or RPC incarnation; and
- externally mutable files or generated trees consulted by a subprocess.

A build scheduler cannot declare those dependencies away. If correctness depends on one of them, either the request must identify it, the upstream boundary must attest the state relevant to its result, or the execution must be reset/isolated enough that omitted state cannot change accepted meaning. Otherwise the task is not pure with respect to the key Anneal is using.

This is also why persistent workers and caching are orthogonal. Keeping a worker alive may improve latency while every request still carries a complete semantic identity and every response echoes that identity. Conversely, a fresh subprocess may still be semantically under-specified if it inherits uncontrolled environment or filesystem state. Process lifetime is one mechanism for limiting hidden state; it is not the identity model itself.

**Basis:** primary 2020 engineering discussion + current Anneal architecture/fault evidence; **derived** trust-boundary analysis.

### Upstream build systems should keep the dependency graphs they understand better

The à-la-carte decomposition does not imply that one scheduler must own the entire transitive system. Anneal already sits above tools that have richer native incremental semantics than an outer orchestration layer could cheaply reproduce.

Cargo/rustc determine compilation units and compiler inputs. Lake owns module-artifact traces and can rebuild or restore Lean artifacts using its own selected toolchain rules. Lean's server owns command/document snapshots and dependency invalidation inside a prepared workspace. The current Charon/Aeneas evidence, by contrast, does not establish a supported cross-run delta protocol that Anneal can consume as an authoritative incremental interface; the conservative current boundary is a complete LLBC generation followed by a complete translated generation.

A small Anneal DAG can therefore compose **coarse values produced by nested incremental systems**. “Run Lake for prepared generated tree G” can be one outer task even if Lake internally performs hundreds of fine-grained freshness decisions. Anneal needs enough identity to know which G and which prepared environment that Lake invocation represented; it does not need to duplicate Lake's trace format. The same principle applies to Cargo and other upstream engines.

The competing approach is to flatten all internal dependencies into one universal Anneal graph. That could in principle improve cross-tool scheduling or caching, but it creates a large compatibility obligation: Anneal must faithfully reproduce each upstream tool's dependency semantics and update that reproduction as upstream behavior changes. Nothing in the papers establishes that such unification is necessary for correctness, and the current Anneal principle to prefer minimally sufficient mechanisms weighs against it without measured benefit.

**Basis:** current reference source/execution reports + Anneal design principle; **derived** orchestration boundary judgment.

### Build correctness does not authorize a verification result

The paper defines correctness relative to its task/store model: after a build, the target and its dependencies should be up to date according to the task description and final store. That is a useful orchestration specification. It is not Anneal's verification theorem.

An Anneal result has a stronger interpretation. Current `anneal/DESIGN.md` requires enough identity and scope to say which program/behavior was verified, which promises were established, and which trusted code/assumptions support them. Missing evidence or a failed tool cannot become success merely because the orchestration pipeline continued.

A separate current fault-model report makes the temporal consequence concrete. Its model requires current revision/digest, stage generation, worker/RPC incarnation, ownership/status, completeness, request echo, and a final selection condition before a result may publish. Removing each modeled fence produces a bounded counterexample, and one gated subprocess replay shows a newer result publishing while an older job completes later and is rejected. These are bounded model/fake-backend observations, but they demonstrate a category the build-system paper does not address: a task can finish successfully for an old request after the user's current request has changed.

The host therefore needs a final authority transition distinct from rebuilding. A useful terminology is:

- **scheduler:** may this task run now?
- **rebuilder/cache:** may this previous value be reused for this task identity?
- **verification acceptance:** does this completed output satisfy the requested evidence contract?
- **publication fence:** is that accepted result still current and authorized to replace the user-visible/current result?

Conflating the last two with a build cache would make stale-result races look like ordinary cache hits.

### The smallest useful Anneal design maps cleanly into the paper's dimensions

A first implementation can use the paper's vocabulary without importing its abstractions literally:

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

The baseline is not “rebuild everything forever.” It leaves obvious upgrade points. Verifying traces can be added per coarse node. A content-addressed cache can be added for stages that meet the stronger assumptions. A dynamic scheduler can be introduced where Anneal truly owns a dynamic dependency relation. A compiler-backed service can replace a one-shot stage while preserving the same explicit request/result contract.

The important sequencing is that these optimizations should depend on proven stage semantics rather than define those semantics after the fact.

### Serious alternatives remain live

**Always rebuild every coarse stage.** This is the simplest correctness baseline when task identity is weak. It may be too slow for interactive use, but no literature argument alone establishes that it is too slow for the actual Anneal workload. Existing upstream incremental behavior may also make an apparently coarse invocation cheaper than full recomputation.

**Use a Shake-like dynamic suspending scheduler from the beginning.** This is attractive if Anneal's own tasks genuinely discover dependencies through an explicit callback. It is much less useful if most expensive work is inside opaque subprocesses whose hidden dependencies never cross the callback. The 2020 paper also warns that suspension machinery has its own cost.

**Use Bazel-like constructive traces or a remote content-addressed cache.** This can eliminate expensive repeated work and enable sharing across machines. It requires stronger cache-key and determinism/equivalence reasoning. The deep-trace Frankenbuild example is a direct warning against assuming terminal-input identity suffices under nondeterminism.

**Adopt fine-grained self-adjusting/query infrastructure.** Such a system could reduce recomputation below coarse stage granularity, especially if upstreams expose stable sub-results. It also requires a durable identity/dependency model, retained query state, invalidation debugging, and compatibility with opaque upstream boundaries. Those tradeoffs are the direct subject of #3732 J035–J037 and are not resolved by J034.

**Push more state into compiler-backed services.** A persistent upstream API may expose incremental state more faithfully than an outer generic build engine. That can be the right answer when the compiler owns semantic structure that cannot be reconstructed externally. It remains orthogonal to Anneal's need to state which source/model/environment generation a service response belongs to.

**Flatten all tools into one global dependency graph.** This maximizes theoretical scheduling visibility but gives Anneal ownership of dependency semantics that currently belong to several upstream tools. It is the strongest integration burden and has no demonstrated necessity in the evidence examined here.

### Conditional judgment for Anneal

The evidence supports the following design rule:

> Use Build Systems à la Carte to classify Anneal's orchestration choices, not to choose an implementation framework. Keep the host's first graph coarse and explicit. Delegate internal build graphs to the tools that own them. Reuse a result only under an identity that covers the effects relevant to that result, and keep verification acceptance/publication authority separate from build freshness.

This rule has two practical consequences.

First, a small DAG scheduler is not a temporary embarrassment to be replaced automatically by a “real” incremental engine. If Anneal's host-owned dependencies are mostly static and coarse, a topological scheduler is the mechanism that matches the problem. The paper treats the topological scheduler as simple because the dependency information is available early, not because it is inherently less sophisticated or less correct.

Second, more advanced machinery should be adopted one dimension at a time. Dynamic scheduling addresses runtime dependency discovery. Verifying traces address skip decisions. Constructive traces address result restoration. Process pools address startup/runtime cost. Fine-grained queries address granularity. None of those mechanisms substitutes for missing input closure, source/model correspondence, proof-acceptance semantics, or stale-publication fencing.

That conditional judgment is consistent with Anneal's current requirement to prefer minimally sufficient mechanisms and with the reference corpus's existing architecture gates. It is not an adopted Anneal architecture decision.

## Boundaries

- **No Anneal scheduler implementation was examined as a completed product.** Current V2 evidence says the full batch/live orchestration path is not yet implemented at the older examined stack revision. The report maps design choices; it does not claim current code already follows them.
- **No representative Anneal performance measurement was run.** The report cannot say when coarse rebuilding becomes too slow, whether persistent workers dominate latency, or whether dynamic scheduling saves enough work to justify its complexity.
- **The Build Systems à la Carte models abstract from real-system details.** The papers intentionally model the essence of systems such as Make, Shake, Bazel, Buck, Nix, Excel, and others. They are not current conformance specifications for those projects in 2026.
- **The paper's correctness theorem is relative to its task semantics.** It does not prove that an external compiler invocation's actual semantic inputs are complete, that a proof translation corresponds soundly to Rust, or that an Anneal verification result satisfies the product's TCB promise.
- **A fresh process is not complete hermeticity.** It can still inherit environment, filesystem, toolchain, plugin, network, device, locale, clock, or other state. Freshness/reset is one containment strategy, not a substitute for input analysis.
- **A verifying trace is only as complete as its dependency identity.** Hashing the dependencies Anneal happened to record does not protect against an omitted dependency.
- **Constructive caching is not rejected.** The report says it needs stronger task identity/determinism/equivalence evidence than simple recomputation. It does not claim those properties are impossible for Charon, Aeneas, Lake, Lean, or future Anneal stages.
- **Dynamic scheduling is not rejected.** It is warranted where the host truly owns a dynamic dependency relation. This report only rejects treating an opaque subprocess as dependency-transparent without an actual observation/interface mechanism.
- **No complete minimum Anneal identity tuple is established here.** Existing reference work names important dimensions, but exact atomic verification subject, build-matrix treatment, generated-artifact handling, and component boundaries remain deliberate Anneal non-decisions.
- **J035–J037 remain separate.** This report does not establish from-scratch consistency for self-adjusting computation, analyze Adapton naming semantics in depth, or evaluate Salsa/rustc-style fine-grained query systems. It provides the build-system vocabulary against which those later mechanisms can be compared.
- **Publication fencing is derived from Anneal-specific evidence, not from the build-system papers.** The paper does not claim that its scheduler/rebuilder abstraction solves stale interactive-result authority.

## Evidence

### Primary publications

- Andrey Mokhov, Neil Mitchell, Simon Peyton Jones, **“Build Systems à la Carte”**, *Proceedings of the ACM on Programming Languages* 2, ICFP, Article 79, 2018. DOI `10.1145/3236774`. This is the original publication establishing the task/build abstractions and scheduler/rebuilder decomposition.
- Andrey Mokhov, Neil Mitchell, Simon Peyton Jones, **“Build systems à la carte: Theory and practice”**, *Journal of Functional Programming* 30:e11, 2020. DOI `10.1017/S0956796820000088`. The paper identifies itself as an extended version of the 2018 conference paper and enumerates the added practical material.

### Exact executable/source revision

`snowleopard/build@43b18b9a362d7d27b64679ea4122e4b8c5dfedd9` was inspected on 2026-09-30. Relevant files and Git blob identities:

- `papers/jfp/1-intro.tex` — `6f38ee9da5913e526367084c2a32e327e9d683f0`: contribution list and 2018→2020 change summary.
- `papers/jfp/3-abstractions.tex` — `c2f6b35e642e410c15c28fb7b641b9d13285d5e3`: store/key/value/task/build vocabulary and task constraints.
- `papers/jfp/4-schedulers.tex` — `6e78793e8035fc21d1e3b237dea37f4ee5e8398c`: topological, restarting, and suspending schedulers; suspension/restart tradeoff.
- `papers/jfp/5-rebuilders.tex` — `e08d004c04f3114b9213f509861cb4a824edc89a`: dirty bits, verifying traces, constructive traces, deep constructive traces, early cutoff, determinism constraints.
- `papers/jfp/7-experience.tex` — `cb07bc7992dc84fe91ccafc11f9d1292d2d1b0b1`: practical experience using the abstractions.
- `papers/jfp/8-engineering.tex` — `d4da065f2c762ad7046ac85df0aef3f744fb5ed5`: failures, parallelism, impurity/untracked dependencies, nondeterminism, volatility, cloud concerns, and other engineering limits.
- `papers/jfp/10-conclusions.tex` — `4da36d2b2df586d336a34555487193238c056e9b`: final statement that build-system properties arise from scheduler/rebuilder composition.
- `src/Build/System.hs` — `dad42cd5b94e0bc51af79987b586e4c1885982c1`: executable composition of scheduler/rebuilder models.
- `src/Build/Scheduler.hs` — `57fc2578aef538e065e361223206439bec883851`: executable topological/restarting/suspending models.
- `src/Build/Rebuilder.hs` — `45233a9fb46ef7e3b7956cd61d2c7a8ce3ca5f15`: executable rebuilder/trace models.
- `README.md` — `ac3242ba441be71effbd935edd8041f01c651bd6`: project description and publication relationship.

The maintained source revision is implementation/source corroboration. Historical publication claims are anchored to the DOI publications rather than backdated from the current repository state.

### Anneal design authority

`google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, reread 2026-09-30:

- `anneal/PRINCIPLES.md` — blob `d5339a95254eae14ac201139d07d9d36d48a19fb`.
- `anneal/DESIGN.md` — blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`.

These files establish the fail-closed TCB promise, precise identity/scope, explicit trust, minimally sufficient mechanisms, and the remaining architecture non-decisions used in this report's Anneal applicability analysis.

### Current reference evidence used for the transfer

At `google/zerocopy` `refs/heads/reference` commit `87bbe2425ed749ba4eff9e729ad6799313124cb2` on 2026-09-30:

- `reports/anneal-interactive-pipeline-invalidation-graph-main-41f5b37/REPORT.md` — blob `9695ae7ab3626273431f6715ee2b0c846e064496`: coarse cross-tool invalidation graph; Charon/Aeneas whole-generation conservative boundaries; open-document versus filesystem distinction; Lake/Lean ownership of downstream freshness.
- `reports/anneal-3730-rust-input-snapshot-2026-09-29/REPORT.md` — blob `8d1ca9ff320e216be72abbca267c4372fcb8d0e1`: execution evidence that a Rust source path/file hash is not a complete Cargo compilation identity.
- `reports/anneal-3730-architecture-contracts-2026-09-29/REPORT.md` — blob `d532b9fe321f547efe355a9044b707a06727ed65`: fresh fully specified request + fenced complete result as a viable baseline; process reuse and richer mechanisms require measured/invariant gates.
- `reports/anneal-3730-fault-model-2026-09-29/REPORT.md` — blob `b11f3bab8082ebe52ca47a2d10eb9f44d6f0832c`: bounded model and fake-backend evidence for generation/ownership/completeness/publication fences.

Those reports are evidence about their exact examined subjects. This report does not widen their direct execution results; it uses them to test which build-system abstractions transfer to Anneal and which do not.

## Revalidation

For the literature decomposition, the cheapest revalidation is to compare a future revision of the two publications or maintained source against the exact sections and blobs listed above. In particular, check whether the project still separates scheduler and rebuilder, whether topological/restarting/suspending semantics have materially changed, and whether the impurity/determinism limitations remain. A future production Bazel, Nix, Shake, or other system does not need to match these models for the paper's vocabulary to remain useful; if this report makes a claim about a production system, revalidate that claim against the production project's own current source/documentation instead of the model.

For Anneal, reread current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`, then inspect the current orchestration implementation and reference corpus for four discriminating changes:

1. **Dependency exposure:** does Anneal now have an explicit API that reveals stage-level dynamic dependencies which were previously opaque?
2. **Incremental upstream contract:** do Charon, Aeneas, Lake, Lean, or another selected component now expose a supported cross-request incremental result with stable identity and reset/invalidation semantics?
3. **Measured bottleneck:** do representative edit/build/proof traces show that coarse recomputation or upstream-native scheduling is the dominant latency/resource cost?
4. **Reuse evidence:** is there now a complete enough source/model/environment/tool identity, plus determinism/equivalence evidence, to justify constructive or remote cache reuse for the stage in question?

If (1) becomes true, reevaluate a dynamic Anneal-owned scheduler. If (2) becomes true, prefer composing the upstream incremental contract before recreating it externally. If (3) becomes true without (1) or (2), benchmark the smallest richer mechanism against the coarse DAG baseline. If (4) becomes true, add cache restoration only for the proven scope and compare against fresh execution.

Separately rerun the current stale-result/publication tests whenever acceptance authority changes. A scheduler or cache refactor is not a substitute for proving that late work, old buffers, old worker incarnations, or incomplete generations cannot become current verification success.