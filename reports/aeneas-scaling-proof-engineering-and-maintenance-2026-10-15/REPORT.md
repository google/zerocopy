# Aeneas scaling, proof engineering and maintenance boundaries

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Scaling an Aeneas verification effort involves several independent costs: Rust/Charon extraction, symbolic translation, target generation, Lean elaboration/kernel checking, proof construction and maintenance of specifications/models. The inspected source already provides function-level parallel translation, per-function timing diagnostics, separate generation/verification stages and handwritten proof dependencies. Those mechanisms do not establish end-to-end throughput, fine-grained semantic incrementalization, or unrestricted concurrent reuse of the library.

Industrial and smaller pipeline reports demonstrate substantial verification work with different tools and assumptions. Their workload-specific code/proof counts and agent measurements must remain attached to the original experiment. The current source and retained older component probes support concrete workflow findings; neither industrial success nor matching generated artifacts proves that the production translator preserves Rust semantics.

## Applicability

This package answers G12 / A33: scaling, proof engineering and maintenance. It reads Aeneas `21345f80fa212c596f6437378d7d57984fa2ea77`, the exact SymCrypt draft `arXiv:2609.15648v1`, the pipeline experience report `arXiv:2605.30106v1`, and selected retained corpus reports at clean corpus revision `fa65b241fd0cb2c791c841eace86d43d724359bc`. [evidence.json](evidence.json) records exact source paths, blob IDs, narrow excerpts, paper locations and prior execution identities.

The coordinating Charon revision `9e95cf318e3a2964fcf5e03104cde5b718f98ea5` is distinct from the source-declared `charon-pin`, `1aebab5f03a58067e5dc0ede2fec584117f54964`. No compatible binary bundle was built or exercised. The backend Lean toolchain file names `v4.35.0-rc4`. Older retained execution used Aeneas `ac9f1bc5262a5e4ff1e24ca78617121382202727` / nightly-2026.06.03, Charon 0.1.210 and Lean 4.30.0-rc2 where stated below.

Basis: **source** for current program/build/configuration facts; **documentation** for paper claims and prior-report descriptions; **derived** for cost decomposition and implications. Prior execution is explicitly attributed to the retained reports. No new upstream execution, build, installation, benchmark, proof replay or downstream build occurred here.

Current Result is an interaction tree over RustEffect; the current WP layer uses DWP/DWLP. This report does not use historical inductive Result reduction facts, re-audit the entire trusted base, or duplicate the separate WP/literature reports.

## Findings

### A33 evidence from the two papers is substantial but workload-specific

The following two paragraphs are the bounded paper-derived factual summaries. Subsequent workflow findings are based on current source or separately identified retained execution, and the cost framework is this report's derivation.

The [SymCrypt draft, arXiv:2609.15648v1](https://arxiv.org/html/2609.15648v1), reports 16.7KLOC Rust and 237,160 Lean lines, including 30,253 generated lines and 206,907 source definitions/proofs (abstract/Table 1). Section 8.1 reports approximately 5,100 agent-generated theorems and 125 KLOC proof scripts. Its seven-hard-proof suite covers HKDF, ML-KEM and SHA-3; Figure 6 averages successful terminal runs. The reported Opus 5 comparison is about 2.8 times faster and 2.5 times cheaper than Opus 4.8, with Opus 5 alone closing all seven in single sessions. These are that suite's agent results, not translator throughput or a universal productivity improvement. Section 8.3 measures compiled cryptographic implementation performance separately, on an Intel Xeon W-2155 with AES-NI/AVX2; throughput uses 16 KB messages and latency medians at least 500 iterations. The report explicitly declines to quantify overall productivity gains because tools and agents evolved. Its industrial proofs retain translator/model/specification assumptions; functional correctness is not leakage resistance. Experimental algorithms are distinguished from deployed code. Basis: **documentation**, not measurements repeated here.

The [pipeline experience report, arXiv:2605.30106v1](https://arxiv.org/html/2605.30106v1), mixes Aeneas and Hax. Sections 5–7 report a small AI sample: two Aleph-completed running-example theorems, while four others remain sorry; that running example uses Hax. Its Aeneas fold_step result covers 13 checked operations and a finite-field specification under explicit bounds. Toolchain alignment uses Lean 4.26.0 for Hax work and 4.28.0 for Aeneas work. The paper describes historical extraction gaps and a monomorphic mathematical core workaround. Those observations do not establish that the current Aeneas source requires all generics to be monomorphized or every loop to carry an explicit recursive termination measure. Basis: **documentation**; downstream artifacts were not rebuilt or individually theorem-audited in this package.

### Current source exposes parallel work and diagnostics, not a speed guarantee

[Config.parallel](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Config.ml#L478-L497) defaults true. [Parallel.Pool](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Parallel.ml#L19-L38) lazily creates a Domainslib pool with recommended_domain_count minus one worker domains and tears it down at process exit. The pool map/filter-map paths schedule one async task per element and await the tasks. `-sequential` clears the option, switching to sequential list operations. These facts describe scheduler structure; they do not quantify useful core utilization, work balance, memory peak or throughput for an input crate.

[Translate.translate_crate_to_pure](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Translate.ml#L315-L325) computes a fresh whole-crate translation context. Before body translation it builds type/global/signature information. Around lines445–526 it separates opaque and transparent functions, sorts transparent functions by size in parallel mode, translates via parallel_filter_map and records optional timing data. Its own comment says size-first ordering does not seem to have much effect. Source intent is not a benchmark result.

The timers collect elapsed wall time and syntax size/rank for each translated function, under a mutex when storing results. `-diagnose-translation` prints times sorted descending; `-diagnose-micro-passes`, `-diagnose-detailed` and `-diagnose-limit` expose related diagnostic choices in [Main](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Main.ml#L259-L274). A per-function time in a parallel run is not additive process elapsed time: tasks overlap and can wait for shared resources. Size rank is an observable heuristic, not an abstract complexity bound.

The boundary [Translate.translate_crate](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Translate.ml#L2198-L2211) explicitly composes whole-crate pure translation and target extraction. It does not accept a previous translated_crate or a changed-declaration set at this entrypoint. Keeping a worker process alive can reuse its pool; it does not by itself validate a retained declaration after edits. This statement is narrowly about inspected entrypoints, not a global proof that no specialized reusable cache exists anywhere in the repository.

### Cost accounting needs separate stage identities

The following is a **derived accounting model** for interpreting the source and evidence. It is not an asserted complexity theorem or measured budget.

| Cost surface | Identity that determines the work | Source-established boundary / practical limit |
|---|---|---|
| Rust analysis and LLBC extraction | Rust source/dependencies, rustc/Charon, target and preset/options | Test runner invokes Charon separately from Aeneas; current package has not measured frontend time. |
| Whole-crate setup | LLBC snapshot, types/globals/trait information and Aeneas options | translate_crate_to_pure computes a context before per-function work. |
| Symbolic translation | Function body plus shared signatures/types/regions and checks | Independent tasks are scheduled per function, but each reads shared translation inputs. |
| Pure transformations | Translated body plus shared maps and representation options | Diagnostics distinguish micro-passes from translation; they are separate possible bottlenecks. |
| Emission | Declaration inventories, names, dependency groups, split-files and model registry | Source text caching and semantic reuse have different identities. |
| Lean elaboration/checking | Generated source, model library/toolchain, imports, tactic options | tests/lean is a separate Lake verification phase. |
| Proof search/development | Theorem statement, invariants/lemmas, automation and human/agent choices | Neither extraction timing nor generated LOC measures the search cost. |
| Proof maintenance | Changes to implementation, output interface, assumptions and dependencies | A unchanged Rust body can still acquire changed Lean signatures or imported lemmas. |

For a sequential full rebuild, stage elapsed times can be summed only if the timing windows are disjoint and include the desired setup. For a parallel workflow, critical-path elapsed time, summed CPU time, peak live working set and aggregate per-task wall times are different quantities. An acceleration at one phase can leave the critical path unchanged, or increase memory pressure enough to slow the total run. No asymptotic bound or universal scaling curve is implied by the current implementation.

### Checks and representation flags materially change the measured workload

[Main's -checks help text](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Main.ml#L133-L136) warns of an approximately100-fold slowdown. This is an upstream help-message estimate, **not a measurement in this report** and not a transferable prediction. [Config.sanity_checks](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Config.ml#L95-L99) defaults false, whereas the test runner appends `-checks` to its Aeneas command. Comparing a production-default run to a test run without recording that flag would change the program doing the work.

Other source-established switches affect output and obligations:

| Flag/default | What source says it changes | Why results under it are distinct |
|---|---|---|
| -sequential / parallel true | Internal function scheduling. | Changes overlap/resources; not an external-process concurrency cap. |
| -split-files | Types/functions/etc. emitted separately. | Changes imports, artifact inventory and target compilation dependencies. |
| -gen-lib-entry | Generates a library entry when output is split. | Output completeness includes that entry/import structure. |
| -loops-to-rec | Always extracts loops recursively. | Changes proof surface and possible termination obligations. |
| -loops-no-rec | Never attempts recursive-loop extraction. | Combinator representation is a different target artifact. |
| -feature-gates | Inserts assertions for target_feature requirements. | Different preconditions and target assumptions. |
| -eval-drops | Clears the default no-op Drop setting. | Changes interpretation/admission, not merely performance instrumentation. |
| -max-heartbeats / -max-recdepth | Sets generated Lean resource options. | A limit failure and a semantic counterexample are different outcomes. |
| -abort-on-error | Controls hard-stop failure behavior. | A partial file after an error cannot count as complete coverage. |
| diagnose flags | Collect/print function and micro-pass timing. | Instrumentation is part of the run identity and may have overhead. |

[Config](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Config.ml#L617-L627) sets default generated Lean maxHeartbeats to 1,000,000 and maxRecDepth to 2048. The loop fixed-point iteration guard is 2 in Config lines176–182; its comment explains the bound catches an unexpected loop in fixed-point computation. It is an implementation guard, not a mathematical proof that every valid source loop converges in two abstract iterations. A failed resource/iteration guard needs its own outcome category; treating it as a rejected source theorem or silently dropping that function loses information.

### The test workflow separates generation from verification

The current [test runner](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/tests/test_runner/run_test.ml) invokes Charon with `--preset=aeneas`, then Aeneas per backend. Its command adds `-print-error-emitters -no-progress-bar -checks -color -sequential`, and normally `-abort-on-error`. Normal tests require success; KnownFailure tests require failure and optionally retain a backend-specific .out stream. The runner performs no target proof check inside its Aeneas invocation. Target verification lives in the separate test Makefiles/Lake phase.

The runner's `IN_CI` path has a material reuse rule: for crate tests, when the target LLBC file already exists, it skips Charon regeneration because a custom derivation may have prepared it. That is intentional workflow reuse, not evidence that the existing file corresponds to arbitrary changed source. A reproducibility record needs to preserve which derivation produced that LLBC and whether the same input/dependency/target identity still applies.

The pinned [tests/README.md](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/tests/README.md) describes generation/golden updates, backend parsing/type checking and handwritten proof replay. It distinguishes expected Aeneas failure tests from Charon failures and says there is no option for successful translation followed by failed backend verification. It also says HOL4 outputs are checked but not regenerated. These are different coverage categories; a single suite label should not conceal them.

[tests/lean/Makefile](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/tests/lean/Makefile) copies the backend toolchain file, prepares the generated lakefile and runs `lake exe cache get && lake build`. These are source facts; no cache retrieval or Lake build was executed here. A warm cache shortens dependency preparation, while proof rechecking against changed local artifacts is a different cost. A cache hit does not establish that unbuilt or skipped obligations were checked.

The root [Makefile](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/Makefile) similarly separates `test` from `verify`, with `test` including extraction and Rust tests. A “test passed” statement therefore needs to identify its target: Rust tests, extraction, generated-file consistency and Lean checking are different stages with different failure oracles.

### Reproducible maintenance depends on an identity bundle

[charon-pin](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/charon-pin) declares a specific dependency revision, and [scripts/check-charon-install.sh](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/scripts/check-charon-install.sh) checks the checkout hash and executable presence. When charon is a symlink, the script explicitly skips hash enforcement on the assumption it is a working copy. Therefore “the setup script passed” alone is not enough to identify Charon bytes. Exact revisions or executable hashes remain necessary in an evidence record. The script was read only; its clone/build actions were not run.

An interface/model update also changes generated registry data. The pinned README's `make extract-lean-std` workflow builds model information into ExtractBuiltinLean. Its metadata includes parameter filters and failure/lifting choices, so stale registry data can affect generated ABI even if a model body appears correct. A proof library build and the generated translator registry must agree.

Derived maintenance identity has at least these components: Rust sources/dependency locks; rustc and target; Charon revision/preset/options; LLBC identity; Aeneas code and options; model/registry identity; Lean toolchain and package locks; generated inventory; theorem statements and assumptions. This is a statement about what can change results, not a request to freeze all development indefinitely. Deliberate updates remain possible when affected artifacts and checked claims move together.

### Process reuse and concurrency have explicit state boundaries

[Config](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Config.ml) keeps mutable process-global configuration. [Errors](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Errors.ml#L79-L98) keeps mutable error_list and unique_errors, protected during updates by a mutex. Main precomputes memoized builtin maps before parallel translation because the source comment identifies races during lazy memoization. Mutex-protected accumulation and precomputation improve a single invocation; they do not automatically turn the entire library into a request-isolated service.

The inspected Main accepts one LLBC filename and exits with failure if registered errors remain. The process boundary therefore provides a natural lifetime for global defaults and accumulated errors. A pool reused within that process is different from overlapping independently configured requests in the same process. The present source does not establish a supported request-reset protocol, cancellation contract or concurrent mutable-config API.

### Retained older execution establishes narrow component facts

The following observations come from corpus packages preserved at `fa65b241fd0cb2c791c841eace86d43d724359bc`. They were **not rerun** here and do not describe current-pin speed or correctness. The measured Aeneas binary SHA-256 was `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`, associated with nightly-2026.06.03/source ac9f1bc5. Retained support transcripts remain the evidence, rather than this summary becoming a new benchmark.

| Retained experiment | Exact useful observation | What remains outside it |
|---|---|---|
| Ten same-input generation runs | Fixed 19,827-byte LLBC; all ten emitted identical 1,219-byte Probe.lean; logs/mtimes varied. | No general theorem of determinism; no larger inputs or backend proof check in that probe. |
| Concurrent split-output Aeneas | Four isolated processes and three same-input shared-destination processes emitted matching three-file inventories; -sequential inside each process. | No same-process reentrancy, differing-input publication safety or shared Lake build-tree safety. |
| Two full tiny pipelines on macOS arm64 / 8 GiB | Low-overhead serial 44.276 s versus parallel 25.946 s; sampled group RSS 1,999,008 versus 3,599,968 KiB. | Only tiny wrapping-add functions, cached dependencies and private roots; four-worker ramp skipped. |

Sources: [repeat-run package](../aeneas-generated-source-repeat-run-probe-nightly-2026-06-03/REPORT.md), [concurrent-generation package](../aeneas-concurrent-generation-determinism-nightly-2026-06-03/REPORT.md), [combined-pipeline package](../anneal-3730-combined-pipeline-concurrency-2026-09-29/REPORT.md), as preserved in the frozen corpus. Package-relative links assume the report is adopted beside those existing packages.

The combined-pipeline report also retained a more intrusive instrumented run whose serial/parallel timings differed strongly. Its RSS sums can double-count shared resident pages; physical-footprint sums were sequential samples, not instantaneous group peaks. The report explicitly declines a general throughput law. One-Lean-slot controls and skipped four-worker admission are evidence of bounded workload scheduling, not a certified concurrency capacity.

### Scaling has distinct failure classes and completion criteria

The following classification is **derived** from current workflow boundaries and retained observations. It explains observed categories without asserting unmeasured rates.

| Outcome | Evidence needed to identify it | What a successful result means |
|---|---|---|
| Extraction/admission failure | Frontend/translator diagnostics and stage status. | The selected input did not complete that extraction configuration. |
| Partial generated output | Expected inventory/declaration coverage plus diagnostics. | Some artifacts exist; no claim of whole-program completion. |
| Target typing failure | Verifier errors with exact library/toolchain identity. | Generated interface/model mismatch or unsupported target construction. |
| Proof/resource failure | Remaining goals, limits, elapsed phase and diagnostic trace. | Automation did not complete under that budget; not a semantic counterexample by itself. |
| False specification/model assumption | Reviewed theorem/axiom or independent semantic counterexample. | A green build may remain logically relative to the wrong contract. |
| Successful proof replay | Exact theorem statements/assumptions and checked artifacts. | Those propositions are established in that Lean environment. |
| Deployment performance result | Compiled binary, platform/features and runtime workload. | Runtime behavior under that benchmark; not proof-development or translator speed. |

## Boundaries

- **Not examined:** fresh industrial/downstream builds, current-pin benchmark execution, a controlled agent productivity study, complete downstream theorem/axiom closure, large-crate memory profiles, native compiler runtime performance or every internal cache.
- **Unknown:** general end-to-end speedup from internal parallelism; throughput/capacity on the user's host; behavior of concurrent in-process requests; minimal semantic invalidation dependencies; current-pin scaling relative to the old binary.
- **Known not to follow:** paper LOC establishes translator soundness; successful agent proofs validate their specifications; old same-input hash agreement establishes publication safety; sampled RSS proves a hard instantaneous memory bound; help-text slowdown estimates are current benchmark measurements.
- **Historical claims:** older generic/loop limitations in experience reports are tied to their described toolchain/workarounds. Current explicit generic dictionaries, loop options and toolchain source take precedence when characterizing this pin.
- The paper summaries deliberately remain bounded. This package uses their reported metrics as context and supplies an independent current-source account rather than reproducing the papers or merging heterogeneous workloads into one score.

## Evidence

Acquired 2026-10-15. [evidence.json](evidence.json) preserves source excerpts for Main, Config, Parallel, Translate, Errors, the test runner, Lean test Makefile, dependency checker and exact pin/toolchain files. The source URLs in Findings are immutable. The paper identities include v1 explicitly; HTML and the existing 18-page SymCrypt PDF were inspected without downloading a new source mirror. No paper result was independently reproduced.

The three prior execution packages are named with frozen corpus revision and exact binary/input coordinates in evidence.json. Their source report and retained support files remain authoritative for those experiments. The local clean corpus was read-only throughout this package's preparation; only the assigned scratch directory was written.

## Revalidation

For a later source revision, inspect the same option defaults, timer placement, scheduling calls, whole-crate entrypoint, global state, test-runner reuse/skip logic, model-registry generation and dependency checks. Reclassify any changed interface rather than assuming continuity from a release label.

For an existing measured claim, the cheapest reliable revalidation is first its retained artifact/transcript checker; a new toolchain requires a fresh explicitly identified workload. Distinguish cold dependency preparation, warm rebuild, regeneration and proof replay; retain failures/skips and stage windows. Do not combine per-task overlapping timers into a total wall-time speedup.

Paper metrics should remain attached to their version and workload. New papers or downstream revisions warrant a new subject identity and a fresh completion/assumption assessment. Passing component probes or an industrial development remains evidence about those components and theorems; it does not remove the separate translator/model correctness obligations.
