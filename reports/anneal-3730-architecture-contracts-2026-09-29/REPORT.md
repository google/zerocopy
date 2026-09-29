# Architecture contracts and adoption gates for an interactive Anneal

## Summary

A fresh, fully specified request and a fenced complete result are a viable *baseline contract* for batch and live Anneal; keeping a backend process alive is an optimization that needs separate evidence of state reset, resource benefit, and cross-project isolation. The current Anneal V2 source at the examined commit does not yet implement a batch/LSP/MCP engine, so these are design gates rather than observations of an implemented architecture.

An executable toy stage compared a new process for every request, one persistent process per project, and one serial shared broker on the **same nine requests**. All three produced the same accepted digests, rejected a failed and a malformed stage result, kept two projects distinct, and reconstructed a correct result after process restart from a full request. Process launches were 9/3/2. With two 120 ms synthetic jobs, median pair wall time over three runs was 204.625/130.925/261.466 ms respectively. The broker's slower pair is a consequence of this fixture's single request lock, not a general claim about brokers or Lean. These measurements do not justify choosing a daemon for Anneal.

The adjacent corpus supplies concrete counterexamples to weaker alternatives: per-file sequential revalidation can accept a mixed A/B snapshot; last-completion-wins can select an obsolete stage; Lean can return a successful old-version wait and a stale imported goal; shared writable Lake outputs can conflict; and “no goals” can coexist with a weakened claim or an admission. Each counterexample has a narrow subject and cannot be promoted to an end-to-end Anneal failure.

## Applicability

The selected Anneal source is `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. Its V2 CLI exposed `setup` while extraction/scanning modules were not wired into a complete interactive pipeline, as documented by `anneal-interactive-pipeline-invalidation-graph-main-41f5b37`. The stack selected there is Charon `a535e914f74db4fd9e6be7048f4233270d8945c0`, Aeneas `ac9f1bc5262a5e4ff1e24ca78617121382202727`, and Lean/Lake `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. Later fixture reports executed pinned local binaries and delimit their own version/provenance claims.

The new experiment is a Python 3.14.7 standard-library process harness on macOS arm64. Its “compiler work” is a SHA-256 of a fully supplied `(project, source, model, toy-tool revision)` tuple plus an artificial 25 or 120 ms sleep. A worker may cache that exact tuple. Each child sends semantic results only through one JSON line; stderr deliberately contains a diagnostic-shaped `ERROR` marker on successful work. The parent validates request echo, status, and expected digest before accepting. This is an adapter and topology *model*, not an Anneal, Charon, Aeneas, Lake, or Lean invocation. The three retained trials differ in process scheduling and cache warmth, so raw elapsed times are observations of this implementation on this host, not backend predictions.

This report directly informs #3731 I001–I008 and I142/I144/I159. It makes the decision gates explicit while preserving the agenda's additional requested experiments. It does not adopt an architecture for the product.

## Findings

### The minimum cross-mode contract is about accepted meaning

For one captured request, batch and live acceptance should agree on: the Cargo compilation subject; exact authored source and annotation bytes; generated obligation set; Charon/Aeneas tool/configuration; complete generated model and imported Lean environment; allowed assumptions; and the intended theorem/claim being checked. A live response additionally needs its document version and worker/RPC incarnation to prevent an old answer being presented as current. The identity must describe *what was consumed*, not merely a locator or latest pathname. This is a proposed contract derived from the pinned stack graph and the executed freshness/acceptance counterexamples in the neighboring reports.

Byte-identical diagnostics, elaboration timing, proof-term serialization, `.olean` bytes, and progress ordering are not necessary for this proposed semantic agreement. The corpus's `lean-batch-diagnostic-normalization-oracle-v4-30-0-rc2` demonstrates path-dependent raw diagnostics and `.olean` bytes while one fixed theorem query has the same type and axioms; it also demonstrates that one consumer query cannot certify all declarations. The `anneal-3730-vertical-acceptance-v4-30-0-rc2` prototype distinguishes local no-goal status from an intended proposition and allowed axiom set. These are narrow execution facts. The stronger full contract remains to be tested on actual Rust-hosted annotations and current Anneal's eventual batch and live shells.

The stage request/response separation suggested by these facts is:

| Layer | Required request or result witness | Why it is separate |
| --- | --- | --- |
| Semantic request | subject, captured source/annotation, dependency/model/configuration/tool identities, requested operation | A stable file name or target slug can name changed content. |
| Process policy | executable/binary digest, timeout, cancellation, resource bounds | A process may be killed or reused without changing the intended semantic input. |
| Stage result | echoed request identity, explicit success/failure, complete output manifest and artifact hashes, diagnostics with origins | A zero-length or partial file, stale destination, or diagnostic-looking log is not accepted output. |
| Publication | current generation fence, remaining consumers, coherent immutable output selection | Completion order and cancellation alone do not authorize selecting “current.” |
| Proof acceptance | exact proof bytes, imported environment, obligation/claim identity, allowed assumptions, fresh verification status | “No goals” is narrower than checked intended Rust-level success. |

The first four rows are exercised only in the toy/fake-stage and selected CLI reports. The last row is a Lean-level prototype and claim contract; no report proves Rust-to-Lean correspondence for all obligations.

### Three process topologies preserve the toy semantic result with different costs

`support/topology_probe.py` runs six sequential requests, one post-restart request, and two overlapping project requests per topology. The six include repeated project A, a different project B with the same source label but different model, a B failure that returns a partial digest, and a malformed A response. The parent accepts only four successful sequential results, rejects the two bad results, and compares the post-restart A digest with its pre-restart value. Each topology passes the same assertions; all accepted digest sequences match exactly across topologies and three runs. Project/model collision is a negative control for a key that would contain source alone.

| Toy topology | Process launches, each run | Warm cache hits in six sequential requests | Two 120 ms jobs, median wall (three runs) | Ownership/coordination in this fixture |
| --- | ---: | ---: | ---: | --- |
| One process per request | 9 | 0 | 204.625 ms | Full request is the only state transfer; two children can run concurrently. |
| Persistent process per project | 3 | 2 | 130.925 ms | Each project has a distinct pipe/lock; restarting A does not terminate B. |
| Single shared broker | 2 | 2 | 261.466 ms | One pipe lock serializes the two requests; restarting that process loses both projects' warm caches. |

Sequential six-request wall sums were roughly 574–587 ms, 268–271 ms, and 214–216 ms respectively. The toy cache saves only its artificial delay. The one-shot mode pays Python process startup for every request, while the persistent modes reuse it. A parallel broker, a different workload, a larger backend startup, or real compiler state could change the ranking. This experiment says only that warm-process benefit and broker contention should be measured on the same real workload before adoption. Basis: **execution**, three retained JSON transcripts and script.

### Existing tool boundaries favor a conservative first adapter

At the selected pins, `anneal-interactive-pipeline-invalidation-graph-main-41f5b37` finds no Charon cross-run LLBC delta protocol and no Aeneas cross-request incremental translation protocol; the conservative semantic handoffs are complete LLBC and complete generated Lean. `anneal-3730-aeneas-process-contract-2026-09-29` observes separate Aeneas CLI processes and source-level global configuration/error refs, but did not execute same-process library calls. `anneal-3730-charon-aeneas-boundary-2026-09-29` shows a failed Charon extraction leaving an old LLBC file and failed Aeneas translation emitting partial Lean with `sorry`. These observations motivate output ownership by request and a complete manifest before publication. They do not prove that a reusable upstream library boundary is unsound.

For Lean, a persistent server is useful for exact tactic context at an open document. `anneal-3730-lean-protocol-races-v4-30-0-rc2` shows that a successful wait for version 1 can arrive after the client sent version 2 and that `plainGoal` has no exact version argument. `anneal-3730-lean-protocol-import-deletion-v4-30-0-rc2` shows an old open worker returning `no goals` after an imported module vanished, while a new worker and fresh batch reject the import. The fallback path is a client-side version/worker fence plus fresh controlled-worker or batch reconstruction where imported environment attestation is unavailable. This is a proposed adapter rule, not a claim that every restart is required under every Lean launch mode.

### Precedents support mechanisms, not Anneal equivalence

At the exact documentation revisions in `REPORT.json`, [TypeScript's language-service guide](https://github.com/microsoft/TypeScript-wiki/blob/966988bcca7c835fd22ab066bb6a9ff4d5ba511d/Using-the-Language-Service-API.md) describes a long-lived service with host-managed files, versioned snapshots, on-demand phase work, and a registry for sharing syntax trees across per-project services. Its own [plugin guide](https://github.com/microsoft/TypeScript/wiki/Writing-a-Language-Service-Plugin) says plugins can change the editing experience but are not loaded by normal `tsc` checking; this is a concrete reason editor diagnostics alone need not equal compiler acceptance. [Roslyn's overview](https://github.com/dotnet/roslyn/blob/3f15e26bcfc984bd9582487713e252f78b8cbbd1/docs/wiki/Roslyn-Overview.md) exposes compiler syntax/semantic/compilation objects through immutable solution snapshots in a mutable workspace, a stronger shared compiler core. [clangd's compile-command design](https://github.com/llvm/clangd-www/blob/ae5866d4552e30a173b8e9c3cec872a82e4c0120/design/compile-commands.md) configures its parser from a virtual compile command and warns that fallback commands can miss flags or includes. [rust-analyzer's architecture guide](https://github.com/rust-lang/rust-analyzer/blob/03fcb77246f2568adb0e9b2fa60d19c6cc1686f4/docs/book/src/contributing/guide.md) describes an I/O-free analysis host fed explicit file/crate graph changes, with cancellable current-state queries. These are **documentation/source** comparisons, not local execution of those tools or proof that their diagnostics match their command-line compilers.

[Volar's pinned README](https://github.com/volarjs/volar.js/blob/44d58aee30d1d476c8ad3f6f5581b288d7185d1e/README.md) separates virtual-code creation from language-service and LSP layers. The mechanism is relevant to Rust-hosted Lean projections, but proof context includes generated imports, Lean elaboration state, and source ownership that a generic virtual code mapping does not attest. `anneal-3730-projection-properties-2026-09-29` supplies a synthetic source-map ambiguity/rejection fixture; it is not a Volar or Razor reproduction. Thus I002/I003 retain their specific compiler-versus-editor and real embedded-language comparison cells.

### Decision gates and falsification controls

The first implementable candidate is a versioned job scheduler with complete stage inputs/results, separate per-consumer ownership, an immutable generation witness, and a post-completion publication fence. This follows the **fake-stage** and finite-model results (`anneal-3730-snapshot-capture-jobs-2026-09-29`, `anneal-3730-fault-model-2026-09-29`), not a production safety proof. It keeps one-shot Charon/Aeneas processes as a viable fallback while a persistent Lean worker serves live goals under explicit document/import identity. A richer incremental database, shared broker, or historical-query service should pass the gates below before adoption:

| Optional mechanism | Required measured win | Additional invariant/evidence gate | Current disposition |
| --- | --- | --- | --- |
| Charon/Aeneas process reuse | Startup/translation latency or memory improvement on representative A/B/A and errors | Same-process reset, output ownership, cancellation, fresh-process oracle | Unmeasured; Aeneas library execution remains toolchain-dependent. |
| Narrow dependency invalidation | End-to-end saved work versus whole-subject rebuild | Explicit dependency closure including newly discovered inputs; clean oracle and deletion cases | Not established. |
| Incremental projection | Better latency on real annotation edit streams | Full regeneration equality of text/maps plus source/projection CAS and malformed-input recovery | Synthetic property harness exists; real grammar absent. |
| Shared broker / server pool | Physical memory or startup gain at 1/2/4/8 actual jobs | Workspace separation, fairness, request routing, cancellation, restart reconstruction, no serial bottleneck | Toy broker serialized; real topology measurement pending. |
| Historical goal snapshots | Measured user benefit versus latest-only queries | Exact old imports/proof identity, retention/GC/expiry cost | Retention tiers measured on tiny Lake fixture; no real historical-goal service. |
| Remote execution | Local resource/latency shortfall that cannot be addressed more simply | Authentication, exact artifact identity, retry/cancel, fresh result validation | Conditional; no remote prototype is justified by this toy result. |

The issue's twelve I159 alternatives are tracked separately so a negative control is not mistaken for a universal prohibition:

| Control | Strong simple alternative | Evidence now; next discriminating cell |
| --- | --- | --- |
| N01 | Path/name alone identifies valid cache content | Same-path Rust/Cargo/Charon and LLBC ordering controls refute selected cells; full cross-layer ablation remains. |
| N02 | URI/version alone identifies current goal environment | Lean old-version wait and stale import worker refute selected cells; attest exact imports across launch modes. |
| N03 | Supported refresh can avoid worker restart | New/reopened worker succeeds after import deletion; test watcher/setup combinations that refresh an *existing* worker. |
| N04 | One server can host independent conflicting workspaces | Source report finds one inherited server environment; run matched actual workspaces, including conflicting imports, on one/many servers. |
| N05 | Shared writable generated build directory is safe | Lake writer runs include a two-consumer failure and four-consumer success; inject conflicting definitions and controlled interrupted publication. |
| N06 | Artifact cache plus minimum control source can reconstruct | Small Lake cache restores for some operations; run full prepared operation matrix and offline/home-isolated first query. |
| N07 | Rename/relocation preserves a prepared environment | Small Lake relocation with original path removed passed; test generated workspace, native/setup/trace paths, and retained workers. |
| N08 | Generated Lean can be canonical authored proof source | Annotation regeneration fixture preserves authored buffer; test real editor/generated external file ownership before rejecting or accepting. |
| N09 | Charon/Aeneas spans directly identify editable Rust ranges | Cross-tool provenance has lexical/serialized mapping limits; real Unicode, macro, one-to-many editable spans remain. |
| N10 | Every apparent proof-only edit skips upstream work | Macro reading doc attributes changed compiled behavior; test actual Anneal classifier on import/config edits. |
| N11 | No goals suffices for verification | Prototype weakened theorem and `sorryAx` controls refute it at Lean claim level; complete obligation/Rust coverage still needed. |
| N12 | Cancellation prevents late stale publication | Fake child completed late despite subscriber cancellation; apply fence to real pipeline stages and diagnostics/cache insertion. |

This table is a **decision ledger** for I144: it records evidence, counterexample, stronger untested claim, fallback, and cheapest next probe. It deliberately makes no adopted V2 design decision. The factual source and execution reports belong in `reference`; product design authority remains in Anneal's own design documents and review process.

## Boundaries

- **Not examined:** a current Anneal V2 batch/live implementation, real LSP/MCP transport, Charon/Aeneas/Lean running through the new toy adapter, or full Rust-level proof acceptance. No synthetic digest is a theorem or verification result.
- **Not established:** that one-shot is fastest or cheapest for the real stack; the toy workload fixes a 25/120 ms sleep and tests a serial broker. A concurrent broker can remove the observed serialization at the cost of extra routing and state management.
- **Not established:** the minimum sufficient cross-layer identity tuple, a sound subset dependency graph, or whether an existing worker can be refreshed without restart after every imported-artifact change. Those require the separate investigations cited above.
- **I002/I003:** The official precedent documentation is pinned and compared by mechanism, but no TypeScript/Roslyn/clangd/rust-analyzer/Volar/Razor process was executed here. Volar's README is an architectural overview, not a source-map semantics proof. The TypeScript plugin guide linked above is a moving wiki page rather than part of the pinned five-repository set.
- **I005/I006/I007:** The toy stage checks request echo, digest, failure, malformed output, and project cache separation. It does not simulate a real dependency mutation graph, true OS cancellation, progress stream, stdout contamination, work sharing by two clients, or all error classes. Those are covered only partially by adjacent fake-stage and finite-model packages.
- **I008:** The current pinned source review identifies candidate gaps (cross-run Charon delta; Aeneas reset; Lean exact-version goal and imported-artifact attestation; source mapping), but no upstream API patch or measured adapter-versus-patch comparison was made. Correctness has conservative fallbacks; latency optimizations may benefit from upstream work.
- **I142/I144/I159:** No optional optimization is approved. The table has all twelve named controls but most require stronger real backend and integrated falsification runs.

## Evidence

- `support/topology_probe.py`, SHA-256 `bd3189ca48a42ff772c41b13db761df7363263a8d60d9e235162803f83e11070`. Each run's full requests, responses, digests, cache hits, worker PIDs, process count, and timings are in `support/topology-run1.json`, `topology-run2.json`, and `topology-run3.json`, SHA-256 `cb46787b7f57eb8f92efbeeef72f765e8221eef7197b587ab7b8fbd7b3c67e62`, `51a282b9b1abe8bc488f967508e0d318148a1c97a75fb7a583e76e92fef4b491`, and `4a5d9bc530289a57cb0add05168bef0c267737dfc6c74253985b07bdf6ea98e0` respectively. Basis: **execution**.
- `anneal-interactive-pipeline-invalidation-graph-main-41f5b37/REPORT.md` and `anneal-v1-end-to-end-pipeline-41f5b37/REPORT.md` are **source synthesis** for the selected current and historical Anneal boundaries.
- `anneal-3730-snapshot-capture-jobs-2026-09-29`, `anneal-3730-fault-model-2026-09-29`, `anneal-3730-lean-protocol-races-v4-30-0-rc2`, `anneal-3730-lean-protocol-import-deletion-v4-30-0-rc2`, `anneal-3730-charon-aeneas-boundary-2026-09-29`, `anneal-3730-aeneas-process-contract-2026-09-29`, `anneal-3730-vertical-acceptance-v4-30-0-rc2`, `anneal-3730-lake-writer-scale-v4-30-0-rc2`, and `anneal-3730-lake-concurrency-preparation-v4-30-0-rc2` retain the specific **execution** and **source** evidence referenced above. This report does not rerun those packages.
- The five pinned documentation links in the precedent section were inspected on 2026-09-29. Their official repositories and full Git revisions are recorded in `REPORT.json`. Basis: **documentation/source**; the comparison and Anneal implications are **derived**.
- [Issue #3731](https://github.com/google/zerocopy/issues/3731), body I001–I008/I142/I144 and scope-extension comment I159, is the proposed investigation agenda, not a normative product design.

## Revalidation

Run `python3 support/topology_probe.py` from this package with Python 3.10 or newer. It writes `support/topology-results.json`; verify identical accepted digest sequences, rejection of failed/malformed results, cross-project separation, and post-restart reconstruction. Timings are expected to vary. For a future Anneal engine, replace the toy stage with typed Charon/Aeneas/Lean adapters and replay the same request/failure/restart controls, then compare accepted claims with an independent fresh process over the exact captured source and imported artifacts. Revisit the pinned upstream source regions and the twelve I159 controls when adopting any optimization or when changing toolchain versions.
