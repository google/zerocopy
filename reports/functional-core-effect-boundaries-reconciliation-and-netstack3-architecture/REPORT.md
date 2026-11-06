# Functional Core Effect Boundaries, Information Hiding, Reconciliation Loops, and Netstack3 Architecture

## Summary

This report synthesizes seven primary-source architectural studies and current-source delta reviews covering functional-core and explicit effect boundaries, Parnas information hiding versus pipeline decomposition, level-based reconciliation and repairable watcher caches, and the multi-year architectural evolution of Fuchsia's Netstack3:

1. **Functional Core / Imperative Shell, Ports and Adapters, Effect Systems, Sans-I/O, and Subprocess Effect Closure (1988–2026)**: Comparing Gary Bernhardt's *Boundaries* and *Functional Core, Imperative Shell* (2012), Alistair Cockburn's *Hexagonal Architecture / Ports and Adapters* (HaT Technical Report 2005.02, 2005), Lucassen & Gifford's polymorphic effect systems (POPL 1988, DOI `10.1145/73560.73564`), Plotkin & Pretnar's algebraic effect handlers (ESOP 2009, DOI `10.1007/978-3-642-00590-9_7`), Daan Leijen's Koka row-polymorphic effect types (EPTCS 153, 2014, DOI `10.4204/EPTCS.153.8`), Python's sans-I/O architecture (`brettcannon/sans-io@b4679927d555cb27d9960ae203c0ecd0d8209771`, Cory Benfield's 2015 Hyper-h2 account, and `python-hyper/h11@62c5068c971579d61fa1b55373390e12f25fd856` plus advisory `GHSA-vqfr-h8mv-ghfj`), and the Bazel Remote Execution API (`bazelbuild/remote-apis@adbf4a27c86fbea4a37637a6cbcacef372406fe7`) establishes that none of these patterns turns an opaque compiler or prover subprocess into a pure mathematical function. Treating a stage invocation as repeatable requires **property-relative effect closure** across four distinct effect classes: (a) **semantic inputs** (principal source, `include_str!` files, Cargo features/manifests, search paths, imported `.olean` environments, native plugins, and semantic clocks), (b) **execution policy** (operational timeouts, cancellation ownership, process lifecycle, and descendant cleanup), (c) **observational output** (progress, logs, and diagnostics), and (d) **authority-changing effects** (artifact installation and compare-and-swap publication fencing).
2. **Information Hiding Versus Pipeline Decomposition (1972–2026)**: Grounded in David Parnas's 1972 modularity criterion (*On the Criteria to Be Used in Decomposing Systems into Modules*, CACM 15(12), DOI `10.1145/361598.361623`), Parnas's 1979 program-family extension/contraction paper (DOI `10.1109/TSE.1979.234169`), Parnas, Clements, and Weiss's 1985 module guides (DOI `10.1109/TSE.1985.232209`), and Garlan & Shaw's 1994 pipes-and-filters analysis (`CMU/SEI-94-TR-021`), a verification tool's runtime dataflow pipeline (`Rust -> Cargo/rustc -> Charon -> LLBC -> Aeneas -> Lean/Lake -> diagnostics`) should remain visible for scheduling and provenance, but **pipeline stages should not be the primary code ownership boundaries**. Instead, modules should hide volatile design decisions across eight cross-cutting responsibility families—subject/source authority (`anneal/src/resolve.rs`), per-tool adapters, prepared-environment construction (`anneal/src/setup.rs`), scheduling/execution policy, artifact identity/storage (`anneal/src/scanner.rs`), provenance projection, incremental invalidation, and acceptance/publication authority—while deliberately exporting every semantic witness and TCB assumption on which verification soundness depends.
3. **Level-Based Reconciliation, Recoverable Watch Caches, and Local Filesystem Watchers (2005–2026)**: Combining Kubernetes `controller-runtime` (`kubernetes-sigs/controller-runtime@8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b`), `client-go` `Reflector` (`kubernetes/kubernetes@6d1d025050cb63ae5b8e53037aced205e6a28410`), WatchList KEP 3157 (`kubernetes/enhancements@914ed6950576832c8579899f092909d27623492e`), Kubernetes API concepts (`kubernetes/website@367a7a21bbef6b2d3c57d5fe113bee9bdb658889`), Borg/Omega/Kubernetes history (`ACM Queue` 14, 2016), and Linux `inotify(7)` (`man-pages 6.19`, 2026-02-14) shows that reliable reactive systems separate **what wakes work up** from **what makes state true**. Because filesystem watchers coalesce identical events, drop events on queue overflow (`IN_Q_OVERFLOW`), and race on recursive directory creation, notifications must be treated as deduplicable **dirty-scope hints** rather than a lossless replay log. Reconcilers should re-read the operation-specific authority (in-memory LSP buffer vs on-disk project snapshot vs canonical published pointer), build into private generations, and fall back to a scoped full rescan on watcher overflow, `410 Gone`-style continuity loss, or process restart. Current-source verification against `kubernetes-sigs/controller-runtime` `main` (`8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b`, plus diverged release `v0.25.1` at `67b72c2517be1d2b0dec612477eb20c3c959a8aa`) and `kubernetes/kubernetes` `master` (`08147af84478f859c2e2234d71ceace8bdb412c7`, +20 commits, plus diverged release `v1.37.1` at `f78e722310e50bcaca9276be22276d9e91d91308`) confirms zero blob changes across all three claim-mapped controller-runtime and Reflector files.
4. **Netstack3 Architecture Evolution: Core/Bindings Separation, Deferred Resource Destruction, Selective Static Typing, and Localized Lock Serialization (2019–2026)**: Across Fuchsia's Netstack3 (`fuchsia/fuchsia@c480400b0e6cb9a9b36384935639fb3e6566bd68` and historical commits `4ccfe9e3c10662b8dea3ccbf020553ebfa179ff3`, `495c194f4a8aabce4b04c7565a7a9d06a8a5462c`, `40ce8a08f2ffa1e9babc8e5b6aaa14cf486c0c6d`, `afe2e7ac4506c2f272c1b4a940cd2206b5756c19`, `a06fa769e2417889de925accc793d4e527280bc1`, `1e9fb101ed58968f5b4cf0b67a439f8cb0479b9d`, `09c560576ca357ffc0853c6251048af2a61b1543`, `d8e2be4f1380f1bcd25f1f1b4f9909f10760485c`, and `a3c17a4d6b3140f9175d6cf6ac4eb4e775f8dea8`), four architectural invariants survived major refactoring: (a) the semantic **core vs bindings** ownership split survived even after the original single core crate was split into `netstack3_ip`, `netstack3_device`, `netstack3_tcp`, and `netstack3_base` and TCP handshake status moved from bindings into core; (b) **identity, retention/liveness, operational eligibility, and reclamation completion** are separated via `PrimaryRc`, `StrongRc`, `WeakRc`, `TcpSocketSetEntry::DeadOnArrival`, and `RemoveResourceResult::Deferred`; (c) **static types** enforce durable local invariants (`AddrSubnet<A>`), whereas typestate socket IDs were deliberately collapsed into a single opaque `UdpSocketId` with runtime transition errors when callers needed stable identity across state changes; and (d) **concurrency** evolved from single-threaded whole-stack `&mut` access to contention-ordered fine-grained locks and core-emitted ordered state-delta channels without turning protocol calls into pervasive actors. Current-source verification across the 91-commit forward range on `fuchsia/fuchsia` `main` (`955de750a2aae45faa99e02e29715b794dd3b544`) found identical Git trees for `docs`, bindings `src`, `core/tcp`, `core/udp`, `core/device`, `core/lock-order`, and `core/sync`, with only one narrow 3-file IP/filter frame-metadata change (`76ab45a89c9f0ccc6e0bef3867a9ffcc775f8e10`).

---

## Applicability

These findings govern the module structure, host-effect interface, file/editor watcher reconciliation loop, resource lifecycle handles, and concurrency model of Anneal (`google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md` blob `d5339a95254eae14ac201139d07d9d36d48a19fb` and `anneal/DESIGN.md` blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`) and `zerocopy`:

1. **Keep Planning, Invalidation, and Acceptance Value-Oriented; Put Subprocess Execution Behind Semantic Effect Envelopes**:
   - Represent compilation-subject resolution, dependency comparison, staleness detection, and publication eligibility as deterministic state transitions over immutable value manifests.
   - Never model `invoke_tool(source) -> output` as a pure function unless the request envelope closes over (or explicitly records in the TCB) all material inputs: `include_str!` files, Cargo features/manifests, working directory, environment variables, imported `.olean` artifacts, loaded native plugins, and semantic clocks.
2. **Modularize by Change Decision (Parnas), Not by Pipeline Stage Name**:
   - Keep the transformation DAG (`Cargo -> Charon -> Aeneas -> Lake/Lean`) explicit as a dataflow specification, but organize code ownership around cross-cutting responsibilities (Subject Authority, Environment Preparation, Tool Adapters, Scheduler/Executor, Artifact Store, Provenance Projection, and Acceptance/Publication Authority).
   - Apply the counterfactual semantic information-hiding test: hide mechanisms whose replacement does not alter verification meaning (e.g., CLI vs library invocation, cache directory layout), and force interface witness changes whenever a change alters the verified claim or TCB.
3. **Treat File and Protocol Watchers as Level-Based Dirty Hints with Explicit Rescan Repair**:
   - Coalesce duplicate file-watch or editor-save events into dirty-scope keys, re-read the authoritative state for the target operation, stage builds/proofs into private generations, and update the canonical published generation only through a compare-and-swap fence.
   - Whenever `inotify`/watcher overflow, LSP/MCP reconnect, or worker restart occurs, discard incremental continuity assumptions and run a scoped authoritative rescan.
4. **Separate Object Identity, Liveness Leases, Operational Eligibility, and Physical Reclamation**:
   - Following Netstack3's `PrimaryRc`/`StrongRc`/`WeakRc` and `RemoveResourceResult::Deferred` design, distinguish a generation or workspace ID (naming) from a reader lease (liveness), retirement marking (forbidding new authority-bearing work on a superseded generation), and garbage collection (deleting backing directories/processes after all active readers drain).
   - Use static types for durable validated witnesses (`VerifiedArtifact`, `AnnealTargetName`, content digests) and runtime enums (`pending | prepared | current | stale | failed | retired`) for mutable lifecycle states that share a stable ID across transitions.

---

## Findings

### 1. Functional Core, Imperative Shell, Ports and Adapters, Effect Systems, and Sans-I/O Boundaries (1988–2026)

*(Coalescing `functional-core-effect-boundaries-1988-2026` and `functional-core-effects-hidden-state-2005-2026`)*

#### 1.1 Comparing the Four Effect-Separation Traditions
Each of the four architectural traditions draws a different boundary between computation and external interaction:

| Architectural Tradition | Primary Sources Inspected | What the Boundary Separates | What It Buys for Anneal | What It Cannot Guarantee Alone |
| :--- | :--- | :--- | :--- | :--- |
| **Functional Core / Imperative Shell** | Gary Bernhardt, *Boundaries* (SCNA 2012) & *Functional Core, Imperative Shell* (2012-07-12) | Value-in / value-out decision logic (core) vs stateful I/O shell (stdin/stdout, DB, network, processes) | Replayable, branch-rich planning, invalidation, and acceptance logic testable without spawning tools | Does not make the shell small, hermetic, or free of ambient env/filesystem/plugin leaks |
| **Hexagonal Architecture (Ports & Adapters)** | Alistair Cockburn, *Hexagonal Architecture* (HaT Technical Report 2005.02, 2005-09-04) | Application domain core communicating through **purpose-defined ports** implemented by technology-specific adapters | Naming host boundaries by authority (`EnvironmentPreparer`, `ResultPublisher`) rather than coupling scheduling to specific CLI tools | **Fake substitutability**: two adapters implementing the same trait (one-shot process vs persistent daemon) can have incompatible reset, plugin-retention, and cancellation semantics |
| **Polymorphic Effect Systems & Algebraic Handlers** | Lucassen & Gifford (POPL 1988, `10.1145/73560.73564`); Plotkin & Pretnar (ESOP 2009, `10.1007/978-3-642-00590-9_7`); Leijen Koka (EPTCS 153, 2014, `10.4204/EPTCS.153.8`) | Static value types vs conservative effect/region annotations and handler interpretations for state, I/O, time, and nondeterminism | Makes Anneal's own in-process authority explicit via capability objects or handler interfaces | Stops at the FFI/subprocess boundary: typing `invoke_tool` as one effect does not reveal which hidden files, env vars, or plugins the child process read |
| **Sans-I/O Protocol State Machines** | Cory Benfield (*The New Hyper*, 2015-10-15); `brettcannon/sans-io@b4679927d555`; `python-hyper/h11@62c5068c9715` (`README.rst` `5f2861600c54`, `_connection.py` `e37d82a82a88`, `notes.org` `36fd741bdac7`) | In-memory protocol framing and state transitions driven by caller-supplied bytes/events without socket I/O or async flow control | Deterministic, runtime-independent LSP/MCP framing, job-state machines, and publication fences | Sans-I/O is **stateful** (`h11.Connection` mutates internal buffers/state), requires caller-owned timeout/driving glue, and does not prove parser correctness (`GHSA-vqfr-h8mv-ghfj` chunked-encoding bug in `h11 <= 0.15.0`) |

#### 1.2 Why Opaque Subprocesses Require Explicit Property-Relative Effect Closure
Both the Bazel Remote Execution API (`bazelbuild/remote-apis@adbf4a27c86fbea4a37637a6cbcacef372406fe7`, `build/bazel/remote/execution/v2/remote_execution.proto` blob `8f83bc9351182a305e5f13ff8471dc28740640e5` and `platform.md` blob `56a11af92e96401fe41d5d945f2c33a7637461d4`) and preserved Anneal corpus experiments demonstrate that `output = run_tool(source_file)` is unsound without environment closure:
1. **Remote Execution `Action` vs Residual Worker State**: Even in `remote_execution.proto`, where an `Action` explicitly hashes the `Command` digest (arguments, `EnvironmentVariable` list, output paths, working directory), complete `input_root_digest`, `timeout`, and `Platform` (`OSFamily`, `ISA`), the specification notes that worker system libraries, mounted filesystems, and `PATH` resolution semantics (which had to be revised in API v2.3 to match implementation reality) remain executor-dependent unless sandboxed.
2. **Four Concrete Hidden-State Counterexamples from Reference Corpus Fixtures**:
   - **Unclosed Rust Compilation Inputs** (`rust-input-snapshot` fixture, blob `8d1ca9ff320e216be72abbca267c4372fcb8d0e1`): Holding principal `main.rs` bytes constant while changing an `include_str!` payload, active Cargo feature set, `Cargo.toml` default features, or macro-visible doc comments changed compiled output.
   - **Prepared-Environment Writability & Relocation Limits** (`lake-prepared-contract` fixture, blob `02adb1a0c60642109951c6ab0b328d8f180c13f1`): While a fully prepared Lake/Lean environment with a complete manifest supported relocated no-build and batch checks under an isolated `$HOME` and denied network, a source-only read-only consumer failed when Lake needed to create `.lake`.
   - **Native Plugin Pathname vs Resident Process Memory** (`native-plugin-mapped-workers` fixture, blob `0d504ae7388111b56ac307ee657c1ba6ff746881`): Redirecting a stable plugin file path from version 1 to version 2 left the running Lean watchdog process mapped to version 1 while a newly spawned file worker mapped version 2; only a full process restart unified both on the current file bytes.
   - **Non-Transactional Subprocess Cancellation & Publication Races** (`cross-tool-stage-cancellation-cleanup` blob `14e91986e6a25cc19f83929652613f8efa02ab44` & `fault-model` blob `b11f3bab8082ebe52ca47a2d10eb9f44d6f0832c`): Killing active Cargo, Charon, Aeneas, Lake, and Lean process groups left partial files in output directories, and removing any of the ownership, status, generation, worker-incarnation, completeness, or current-input fences in the bounded fault model allowed stale or cancelled work to corrupt published state.

#### 1.3 Four-Way Effect Classification and Three Operating Postures for Anneal
| Effect Category | Role in Verification & Orchestration | Required Host Control & Evidence Contract |
| :--- | :--- | :--- |
| **1. Semantic Inputs** | Source files, `include_str!`, Cargo features/manifests, `cwd`, env vars, imported `.olean`s, native plugin bytes, and **semantic clocks** (timestamps embedded in build scripts/codegen) | Must be captured in the immutable subject/environment manifest, blocked by sandbox policy, or declared in the result's TCB assumptions |
| **2. Execution Policy & Lifecycle** | **Operational clocks** (scheduler timeouts, worker leases, debounce timers), cancellation ownership (`consumer_id`), process-group termination, memory/CPU limits | Keep operational clocks out of semantic cache keys unless timeout alters cacheable status; treat cancellation as demand withdrawal + private-output cleanup, never rollback |
| **3. Observational Output** | Progress notifications, logs, diagnostics, timing telemetry | Tag with originating request/generation identity; never promote observational output to verification acceptance |
| **4. Authority-Changing Effects** | Installing shared cache artifacts, moving the `current` generation pointer, publishing verification success | Isolate stage writes to private generation directories; require a complete output manifest and atomic compare-and-swap generation fence at publication |

Across opaque stages (Charon, Aeneas, Lake, Lean), Anneal can operate at three explicit postures:
- **Posture 1 — Captured / Hermetic Execution**: Closed input-root digest, pinned toolchain, allowlisted env, restricted filesystem/network, private output directory.
- **Posture 2 — Controlled Ambient Execution with Explicit TCB**: Pinned tool/config identities, private output directory, generation fencing, and explicit residual ambient assumptions recorded in the verification result.
- **Posture 3 — Ephemeral One-Shot Process Isolation**: Fresh OS process per semantic job with private output directory to guarantee clean global/plugin reset when persistent-worker state is underspecified.

---

### 2. Information Hiding Versus Pipeline Decomposition (1972–2026)

*(From `information-hiding-versus-pipeline-decomposition-1972-2026`)*

#### 2.1 Parnas's Modularity Criterion vs Garlan & Shaw's Pipes-and-Filters
1. **Why Pipeline Stages Are Weak Code-Ownership Boundaries (Parnas 1972, DOI `10.1145/361598.361623`)**:
   - In Parnas's KWIC index comparison, decomposing a system into modules named after sequential execution steps (`Input`, `Circular Shift`, `Alphabetizing`, `Output`, `Master Control`) forces representation details and shared table formats to leak across every stage.
   - Parnas defines a **module** as a responsibility assignment that hides a difficult or likely-to-change design decision (`10.1109/TSE.1979.234169`), supplemented in complex systems by a hierarchical **module guide** (`10.1109/TSE.1985.232209`).
2. **Why the Transformation Pipeline Still Matters (Garlan & Shaw 1994, `CMU/SEI-94-TR-021`)**:
   - Pipes-and-filters describes **runtime dataflow** among transformations. In Anneal (`google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/src/{main,resolve,scanner,setup,util}.rs`, compared with historical V1 `dbb81cc7759bb6b21b82a1ca98bb32e9676f8655`), the transformation sequence (`Rust -> Cargo/rustc -> Charon -> LLBC -> Aeneas -> Lean/Lake -> diagnostics`) is essential for scheduling, provenance lineage, and debugging—but organizing top-level ownership solely as `cargo_stage`, `charon_stage`, `aeneas_stage`, and `lean_stage` scatters cross-cutting correctness invariants across every stage.

#### 2.2 Eight Responsibility Boundaries and the Semantic Information-Hiding Matrix
*(From `support/information-hiding-versus-pipeline-decomposition-1972-2026/change-matrix.json`)*

| Responsibility Family | Volatile Mechanism to Hide Behind the Interface | Semantic Witnesses & Evidence That Must Be Exported | Current V2 / Reference Anchor |
| :--- | :--- | :--- | :--- |
| **1. Subject & Source Authority** | `cargo_metadata` traversal, path canonicalization, workspace locator construction | Semantic compilation subject (`AnnealTargetName` extended with cfg/features/target/profile), exact source/annotation digest, unsupported-coverage flags | `anneal/src/resolve.rs` (`a87fa5cde060d5fbf59d47f68b5ed0823fe001c5`) |
| **2. Per-Tool Adapters** | CLI flag syntax, library vs subprocess invocation, temp file paths, reset protocol, raw stderr parsing | Exact tool/version/config identity (when in TCB), input digest, explicit success/failure status, complete immutable output manifest | Charon, Aeneas, Lake, Lean adapters |
| **3. Prepared Proof Environment** | Toolchain archive unpacking, Lake manifest/cache layout, relocation mechanics, `$PATH` construction | Imported `.olean`/package/toolchain witness, elaboration-affecting flags, trust-bearing library assumptions | `anneal/src/setup.rs` (`9e17911f4d1e7695cc63fe9f8b2b20b2f0322f00`) |
| **4. Scheduling & Execution Policy** | One-shot vs persistent worker pools, queue ordering, concurrency limits, signal delivery mechanics | Request identity, attempt/generation token, cancellation/completion witnesses, worker incarnation ID | `anneal/src/util.rs` (`602e1585d1c7b4cd61c736a420750b4c396ecdef`) & architecture-contract models |
| **5. Artifact Identity & Storage** | Directory naming, slug conventions, on-disk cache hierarchy, atomic rename/lock mechanics | Typed immutable artifact handles carrying content/semantic digest, producer witness, and completeness | `anneal/src/scanner.rs` (`7b4884c9ac16cf30146b851894bd7216b0d1edb8`) |
| **6. Provenance Projection** | Charon span tables, Aeneas generated line maps, internal source-map data structures | Authored Rust source origin, explicit `ambiguous`/`unmappable` status for macro/synthesized code, transformation lineage | Cross-stage source mapping |
| **7. Incremental Invalidation** | Dependency-graph storage layout, dirty-bit propagation, memoization table internals | Complete dependency/evidence closure justifying reuse; invalidation witness for cached artifacts | Pipeline invalidation graph |
| **8. Acceptance & Publication Authority** | Internal check ordering, storage CAS implementation, retry mechanics | Verified Rust subject, obligation/claim match, full TCB/assumption envelope, current-generation publication fence | Normative contract in `anneal/PRINCIPLES.md` & `anneal/DESIGN.md` |

---

### 3. Level-Based Reconciliation, Recoverable Watch Caches, and Local Watcher Loops (2005–2026)

*(Coalescing `reconciliation-event-hints-repair-loops-2005-2026` and `reconciliation-current-source-review`)*

#### 3.1 Separating Wake-Up Hints from Authoritative State in Kubernetes and Linux `inotify(7)`
1. **Level-Based Controller Reconciliation (`kubernetes-sigs/controller-runtime@8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b`)**:
   - In `pkg/reconcile/reconcile.go` (lines 102–119) and `pkg/doc.go` (lines 38–50, 184–205), controller watch events never carry the authoritative state transition to apply. Instead, events enqueue a deduplicated object key (`Request`), and the `Reconciler` reads actual current state to compute the delta toward desired state. Coalesced or duplicate events are harmless because reconciliation is **level-based**, not edge-driven.
2. **Recoverable Snapshot + Watch Stream Continuity (`kubernetes/kubernetes@6d1d025050cb63ae5b8e53037aced205e6a28410`, `kubernetes/website@367a7a21bbef6b2d3c57d5fe113bee9bdb658889`, `kubernetes/enhancements@914ed6950576832c8579899f092909d27623492e`)**:
   - As documented in `api-concepts.md` and implemented in `staging/src/k8s.io/client-go/tools/cache/reflector.go` (`watch`, `list`, `watchList`, `syncWith`), watch history is finite. When a client's `lastSyncResourceVersion` expires (`410 Gone`), `Reflector` clears its local store and rebuilds from a fresh consistent snapshot.
   - KEP 3157 (`keps/sig-api-machinery/3157-watch-list/README.md`, proposed 2022-01-14, alpha in v1.27, beta in v1.32, GA in v1.38) replaced memory-heavy initial `LIST` calls with streaming `watchList` into a temporary store up to an explicit bookmark boundary before swapping the live cache, with automatic fallback to `ListAndWatch`—proving that transport mechanics can change while preserving the **snapshot + version cursor + full-rebuild repair** invariant.
3. **Why Local Filesystem Watchers (`inotify(7)`, Linux `man-pages 6.19`) Cannot Be Replay Logs**:
   - Linux `inotify(7)` explicitly documents that (a) successive identical unread events are coalesced, (b) queue overflow (`IN_Q_OVERFLOW`) drops events and requires applications to rebuild their cache, and (c) watching newly created subdirectories races with file creation inside those directories unless followed by an explicit directory scan.
4. **Operation-Specific Authority in Editor/Disk Watch Loops**:
   - In the preserved Anneal save/format/watch-loop experiment (`google/zerocopy@2cec790eeec883e83ac66dcfa021c51ad65ad4f1`, report blob `ca2c4e0f92eb9432002b240a986073417a177b48`), an open Lean LSP document continued diagnosing its unsaved in-memory buffer while on-disk files were overwritten and compiled in the background; closing and reopening reconciled the LSP view with disk, while failed/killed background builds left the canonical published artifact pointer untouched until a valid build succeeded.
   - This yields the core local safety invariant for Anneal: **after notifications quiesce or continuity is lost, Anneal's current state must converge to what a fresh authoritative rescan of the operation's basis would produce**, while coalescing only invalidation hints (never authoritative user mutations) and staging all builds in private generations behind a compare-before-publish fence.

#### 3.2 Current-Source Review of `controller-runtime` and `client-go` `Reflector` (`2026-09-30`)
As verified in `support/reconciliation-current-source-review/matrix.json` and `support/reconciliation-current-source-review/official-source-observation.json`:
- `kubernetes-sigs/controller-runtime` `main` remained at `8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b` (0 forward commits; `pkg/reconcile/reconcile.go` and `pkg/doc.go` blobs identical; latest release `v0.25.1` on 2026-09-14 at `67b72c2517be1d2b0dec612477eb20c3c959a8aa` is a diverged release branch).
- `kubernetes/kubernetes` `master` advanced by 20 commits from `6d1d025050cb63ae5b8e53037aced205e6a28410` to `08147af84478f859c2e2234d71ceace8bdb412c7` (38 changed files across the monorepo, **0 overlap** with `staging/src/k8s.io/client-go/tools/cache/reflector.go`, whose Git blob is identical; latest release `v1.37.1` on 2026-09-23 at `f78e722310e50bcaca9276be22276d9e91d91308` is a diverged release branch).

---

### 4. Netstack3 Architecture Evolution and Current-Source Review (2019–2026)

*(Coalescing `netstack3-architecture-evolution-2019-2026` and `netstack3-current-source-review`)*

#### 4.1 Four Durable Architectural Decisions Across Netstack3's Evolution
Inspection of Fuchsia's Netstack3 documentation and source at `fuchsia/fuchsia@c480400b0e6cb9a9b36384935639fb3e6566bd68` (`src/connectivity/network/netstack3/docs/{CORE_BINDINGS.md,STATIC_TYPING.md,TENETS_AND_DESIGN_DECISIONS.md,IMPROVEMENTS.md,CONTROL_FLOW.md}`) alongside pinned historical commits and 2026 TCP/resource-reference snapshots (`support/netstack3-architecture-evolution-2019-2026/{judgment-matrix.json,source-map.json,timeline.json}`) establishes four lessons:

1. **Semantic Core/Bindings Ownership Outlived Crate Topology**:
   - `CORE_BINDINGS.md` separated platform-independent protocol logic (`Core`) from Fuchsia platform/FIDL/executor integration (`Bindings`), noting that `Core` resembles a functional core except that it owns mutable protocol state and interacts with `Bindings` through context traits (`TENETS_AND_DESIGN_DECISIONS.md`).
   - Although `CORE_BINDINGS.md` originally described "two crates," in May 2024 Netstack3 split the monolithic core crate into `netstack3_ip` (`afe2e7ac4506c2f272c1b4a940cd2206b5756c19`), `netstack3_device` (`a06fa769e2417889de925accc793d4e527280bc1`), `netstack3_tcp`, and `netstack3_base`.
   - Furthermore, when semantic ownership required it, state crossed the boundary: commit `40ce8a08f2ffa1e9babc8e5b6aaa14cf486c0c6d` (2023-07-08) moved TCP handshake status tracking from `Bindings` into `Core` because `Core` was the authoritative source of truth for connection state.
2. **Separating Identity, Liveness, Operational Eligibility, and Deferred Reclamation**:
   - Early Netstack3 passed `HashMap` keys to avoid borrow-checker aliasing across mutable state (`IMPROVEMENTS.md`).
   - By 2026 (`09c560576ca357ffc0853c6251048af2a61b1543` on 2026-06-23, `d8e2be4f1380f1bcd25f1f1b4f9909f10760485c`, and `a3c17a4d6b3140f9175d6cf6ac4eb4e775f8dea8` in `core/tcp/src/socket.rs` and `core/base/src/resource_references.rs`), long-lived resources use a three-tier reference system:
     - **`PrimaryRc`**: Owned uniquely by the authoritative table (such as the socket set).
     - **`StrongRc`**: Held by active socket IDs and in-flight operations.
     - **`WeakRc`**: Identifies the resource for diagnostics, timers, or destruction notifications without keeping it alive.
   - During teardown, `TcpSocketSetEntry::DeadOnArrival` handles races where an accepted connection closes before listener insertion completes, and removing the `PrimaryRc` under the socket-set lock returns `RemoveResourceResult::Deferred` when outstanding `StrongRc` handles remain—forbidding new operations while deferring physical deallocation until the last strong reference drains.
3. **Static Types for Durable Local Invariants vs Runtime Enums for Mutable Lifecycle Identities**:
   - `STATIC_TYPING.md` validates invariant-carrying value types such as `AddrSubnet<A>`, which verify constraints once at construction so internal functions never panic on malformed addresses.
   - However, in June 2023 (`4ccfe9e3c10662b8dea3ccbf020553ebfa179ff3`, preceded by temporary ICMP socket bindings removal in `495c194f4a8aabce4b04c7565a7a9d06a8a5462c`), Netstack3 **deliberately collapsed separate typestate UDP socket IDs into a single opaque `UdpSocketId`**, trading compile-time rejection of invalid transitions (such as binding an already-connected socket) for runtime error returns so callers could hold one stable identifier across socket state transitions.
   - Similarly, commit `1e9fb101ed58968f5b4cf0b67a439f8cb0479b9d` (2024-07-23) modeled multicast forwarding enablement as a runtime enum owning the route/pending tables so switching the enum to `Disabled` automatically purges all dependent state without infecting caller type signatures with typestate parameters.
4. **Serializing Specific Authority Transitions Without Pervasive Actors**:
   - Netstack3 evolved from single-threaded whole-stack `&mut` access (`CONTROL_FLOW.md`, `IMPROVEMENTS.md`) to fine-grained shared state with contention-aware lock ordering (`TENETS_AND_DESIGN_DECISIONS.md`).
   - Rather than turning every protocol module into an asynchronous actor with mailbox queues, `Core` operations remain direct synchronous calls over context traits, while critical sections emit ordered state-delta events into a `Bindings` channel so external FIDL watchers observe linearized state transitions without holding `Core` locks.

| Netstack3 Design Dimension | What Changed Over Time (2019–2026) | Durable Invariant Preserved | Transferable Rule for Anneal |
| :--- | :--- | :--- | :--- |
| **Core vs Bindings Boundary** | Monolithic `netstack3_core` split into `netstack3_ip`, `netstack3_device`, `netstack3_tcp`, `netstack3_base`; TCP handshake status moved into `Core` (`40ce8a08f2ff`) | Protocol state truth is owned by platform-independent `Core`; platform I/O and scheduling live in `Bindings` | Preserve semantic ownership boundaries rather than freezing current crate or process layouts; move shadow state to the true owner |
| **Resource Lifecycle & Teardown** | `HashMap` keys evolved into `PrimaryRc`/`StrongRc`/`WeakRc`, `DeadOnArrival`, and `RemoveResourceResult::Deferred` (`09c560576ca3`) | Naming (`WeakRc`), active lease (`StrongRc`), eligibility for new work, and final reclamation are distinct | Separate workspace/generation ID, reader lease, retirement marker, and physical artifact garbage collection |
| **Static vs Dynamic State Modeling** | Distinct typestate UDP/TCP socket IDs collapsed into unified opaque IDs (`4ccfe9e3c106`); multicast state stored in runtime enum (`1e9fb101ed58`) | Use static types for immutable local invariants (`AddrSubnet<A>`); use runtime enums behind stable IDs for mutable lifecycles | Use static types for validated digests/witnesses; use dynamic state enums for mutable job/generation lifecycle phases |
| **Concurrency & Serialization** | Single-threaded `&mut` stack replaced by lock-ordered shared state and ordered core-emitted state-delta channels | Linearize authority transitions under narrow locks; keep computation synchronous and state projection decoupled | Serialize generation publication and retirement; run translation/proof checking concurrently without actorizing every stage |

#### 4.2 Current-Source Delta Review Against `fuchsia/fuchsia` `main` (`955de750a2aae45faa99e02e29715b794dd3b544`)
As verified in `support/netstack3-current-source-review/matrix.json` and `support/netstack3-current-source-review/official-source-comparison.json`:
- Across the 91-commit forward range on `fuchsia/fuchsia` `main` from `c480400b0e6cb9a9b36384935639fb3e6566bd68` to `955de750a2aae45faa99e02e29715b794dd3b544`, recursive Git tree comparison shows **identical tree IDs** for Netstack3 `docs`, top-level bindings `src`, `core/tcp`, `core/udp`, `core/device`, `core/lock-order`, and `core/sync`.
- Only one Netstack3 commit (`76ab45a89c9f0ccc6e0bef3867a9ffcc775f8e10`) modified three blobs in IP/filter frame-metadata splitting:
  - `src/connectivity/network/netstack3/core/filter/src/logic.rs`: renamed `ProofOfEgressCheck::clone_for_fragmentation` to `clone_for_multiple_frames` (covering fragmentation and GSO segmentation).
  - `src/connectivity/network/netstack3/core/ip/src/base.rs`: added `SplitDeviceIpLayerMetadata` to keep unique transmit metadata on the primary frame while copying shareable metadata to secondary frames.
  - `src/connectivity/network/netstack3/core/ip/src/base/tests.rs`: added unit test coverage for metadata splitting.
- None of the four architectural conclusions in the Netstack3 study is altered by this localized IP/filter metadata change.

---

## Boundaries

1. **Source, Specification, and Historical Scope vs Runtime Execution**:
   - No new execution of Cargo, Charon, Aeneas, Lake, Lean, `python-hyper/h11`, Bazel Remote Execution, Kubernetes `controller-runtime`/`Reflector`, Linux `inotify`, or Fuchsia `Netstack3` was performed in this synthesis. Bounded Anneal execution findings (Rust input closure, Lake prepared environments, native plugin mapping, cross-tool cancellation, fault models, and save/format/watch loops) are cited strictly within the scope of their preserved reference corpus fixtures.
2. **Pattern and Domain Differences**:
   - Functional-core/imperative-shell (Bernhardt) and Ports-and-Adapters (Cockburn) are architectural design patterns, not formal soundness proofs; Koka and algebraic-effect soundness theorems apply within their typed language semantics and do not automatically constrain foreign subprocesses or native plugins.
   - Linux `inotify(7)` coalescing and overflow behaviors are specific to Linux man-pages `6.19`; macOS `FSEvents` and Windows directory-change notifications require their own platform-specific boundary checks.
   - Netstack3's packet-demultiplexing, passive-open TCP races (`DeadOnArrival`), and in-process `PrimaryRc`/`StrongRc`/`WeakRc` reference counts address kernel/network-stack concurrency; cross-process Anneal caches and disk artifacts require lease manifests and garbage collection rather than in-memory Rust reference counts alone.

---

## Evidence

### Primary Publications, Specifications, and Pinned Repositories
1. **Functional Core, Ports & Adapters, Effect Systems, Sans-I/O, and Remote Execution**:
   - Gary Bernhardt, *Boundaries* (SCNA 2012, `https://www.destroyallsoftware.com/talks/boundaries`) and *Functional Core, Imperative Shell* (2012-07-12).
   - Alistair Cockburn, *Hexagonal Architecture* (HaT Technical Report 2005.02, version 0.9, 2005-09-04, `https://alistair.cockburn.us/hexagonal-architecture/`).
   - John M. Lucassen and David K. Gifford, *Polymorphic Effect Systems*, POPL 1988, DOI `10.1145/73560.73564`.
   - Gordon D. Plotkin and Matija Pretnar, *Handlers of Algebraic Effects*, ESOP 2009, DOI `10.1007/978-3-642-00590-9_7`.
   - Daan Leijen, *Koka: Programming with Row Polymorphic Effect Types*, EPTCS 153, 2014, DOI `10.4204/EPTCS.153.8`; Andrej Bauer and Matija Pretnar, *An Effect System for Algebraic Effects and Handlers*, LMCS 10(4), 2014, DOI `10.2168/LMCS-10(4:9)2014`.
   - Cory Benfield, *The New Hyper* (2015-10-15); `brettcannon/sans-io@b4679927d555cb27d9960ae203c0ecd0d8209771` (`how-to-sans-io.rst` blob `afaddd4bb36c6268d1e77bcb6d9e618cd271478f`); `python-hyper/h11@62c5068c971579d61fa1b55373390e12f25fd856` (`README.rst` `5f2861600c543733424127ed0baa70e62c647373`, `h11/_connection.py` `e37d82a82a882c072cb938a90eb4486b51cdad99`, `notes.org` `36fd741bdac7294c42a1bb41f25c93821a39fdb3`) and `GHSA-vqfr-h8mv-ghfj` (2025-04-24).
   - `bazelbuild/remote-apis@adbf4a27c86fbea4a37637a6cbcacef372406fe7`: `build/bazel/remote/execution/v2/remote_execution.proto` (`8f83bc9351182a305e5f13ff8471dc28740640e5`) and `platform.md` (`56a11af92e96401fe41d5d945f2c33a7637461d4`).
2. **Information Hiding, Pipes-and-Filters, and Anneal V2 Source**:
   - D. L. Parnas, *On the Criteria to Be Used in Decomposing Systems into Modules*, CACM 15(12):1053–1058, 1972, DOI `10.1145/361598.361623`.
   - D. L. Parnas, *Designing Software for Ease of Extension and Contraction*, IEEE TSE SE-5(2):128–138, 1979, DOI `10.1109/TSE.1979.234169`.
   - D. L. Parnas, P. C. Clements, and D. M. Weiss, *The Modular Structure of Complex Systems*, IEEE TSE SE-11(3):259–266, 1985, DOI `10.1109/TSE.1985.232209`.
   - D. Garlan and M. Shaw, *An Introduction to Software Architecture*, `CMU/SEI-94-TR-021`, 1994.
   - `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`: `anneal/PRINCIPLES.md` (`d5339a95254eae14ac201139d07d9d36d48a19fb`), `anneal/DESIGN.md` (`0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`), `anneal/src/main.rs` (`b947700606677ea89c7a205f3ffcc75493508f63`), `anneal/src/resolve.rs` (`a87fa5cde060d5fbf59d47f68b5ed0823fe001c5`), `anneal/src/scanner.rs` (`7b4884c9ac16cf30146b851894bd7216b0d1edb8`), `anneal/src/setup.rs` (`9e17911f4d1e7695cc63fe9f8b2b20b2f0322f00`), `anneal/src/util.rs` (`602e1585d1c7b4cd61c736a420750b4c396ecdef`).
3. **Reconciliation Loops, Kubernetes Informers, and Linux `inotify`**:
   - `kubernetes-sigs/controller-runtime@8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b` (`pkg/reconcile/reconcile.go`, `pkg/doc.go`; plus release `v0.25.1` at `67b72c2517be1d2b0dec612477eb20c3c959a8aa`).
   - `kubernetes/kubernetes`: baseline `6d1d025050cb63ae5b8e53037aced205e6a28410` and target `master` `08147af84478f859c2e2234d71ceace8bdb412c7` (`staging/src/k8s.io/client-go/tools/cache/reflector.go`; plus release `v1.37.1` at `f78e722310e50bcaca9276be22276d9e91d91308`).
   - `kubernetes/enhancements@914ed6950576832c8579899f092909d27623492e` (`keps/sig-api-machinery/3157-watch-list/README.md`).
   - `kubernetes/website@367a7a21bbef6b2d3c57d5fe113bee9bdb658889` (`content/en/docs/reference/using-api/api-concepts.md`, `content/en/docs/concepts/architecture/controller.md`).
   - Brendan Burns et al., *Borg, Omega, and Kubernetes*, ACM Queue 14 (2016), pp. 70–93.
   - Linux `man-pages 6.19` (`2026-02-14`), `inotify(7)`.
4. **Fuchsia Netstack3**:
   - `fuchsia/fuchsia`: baseline `c480400b0e6cb9a9b36384935639fb3e6566bd68`, target `main` `955de750a2aae45faa99e02e29715b794dd3b544`, and intervening IP/filter commit `76ab45a89c9f0ccc6e0bef3867a9ffcc775f8e10`; historical commits `4ccfe9e3c10662b8dea3ccbf020553ebfa179ff3`, `495c194f4a8aabce4b04c7565a7a9d06a8a5462c`, `40ce8a08f2ffa1e9babc8e5b6aaa14cf486c0c6d`, `afe2e7ac4506c2f272c1b4a940cd2206b5756c19`, `a06fa769e2417889de925accc793d4e527280bc1`, `1e9fb101ed58968f5b4cf0b67a439f8cb0479b9d`, `09c560576ca357ffc0853c6251048af2a61b1543`, and TCP socket snapshots `d8e2be4f1380f1bcd25f1f1b4f9909f10760485c` and `a3c17a4d6b3140f9175d6cf6ac4eb4e775f8dea8`.

### Staged `support/` Artifacts
- **Functional Core, Effect Boundaries, & Information Hiding**:
  - `support/functional-core-effect-boundaries-1988-2026/evidence-map.json`
  - `support/functional-core-effects-hidden-state-2005-2026/evidence-map.json`
  - `support/information-hiding-versus-pipeline-decomposition-1972-2026/change-matrix.json`
- **Reconciliation & Current-Source Review**:
  - `support/reconciliation-event-hints-repair-loops-2005-2026/evidence-map.json`
  - `support/reconciliation-current-source-review/baseline-report-paths.txt`
  - `support/reconciliation-current-source-review/check_matrix.py`
  - `support/reconciliation-current-source-review/frozen-cohort.csv`
  - `support/reconciliation-current-source-review/matrix.json`
  - `support/reconciliation-current-source-review/official-source-observation.json`
  - `support/reconciliation-current-source-review/version-inventory-ebcdcad-581.csv`
- **Netstack3 Architecture Evolution & Current-Source Review**:
  - `support/netstack3-architecture-evolution-2019-2026/judgment-matrix.json`
  - `support/netstack3-architecture-evolution-2019-2026/source-map.json`
  - `support/netstack3-architecture-evolution-2019-2026/timeline.json`
  - `support/netstack3-current-source-review/baseline-report-paths.txt`
  - `support/netstack3-current-source-review/check_matrix.py`
  - `support/netstack3-current-source-review/frozen-cohort.csv`
  - `support/netstack3-current-source-review/matrix.json`
  - `support/netstack3-current-source-review/official-source-comparison.json`
  - `support/netstack3-current-source-review/version-inventory-ebcdcad-581.csv`

---

## Revalidation

1. **Re-Run the Current-Source Matrix Checkers**:
   - Execute:
     - `python3 support/reconciliation-current-source-review/check_matrix.py`
     - `python3 support/netstack3-current-source-review/check_matrix.py`
2. **Effect Closure and Information-Hiding Perturbation Checks**:
   - Whenever Anneal adds or modifies a backend stage or cache key, run a **fixed-declared-request perturbation test**: hold the declared request identity constant while perturbing one ambient input class (`include_str!`, Cargo feature/profile, environment variable, search path, native plugin binary, or worker generation) and verify that every promise-affecting perturbation either changes the captured manifest, is blocked by sandbox policy, or is explicitly declared in the TCB.
   - Trace the 8-scenario modularity change test (CLI-to-library swap, persistent server addition, Lake layout change, expanded Cargo subject identity, source-map format change, late stale worker response, trusted translator version bump, and dependency-graph omission) to verify that mechanism-only changes stay local to their adapter while meaning-changing modifications force witness updates at the acceptance boundary.
3. **Watcher Reconciliation and Resource Lifecycle Probes**:
   - Inject duplicate watcher notifications, dropped notifications / simulated `IN_Q_OVERFLOW`, rename-over-save replacements, watcher restarts, $A \to B \to A$ content cycles, and open-buffer-vs-disk divergence, verifying that Anneal converges to the exact state of a fresh authoritative rescan without moving the canonical published pointer on failed or superseded private generations.
   - When updating Fuchsia Netstack3 references past `955de750a2aae45faa99e02e29715b794dd3b544`, diff `src/connectivity/network/netstack3/docs/`, `core/base/src/resource_references.rs`, and `core/tcp/src/socket.rs` (`PrimaryRc`, `StrongRc`, `WeakRc`, `DeadOnArrival`, `RemoveResourceResult::Deferred`).
