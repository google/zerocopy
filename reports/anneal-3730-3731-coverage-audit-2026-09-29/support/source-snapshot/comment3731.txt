# Consolidation of #3730 into #3731

At Josh's request, this issue now combines both agendas. **Read the original I001–I144 in the issue body together with the scope extensions and I145–I159 below.** The original entries and IDs are retained; overlapping suggestions are merged into their scope instead of being copied as another backlog. The complete crosswalk accounts for all **174** numbered suggestions in #3730.

Merge baselines: #3730 last updated `2026-09-29T05:05:19Z`; #3731 last updated `2026-09-29T05:17:56Z`. Both had no comments at the initial read. This is an editorial consolidation, not executed research, adopted architecture, or a change to scheduled workers. Closing #3730 means consolidation, not completion of its experiments.

The motivating hypothesis remains `CLI / LSP / MCP → workspace/snapshot engine → Charon, Aeneas, Lake preparation, and Lean`, with Rust-hosted Lean projected into documents containing the correct generated model and scaffolding. All parts remain open to simpler alternatives and counterexamples. Method tags and evidence/authority rules from the issue body apply throughout.

## Additional investigations: I145–I159

These add distinct comparisons from #3730. They complement—not replace—the original I001–I144.

**I145 — Minimum cross-layer identity by ablation [S/M/X].** Prototype an identity tuple containing Cargo subject, exact source snapshot, Charon tool/configuration, LLBC digest, Aeneas tool/configuration, generated-tree digest, prepared Lake environment, import traces/hashes, projected URI/version/hash, server generation, file-worker incarnation, and RPC-session incarnation. Remove one dimension at a time and seek a counterexample. Keep locators constant while changing payloads at every stage; compare A→B→A, byte-identical output from different upstream histories, semantically equivalent but byte-different output, and unchanged proof text with changed imports. Distinguish monotonic causality from reusable content identity. Test a thin-adapter response envelope carrying workspace/generation, source/projected positions, current/stale status, actual environment, goal/diagnostic payload, and separately optional verification status.

**I146 — Retention versus recomputation economics [X].** Compare retaining source only; source plus projection; generated Lean; workspace-local Lake state; compiled generated modules; and live workers. Sweep 1/2/4/8/16 retained generations within host budgets. Measure disk, memory, reconstruction latency, and correctness of historical goals against old imports. Compare retained worker, reconstructed projection, fresh worker over retained artifacts, and refusal. Determine when a revision handle should expire rather than implying durable historical-query support.

**I147 — Source/artifact changes decoupled from each other [S/X].** Replace an imported `.olean` while leaving source unchanged, varying relevant timestamps; separately change source but obtain byte-identical rebuilt semantic artifacts. Include changed external models with unchanged Aeneas output. Query existing and refreshed workers and compare fresh batch controls. Determine when artifact identity forces reload, when restart is merely conservative, and which additional options/native/setup identities prevent byte equality from establishing an equivalent environment.

**I148 — Translation determinism and harmless textual instability [X].** Repeat identical Charon extractions and Aeneas generations sequentially and concurrently at Anneal's intended flags, split-file layout, and parallel settings. Preserve raw LLBC and Lean and separately compare justified semantic relationships. Investigate ordering/comment/formatting changes that leave the intended model equivalent but invalidate raw hashes, Lake traces, or Lean command-prefix reuse. Measure downstream cost before normalizing keys; retain source/provenance differences that matter to editing or evidence.

**I149 — Cross-layer declaration and generation manifest [S/X].** Prototype one machine-readable handoff manifest with subject/tool/configuration identities, source LLBC digest, complete generated file list, module/import graph, declaration identities, and coarse source provenance. Relate compiler-resolved Rust items through Charon declarations and Aeneas pure declarations to generated Lean declarations and Anneal obligations, including one-to-many helpers. Keep exact editable proof ranges separate. Test navigation, deletion, and invalidation consumers; establish what Anneal must supply at its selected Aeneas pin without assuming newer `translation.json` support.

**I150 — Prepared-environment contract by operation [S/X].** Enumerate required inputs/artifacts/configuration for batch build, `lake env lean --json`, `lake serve`, per-file `setup-file`, InfoView/RPC, and native plugin/dynamic-library use. Classify producer-owned immutable state, consumer-owned mutable state, and any explicitly permitted shared-writable cache. Test the minimum source/control-plane material plus artifact cache as a reconstruction candidate and identify missing classes. Derive the identity under which pooling is valid rather than using a single unqualified “prepared” flag.

**I151 — Shared writable build-tree counterexample study [M/X].** In owned disposable fixtures, compare consumers sharing one writable package directory or generated-module build directory with isolated consumers over a frozen producer. Run identical and conflicting builds and interrupt writers at controlled publication points. Check cache maps, partial outputs, subsequent reads/retries, and cross-consumer definitions. Seek the strongest valid shared-writer contract or preserve a minimal failure—not a preselected negative result. Keep artifact-cache publication distinct from shared package-directory mutation.

**I152 — MCP subscriptions versus polling [S/X].** On explicitly supported protocol revisions, prototype subscriptions/change streams for generation changes, diagnostics, proof readiness, and verification completion; compare polling and explicit state reconciliation. Drop or delay notifications, disconnect clients, and retry result retrieval. Determine whether subscriptions improve responsiveness while polling/reconciliation remains the correctness path, and provide a capability fallback rather than presuming every MCP client supports the same mechanism.

**I153 — Server, MCP, and scratch-pool topology [X].** For one prepared environment, compare N open proof files under one watchdog with N independent servers. Compare one MCP process serving many sessions, environments, or repositories with per-workspace adapters and an external broker. Sweep 1/2/4/8/... prewarmed scratch documents and compare fresh scratch creation, prefix reuse, teardown, memory, latency, and process ownership. Use conflicting definitions/options/plugins to detect cross-workspace reuse; do not pool independently configured projects merely because document APIs accept their URIs.

**I154 — Fixture sharing and contamination sentinels [X].** Compare one workspace per test, one per fixture with multiple phases, and one per logical suite. Give each test a unique model definition or option that makes accidental reuse observable; include conflicting plugins where supported. Run phases in different orders and parallel schedules, interrupt selected workers, then rerun subsequent tests. Measure disk/setup savings against required reset/isolation guarantees rather than replacing heavyweight sandboxes with untested shared mutable state.

**I155 — Shadow files and hidden Lean-document lifecycle [S/X].** If Lean/Lake requires physical paths, distinguish internal file-backed URIs from editor-facing logical documents. Independently of backing choice, open/change/save/rename/close a Rust host and trace hidden document creation, workers, updates, and cleanup. Keep unsaved source authoritative while deliberately stale or missing shadow files exist; crash/restart and reconstruct without treating mirrors as canonical. Test whether custom URIs require shadow paths, and whether model regeneration can preserve authored proof identity while changing the environment generation.

**I156 — Explicit backend capability negotiation [S/X].** Prototype versioned descriptors for accepting unsaved inputs, filesystem materialization requirements, concurrent requests, cancellation, deterministic output, persistent process support, and fine-grained invalidation. Test descriptors against actual implementations and unsupported combinations. Distinguish a documented promise from measured behavior; choose conservative fallback or explicit failure when capabilities are absent rather than letting a uniform logical API imply uniform implementation guarantees.

**I157 — Batch and transport-free live shells over one engine [X].** Build a small batch shell and an in-process repeated edit/query driver over the same structured engine. Compare the batch shell with current CLI behavior where implemented and the live driver with fresh checks on identical captured inputs. Include model changes, cancellation, and reconstruction before adding an LSP/MCP transport. Identify divergence caused by the engine separately from adapter protocol bugs; the prototype does not claim the current CLI already implements every stage.

**I158 — Minimal interactive upgrade suite and workaround deletion probes [S/X].** Derive a small retained replay suite for compatible toolchain tuples. For Lean/Lake, cover configuration ownership, workspace isolation, dependency refresh, goal versioning, server setup, and artifact families. For Charon, cover LLBC schema, span units, process lifecycle, determinism, and subject identity. For Aeneas, cover mutable globals, package layout, naming, provenance, determinism, and library/incremental APIs. Associate every manifest/trace/mtime/rewrite workaround with the exact behavior requiring it and a probe that would justify removal. Compare the examined 4.30 pin with 4.31 or another explicitly selected compatible candidate; retain accurate old-version findings and do not create a competing mutable corpus lifecycle.

**I159 — Deliberately challenge the proposed architecture [M/X].** Run the following as falsification controls in the relevant existing harnesses, not twelve duplicate surveys. Build the strongest plausible simple alternative; record the smallest counterexample or exact successful preconditions. Do not assume the leading design must win.

| Original #3730 control | Alternative to test | Main investigations |
| --- | --- | --- |
| N01 | Path/name identity alone establishes cache validity | I011, I079, I097, I145 |
| N02 | URI/document version alone establishes query freshness | I041, I048, I145, I147 |
| N03 | Supported refresh can avoid worker restart after imported changes | I049, I050, I147 |
| N04 | One Lean server can safely serve conflicting independent Lake workspaces | I004, I057, I153 |
| N05 | Consumers can share one writable generated build directory | I102, I108, I151 |
| N06 | Artifact cache plus minimum source/control state reconstructs the environment | I092, I098, I104, I150 |
| N07 | Renaming a prepared directory preserves a valid generated environment | I052, I101 |
| N08 | Generated Lean can be canonical proof source without losing user edits on regeneration | I024, I085, I155 |
| N09 | Charon/Aeneas spans alone recover editable Rust ranges, even for Unicode/macros/scaffolding | I019, I025–I027, I087 |
| N10 | Every apparent proof-only edit can bypass upstream preparation, even import/config edits | I018, I091 |
| N11 | “No goals” suffices for agent verification success despite stale imports/errors/admissions/coverage gaps | I129–I132 |
| N12 | Cancellation alone prevents stale publication when cancelled work completes late | I053, I105–I106, I134 |

## Scope extensions to I001–I144

The following details are merged into the named investigations; they are not separate duplicate tasks. Read each original entry together with its extension here. All other original entries retain their full scope.

**I006.** Include Lake's preparation/build calls explicitly. The result contract should be tested with output identity, diagnostics, provenance, timing/resource metadata, progress, cancellation, and stale status. Inventory every backend write in an instrumented environment; compare native structured progress with safely derived progress without embedding UI policy.

**I009.** Mutate body, module, feature, target, profile, `cfg`, build-script output, proc-macro implementation, dependency version, and toolchain separately; record which compilation subjects change.

**I014.** Include two editors with different unsaved buffers and two agents racing read-only queries, proof patches, and verification starts. Compare separate snapshot forks with shared-current-document semantics rather than presuming one current buffer fits both.

**I016.** Destroy every live process and reconstruct one retained generation; compare goals and diagnostics as well as imported identities and fresh batch checking.

**I017.** When delimiter corruption makes a payload temporarily undiscoverable, determine explicitly which previous queries and diagnostics remain usable, stale, or unavailable.

**I018.** Run positive annotation-only controls through rustc/Charon and compare both byte-level and justified semantic LLBC equality. Test import/configuration-affecting annotation edits separately: skipping Charon does not imply skipping Lake setup.

**I019.** Include `cfg_attr`, attribute/procedural macros, `include!`, and generated files. Determine whether each transformed annotation supports exact editing, only read-only inspection, or no reliable attachment.

**I021.** Include whitespace-only movement, file/module rename, and deletion of the owning range during an in-flight query; trace source maps, generated import names, and worker reuse, not just item lookup. Determine when correspondence can be retained without broad rediscovery.

**I025.** Preserve an exact Rust-byte-range sidecar before compilation. Test ASCII, wide characters, and positions before/inside/after surrogate pairs; compare Rust bytes, projected bytes, Lean raw positions, LSP UTF-16, and returned goal/diagnostic locations. Round-trip every valid authored position; classify invalid or ambiguous positions rather than forcing a bijection.

**I026.** Inventory doc/block-comment prefixes, indentation, fence removal, escaped doc strings/documentation attributes, concatenation, line-ending normalization, and inserted imports/namespaces/scaffolding. Classify each transformation as lossless, invertible, partially invertible, or synthetic. Include nested Markdown fences and Lean comments containing fence-like text; test accepted/split/rejected edits across authored, Anneal-generated, and Aeneas-generated regions.

**I031.** Induce failures in generated theorem names, binders, and tactics as distinct responsibility-anchor cases. Evaluate candidate Rust-facing blame anchors without presenting synthetic text as directly editable source.

**I032.** Compare full-content `didChange` with range-local updates for correctness, emitted ranges, Lean reuse, latency, and implementation complexity. Include host-only edits and rustfmt reflow that shift Rust coordinates while projected Lean stays unchanged; test safe remapping versus rejection of in-flight results.

**I035.** Include one document per Rust item, alongside per-annotation, per-file, and per-Cargo-target layouts.

**I041.** Prototype the wrapper over both `plainGoal` and rich interactive goals, recording request-start text/hash/version, environment, worker, and response-time state. Query many positions simultaneously while editing, and observe ordering, cancellation, and completion.

**I042.** Compare `waitForDiagnostics`, file-progress completion, RPC-specific readiness, command-snapshot completion, and a candidate custom RPC that returns current document/environment identities.

**I043.** Include term proofs and compare the simple and rich surfaces across syntax errors, incomplete elaboration, restart, and RPC reconnect before selecting an internal API.

**I044.** Add environment swaps and idle timeout. Test stale RPC references, session IDs, and MCP handles after replacement or collection; expired identifiers must not be silently rebound.

**I047.** Compare retaining an old worker, reconstructing an old projection with old imports, restarting against retained old artifacts, and refusing the query. Decide whether revision handles are retained snapshots or optimistic current-state guards.

**I049.** Test notification only, proof-text resend only, close/reopen, supported dependency refresh, file-worker restart, entire-server restart, and a new workspace/server generation. Seek the minimum reliable barrier, not a predetermined restart policy.

**I050.** Include an external user model changed while Aeneas output is byte-identical. Use several independently edited proof documents importing one model and verify affected-worker fan-out while unrelated workers remain valid.

**I051.** Include direct overwrite, temp-directory generation, and an atomic generation-pointer swap as explicit alternatives; test interrupted split-file Aeneas emission as well as compiled-artifact publication.

**I057.** Keep the editor connected while switching workspace folders or moving files across Cargo/Lake boundaries; verify routing to the correct independently configured server.

**I058.** Include stale diagnostics with fresh goals and the converse, so distinct streams cannot be combined into an apparently current result.

**I059.** Test signature help and inlay hints as well as hover, completion, semantic tokens, references, and navigation; determine whether each needs feature-specific projection rules.

**I063.** Test save when the projection already reflects the same or newer unsaved buffer: no duplicate generation or version reversal. Include rustfmt changing host indentation while preserving Lean payload.

**I065.** Prototype explicit open/create, snapshot publication/update, current-generation lookup, goal/check, and close/release operations. Compare synchronous tools with task-backed long work on supported protocol revisions; retain application identities independently of transport sessions.

**I066.** Evaluate navigation from Rust annotation through projected proof, Aeneas declaration, and imported model back to the owning Rust item. Test the result envelope in I145 rather than exposing brittle paths.

**I069.** Classify queries, diagnostics, scratch trials, proof edits, ordinary Rust edits, generated-file edits, regeneration, verification, environment rebuilding, and toolchain setup separately. Instrument supposedly read-only tools for hidden source/shared-environment mutations; execution permission is not write permission.

**I070.** Exercise the complete loop: goal at G → candidate → compare-and-swap patch → readiness for G+1 → re-query. Inject unrelated edits between every step and measure scratch prefix reuse and cleanup without touching canonical source.

**I071.** Cancel before start, during Lean queries/Lake setup/Aeneas work, and immediately after completion; cover task result retrieval and late completion separately.

**I072.** Compare Anneal speaking Lean LSP/RPC directly with delegating to an existing Lean MCP bridge, including state identity, cancellation, projections, environment ownership, and observability.

**I074.** Vary workspace location, symlinks, `CARGO_MANIFEST_DIR`, `OUT_DIR`, relative include/build-script paths, and path-sensitive proc macros explicitly.

**I077.** Include a retained wrapper that launches fresh rustc processes, distinct from in-process extraction, and measure startup costs without conflating process reuse with semantic reuse.

**I080.** Measure whether isolated materialized overlays can share Cargo/rustc incremental products safely and cheaply, including later retries after interrupted extraction.

**I081.** Measure warm whole-crate calls that retain only initialization, not old semantic results. Vary backend/options, namespace, output directory, crate name, and failures. Execute the available library repeatedly and compare parallel requests in one process, serialized requests, and separate processes against fresh executable controls.

**I083.** Include a restricted body-only prototype that reuses unaffected function translations, validated against clean whole-crate output; report the metadata and restrictions it requires.

**I089.** Use rich RPC goals and dependency refresh as well as first open/query. Add a genuinely missing-manifest negative control against the real archive before testing pre-seeding. Rebuild only consumer-generated modules and verify zero dependency-universe writes.

**I090.** Add `-K` options, server options, platform, and Lean executable/hash differences to the consumer-identity matrix.

**I091.** Test user-authored imports/options competing with generated headers. Immediately open/query after a successful batch build and observe extra setup or rebuilds; track unsaved import changes through dependency building, worker restart, and cache behavior.

**I092.** Exercise the dependency-build-never path using `--no-build --no-cache` in a real generated workspace, and verify explicit failure for deliberately stale or missing imports.

**I095.** Distinguish local reuse, cache restoration, compilation, reconfiguration, dependency resolution, network access, and shared writes. Where no structured status exists, evaluate the reliability of filesystem/process inference.

**I098.** Omit `.olean`, `.olean.server`, `.olean.private`, `.ilean`, native plugins, dynamic libraries, and trace/hash sidecars individually; compare batch acceptance with interactive setup.

**I099.** Compare `ModuleSetup`, imported artifact paths/hashes, server options, diagnostics, goals, and navigation/references, in addition to compiled-artifact and declaration checks.

**I100.** Perturb source, configuration, and artifact mtimes independently of bytes; compare normal and `--old` builds, `setup-file`, and server startup.

**I101.** After complete server preparation, relocate consumer only, toolchain only, and both together. Check interactive diagnostics/navigation and source-map identity so normalized paths cannot conceal wrong origins or become brittle persistent handles.

**I102.** Run many identical and different writers; kill them during publication and verify subsequent readers and cache-map integrity.

**I104.** Compare empty HOME/XDG, populated unrelated Lake/Mathlib caches, and deliberately incompatible caches under actual network denial.

**I105.** Map one logical cancellation request to child kill, process-group kill, Lean JSON-RPC cancellation, and task cancellation. Follow editor cancellation through projection and shared upstream jobs without over-cancelling other consumers.

**I107.** Create a high-parallel identical-cache-miss storm. Compare shared cache writers, a serialized producer build, and isolated builds followed by publication, with individual consumer cancellation and producer failure.

**I109.** Include inode exhaustion independently of byte-capacity exhaustion.

**I110.** Force a file-worker crash after unsaved edits and check reconstruction from watchdog/client text, with the correct generation; distinguish this from graceful restart. Crash and retry the identical request for each backend to test replaceability without hidden history.

**I113.** Classify every per-worker byte as necessary mutable state, generated fixture state, shareable immutable input, or accidental duplicate product/cache; instrument hidden writes outside temporary roots.

**I114.** Use guarded 1/2/4/8/16/32-consumer disk/throughput sweeps and 1/2/4/8/16-server memory sweeps where host budgets permit; smaller runs do not establish unexecuted cells.

**I115.** Count Cargo jobs, Charon parallelism, Aeneas domains, actual Lake jobs, Lean file workers, and concurrent MCP scratch trials against the same measured budget.

**I116.** Run hundreds or thousands of edits/generations where budgets permit, recording file descriptors, temporary files, cache growth, and all Anneal/MCP/Lean descendants as well as memory.

**I118.** Separate workspace construction, generated-module build, server launch, `setup-file`, first goal, and later proof-edit/goal latency in cold and warm runs.

**I124.** Where supported, compare APFS, ext4, container/overlay filesystems, and remote/networked CI runners for the sharing and publication strategies; keep unsupported environments conditional.

**I129.** Include solved-local/later-file-error, failing sibling theorem, stale imports, admitted dependency, warning-only acceptance, and unsupported upstream translation. Trace verified G → edited G+1 → new projection with old model → prepared new model/incomplete proof → fully checked G+1.

**I130.** Vary toolchain and plugin identities while proof text stays fixed; check that TCB-relevant changes invalidate cached results and remain visible in the trust account.

**I131.** Run valid/invalid proofs through batch, fresh/warm servers, edited servers, and dependency-changed/restarted servers. Check both directions: live acceptance followed by fresh same-generation batch verification, and batch acceptance followed by cold interactive goals without unexpected prerequisite rebuilding. Record actual imports/options/plugins in each mode. In the tested agent workflow, fresh-check every interactively accepted proof and classify all mismatches.

**I134.** Force overlap at every handoff: Rust changes during Charon, LLBC replacement during Aeneas, generated publication during Lake, Lake rebuilding during Lean elaboration, proof edits during model publication, and MCP queries during any upstream advance.

**I139.** Inject controlled, recorded worker kills during high concurrency; check producer immutability, cache integrity, orphan cleanup, subsequent tests, and disk leaks. Include reproducibly seeded random failure schedules.

**I141.** Compare retaining stale diagnostics, hiding them, showing a rebuilding banner, and showing old-model proof feedback with explicit generation identity.

**I144.** After sufficient execution evidence, synthesize ten linked contracts: (1) state machine with legal transitions/invariants for source, model, environment, projections, workers, verification, and stale/tainted states; (2) change matrix distinguishing unchanged, reusable, invalidated, rebuilt, restarted, and reverified; (3) stable/ephemeral identities for workspace, subject, snapshots, model, environment, document, worker, and result; (4) canonical/generated/projected source ownership, editable versus responsibility maps, persistence, and regeneration; (5) setup-once versus per-consumer state, immutable versus permitted shared-writable state, and fail-closed operations; (6) exact goal-at-Rust-position semantics; (7) MCP semantic API; (8) editor/LSP lifecycle API; (9) measured integration-test sharing/isolation and resource envelope; (10) batch/live agreement, intentional differences, and fresh/clean oracles. These are design proposals until adopted in the proper authority; factual reports remain in `reference`.

## Complete #3730 → #3731 crosswalk

The left-hand IDs belong to **#3730**; `I001`–`I159` on the right belong to **this issue**. Every one of #3730's 174 entries appears once. A mapping denotes preserved research scope, **not completed research**. Scope extensions above are part of their target investigations; no original I001–I144 entry is removed or renumbered.

| #3730 ID | Suggestion | Consolidated destination |
| --- | --- | --- |
| A01 | Minimum sufficient generation identity | I145 |
| A02 | Locators versus semantic generations | I011, I034, I079, I145 |
| A03 | Mixed-generation race matrix | I013, I051, I134, I138 |
| A04 | Late publication after cancellation | I053, I106 |
| A05 | Snapshot retention versus recomputation | I047, I146 |
| A06 | Historical query semantics | I047, I146 |
| A07 | Cross-process reconstruction | I016, I110 |
| A08 | Hashes versus monotonic revisions | I011, I079, I097, I145 |
| B01 | Exact projection model | I026 |
| B02 | Executed round-trip corpus | I025, I026, I032 |
| B03 | UTF-16 stress tests | I025, I062 |
| B04 | Incremental projection algorithm | I032 |
| B05 | Host-only edits shift source positions | I029, I032 |
| B06 | Delimiter corruption and partial syntax | I017, I046 |
| B07 | Multiple-annotation document granularity | I022, I035 |
| B08 | Name visibility and namespaces | I022, I037 |
| B09 | Embedded import-header ownership | I018, I022, I091 |
| B10 | Authored versus generated edits | I026, I027, I030, I069 |
| B11 | Code actions and rename | I030, I059, I060 |
| B12 | Hover/completion/tokens/signature help/inlay hints | I030, I059, I062 |
| B13 | Diagnostic responsibility versus editability | I027, I031 |
| B14 | Macro-generated annotations | I019, I087 |
| B15 | Unsaved host as proof authority | I012, I068, I137, I155 |
| C01 | Version-bound goal wrapper | I041, I045, I048, I145 |
| C02 | Rich RPC versus plainGoal | I043, I044, I046 |
| C03 | Worker-restart freshness barrier | I049 |
| C04 | Server launch-mode comparison | I049 |
| C05 | Changed artifact with unchanged source | I147 |
| C06 | Changed source with identical rebuilt artifact | I147 |
| C07 | Import additions/removals/renames | I051, I055 |
| C08 | RPC and handle lifetimes | I044, I045, I047, I122 |
| C09 | Concurrent goal queries in one document | I041, I134 |
| C10 | Many proofs importing one model | I050, I056 |
| C11 | Importing another live proof | I038, I039 |
| C12 | Semantic-readiness alternatives | I042, I048 |
| C13 | Partial-file elaboration | I046 |
| C14 | Diagnostics/goal disagreement | I058, I129 |
| C15 | Crash recovery of unsaved text | I016, I110 |
| D01 | Saved Rust versus overlays | I073, I074 |
| D02 | Overlay path sensitivity | I074 |
| D03 | Cargo reuse with materialized snapshots | I075, I080 |
| D04 | Charon process lifetime | I077, I118 |
| D05 | Charon concurrent determinism | I079, I148 |
| D06 | Charon cancellation cleanup | I078, I080, I105 |
| D07 | Compilation-subject invalidation matrix | I009, I020, I076 |
| D08 | Annotation-only upstream bypass | I018 |
| D09 | Compilation-affecting annotations | I018, I019 |
| D10 | Stable item correspondence across edits | I019, I021, I149 |
| E01 | Warm Aeneas without semantic reuse | I081, I118 |
| E02 | Global-state reset audit | I081, I088 |
| E03 | In-process concurrent Aeneas requests | I081 |
| E04 | Transactional generated-tree replacement | I051, I052, I085 |
| E05 | Declaration deletion and rename | I055, I085 |
| E06 | Generated-source determinism | I148 |
| E07 | Semantic sameness with textual instability | I079, I084, I132, I148 |
| E08 | Output-to-model manifest | I149 |
| E09 | Generated versus external-model ownership | I024, I085 |
| E10 | External model changes without codegen changes | I050, I082, I147 |
| E11 | Restricted finer-grained Aeneas prototype | I083 |
| E12 | Failure during generation and fallback | I054, I085, I088 |
| F01 | Prepared-environment schema | I090, I091, I150 |
| F02 | Real read-only archive/server probe | I089 |
| F03 | 4.30 versus later Lake ownership | I094, I158 |
| F04 | Real-archive missing-manifest control | I089 |
| F05 | Prepared-environment identity collisions | I090, I096, I145 |
| F06 | Server artifact completeness | I098, I150 |
| F07 | No-build/no-cache fail-closed path | I092 |
| F08 | Build completion versus server readiness | I042, I089, I091 |
| F09 | Unsaved import changes | I091 |
| F10 | Cache-hit and rebuild observability | I095 |
| F11 | Artifact-cache writer crash consistency | I102 |
| F12 | Shared package-directory writer crashes | I108, I151 |
| F13 | Read-only producer/many consumers | I089, I114, I139 |
| F14 | Consumer/toolchain relocation separately and together | I101 |
| F15 | Final-location preparation versus rename | I052 |
| F16 | Network-denied consumption | I104 |
| F17 | User-cache contamination | I096, I104 |
| F18 | Timestamp perturbations | I100 |
| F19 | Clean oracle for interactive setup | I099, I131, I132 |
| F20 | Generated-module rebuild isolation | I089, I113 |
| G01 | Explicit transport-independent MCP handles | I065, I066, I145 |
| G02 | Handle expiry and stale-generation failures | I044, I047, I122, I145 |
| G03 | Long-running MCP tasks | I065, I071 |
| G04 | Subscriptions for diagnostics/progress | I152 |
| G05 | Concurrent agents in one workspace | I014, I067, I068 |
| G06 | Version-checked agent patch transaction | I029, I070, I137 |
| G07 | Scratch tactic trials and reuse | I040, I070, I116, I153 |
| G08 | Scratch environment fidelity | I040 |
| G09 | Read-only versus mutating tools | I069, I126 |
| G10 | MCP multiplexing/process isolation | I004, I153 |
| G11 | Edit/setup authorization taxonomy | I069 |
| G12 | Response provenance envelope | I066, I145 |
| G13 | Retry and idempotency | I067 |
| G14 | MCP cancellation races | I071, I105, I106 |
| G15 | Agent navigation Rust-to-Lean-and-back | I066, I140, I149 |
| H01 | Virtual document URI strategy | I033, I034, I155 |
| H02 | Custom URI versus setup-file | I033, I155 |
| H03 | Shadow-file authority and recovery | I155 |
| H04 | Hidden Lean document lifecycle | I033, I064, I155 |
| H05 | Different unsaved editor clients | I014, I068 |
| H06 | Save versus existing unsaved generation | I063 |
| H07 | Rename/move with open proof | I021, I034, I063, I155 |
| H08 | Workspace-folder/project switch | I004, I057, I153 |
| H09 | Editor cancellation through scheduler | I007, I105, I107 |
| H10 | Stale diagnostics during regeneration | I054, I058, I141 |
| I01 | Batch/fresh/warm/edited/restarted equivalence | I001, I131, I132 |
| I02 | Actual batch/live import identity | I048, I099, I131 |
| I03 | Live acceptance followed by fresh verification | I131, I137, I138 |
| I04 | Batch acceptance followed by cold interactive use | I089, I091, I131 |
| I05 | Verification scope across live transitions | I129, I138, I144 |
| I06 | No goals versus theorem/file/project acceptance | I129 |
| I07 | TCB identity under reuse | I130 |
| I08 | Development/partial-result taint | I130, I141 |
| J01 | Real generated-project disk scaling | I113, I114, I139 |
| J02 | Every copied byte classified | I113 |
| J03 | Real-import server memory scaling | I114, I117, I153 |
| J04 | One watchdog/many documents versus many servers | I153 |
| J05 | Prewarmed scratch pool scaling | I116, I153 |
| J06 | Nested parallelism budget | I115 |
| J07 | Cold/warm latency decomposition | I118 |
| J08 | Test/fixture/suite reuse granularity | I154 |
| J09 | Failures under high concurrency | I105, I110, I139 |
| J10 | Long-lived daemon resource drift | I116, I122 |
| J11 | Generation collection with live readers | I121 |
| J12 | Cross-test contamination sentinels | I135, I154 |
| J13 | Concurrent identical cache misses | I102, I107 |
| J14 | Filesystem-specific resource scaling | I119, I124 |
| J15 | Resource limits and stale-success fallback | I109, I129 |
| K01 | Exact pre-compiler proof-range sidecar | I025, I026, I149 |
| K02 | Cross-layer declaration manifest | I149 |
| K03 | Macro provenance/edit responsibility | I019, I031 |
| K04 | Synthetic-scaffolding blame evaluation | I031, I141 |
| K05 | Relocation and normalized diagnostic identities | I059, I101, I123 |
| K06 | Owning range deleted during query | I021, I029 |
| K07 | Rustfmt and proof-map stability | I032, I063 |
| K08 | Stable proof identity through model regeneration | I024, I034, I056, I155 |
| L01 | Structured stage results | I006, I145 |
| L02 | Backend filesystem-effects inventory | I006, I113 |
| L03 | Progress independent of UI | I006, I095 |
| L04 | Cancellation abstraction fit | I007, I105 |
| L05 | Backend crash/retry reconstruction | I077, I081, I110 |
| L06 | Backend version/capability negotiation | I156 |
| L07 | Batch shell over shared engine | I157 |
| L08 | Transport-free interactive shell | I157 |
| L09 | Direct Lean backend versus MCP delegation | I072 |
| L10 | Aeneas library embedding | I081, I086 |
| M01 | Interactive invariants on upgraded Lean/Lake | I094, I136, I158 |
| M02 | Minimal interactive upgrade checklist | I158 |
| M03 | Charon upgrade checklist | I158 |
| M04 | Aeneas upgrade checklist | I158 |
| M05 | Golden replay across toolchain tuples | I136, I158 |
| M06 | Probes for deleting obsolete workarounds | I100, I142, I158 |
| N01 | Challenge path-only identity | I159 |
| N02 | Challenge document-version-only identity | I159 |
| N03 | Try supported refresh without restart | I159 |
| N04 | Try one server for conflicting workspaces | I159 |
| N05 | Try shared writable generated build state | I159 |
| N06 | Try artifact-cache-only reconstruction | I159 |
| N07 | Try renaming a prepared generation | I159 |
| N08 | Try generated Lean as canonical proof source | I159 |
| N09 | Try span-only editable-range recovery | I159 |
| N10 | Challenge universal proof-only bypass | I159 |
| N11 | Challenge no-goals-as-success | I159 |
| N12 | Challenge cancellation-only freshness | I159 |
| O01 | Synthesize state machine and invariants | I144 |
| O02 | Synthesize invalidation matrix | I144 |
| O03 | Synthesize stable/ephemeral identity model | I144, I145 |
| O04 | Synthesize ownership/projection contract | I144 |
| O05 | Synthesize prepared producer/consumer contract | I144, I150 |
| O06 | Synthesize exact proof-query contract | I144 |
| O07 | Synthesize MCP semantic API | I144 |
| O08 | Synthesize LSP semantic API | I144 |
| O09 | Synthesize measured test-resource architecture | I144 |
| O10 | Synthesize batch/live equivalence contract | I144 |

## Combined sequencing, shared harnesses, and readiness questions

The original first tranche remains useful. #3730 adds the following complementary execution sequence, now expressed in consolidated IDs:

1. Establish stale-state correctness with I145/I134/I049/I089/I092/I131.
2. Establish exact user-proof projection with I025–I026/I068, then I137.
3. Establish real prepared-environment identity and scalability with I089–I090/I098/I113–I115/I153.
4. Exercise the explicit MCP workspace and concurrent patch loop with I065/I014/I029/I070/I145.
5. Sharpen proof-only classification and backend lifetimes with I018–I021/I081/I051.
6. Challenge the resulting design using I159's twelve controls.
7. Synthesize I144's ten contracts only after enough execution evidence exists.

Avoid rebuilding separate harnesses for tightly coupled questions. A dependency-refresh harness can answer I049/I147/I055; a real-archive consumer harness can answer I089/I098/I092/I091/I101/I104; a parallel integration harness can answer I113/I114/I115/I139/I107; a projection/coordinate harness can answer I025/I026/I032; and a concurrent-agent harness can answer I014/I029/I067/I071. These groupings preserve different evidence scopes and do not imply one passing fixture answers every item.

Before freezing the affected v2 scaffolding, seek pinned answers to all ten questions retained from #3730:

| Question | Main evidence destinations |
| --- | --- |
| What identifies the exact source/model/environment used for a result? | I009, I048, I145, I149 |
| What establishes that the result is current rather than stale? | I041, I048–I050, I134 |
| Which edits stay Lean-only, and which invalidate upstream/build state? | I018, I056, I073, I083, I091 |
| How do embedded positions and edits map exactly to canonical authored bytes? | I019, I025–I032 |
| What is immutable, per-consumer mutable, or explicitly safe to share writable? | I089–I093, I102, I150–I151 |
| What must refresh or restart after generated imports change? | I049–I050, I147 |
| How do batch and live checks cross-check one another? | I001, I099, I131–I132, I137–I138 |
| How do many tests/agents avoid dependency duplication and shared-state corruption? | I080, I107, I113–I124, I139, I153–I154 |
| Which handles/results survive restart and which expire? | I016, I044–I048, I110, I121–I122, I145–I146 |
| Which conclusions are pin-specific, and which are durable cross-version contracts? | I094, I136, I144, I158 |

For every selected investigation, preserve its exact subject, hypothesis, confirming and falsifying observations, strongest feasible evidence method, and the design choice its result changes. Distinguish byte equality, build freshness, elaboration equivalence, theorem acceptance, semantic equivalence, and Rust-level claim equivalence. Repeated/racing tests need negative controls and interruption evidence; source inspection, unrun scripts, and a successful isolated run do not supply stronger execution or proof claims.

There are **159 consolidated investigation IDs**, not a requirement for 159 report packages. The 64 scope extensions are part of existing IDs, and the 174-row crosswalk is a provenance/coverage aid, not a second work-status system. All suggestions from both agendas remain in this issue; #3730 remains historical provenance.

*Agent origin: ChatGPT, 2026-09-29; direct conversation locator unavailable. Consolidated at Josh Liebow-Feeser's request; research proposals remain unadopted.*