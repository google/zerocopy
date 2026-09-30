# Aeneas compatible-bundle drift tranche — source review only

Baseline report catalog: `reference@ebcdcad`, 581 packages. This tranche covers **169 unique report packages**: **150** selected by Aeneas in the inventory cohort or `REPORT.json` subjects, plus **19** additional reports whose title/first claim explicitly names Aeneas. The companion CSV preserves both selection bases. The 169 rows are classified as 60 direct/full-bundle, 35 paired-Charon, 16 paired-Lean, and 58 contextual. Contextual rows remain in the inventory to prevent a cited Aeneas pin from silently becoming a claim that Aeneas runtime behavior changed.

Files: [`claim-matrix-ebcdcad-169.csv`](claim-matrix-ebcdcad-169.csv) is the claim-by-claim matrix; [`source-deltas.md`](source-deltas.md) records exact bundle pins and source evidence; [`source-path-diff.csv`](source-path-diff.csv) records complete Git-blob path drift for Aeneas and paired Charon. All files are scratch artifacts in this Data directory.

No new binary or package was installed or executed. Current-source additions such as `translation.json`, default Lean module output, and Charon `ItemMeta.started_from` are source/schema observations. Every current-fixture outcome remains untested. The report-level CSV identifies the exact original section, first claim, applicable source delta codes, bounded follow-up, and required toolchain.

## Coverage by source relation

- `direct_or_full_bundle`: 60
- `paired_charon`: 35
- `paired_lean`: 16
- `contextual`: 58

## Report index

### direct_or_full_bundle

- R003 `reports/aeneas-architecture-translation-pipeline-nightly-2026-06-03/REPORT.md` — ## Summary; ### Types, globals, signatures, functions, traits, and impls have separate translation steps; deltas `P0,A1,C1,A2,L1,A6,C2`; yes_for_new_runtime_or_package_claim.
- R004 `reports/aeneas-charon-compatibility-nightly-2026-06-03/REPORT.md` — ## Summary; ## Findings; deltas `P0,A2,L1,A7,C2,C1`; yes_for_new_runtime_or_package_claim.
- R005 `reports/aeneas-concurrent-generation-determinism-nightly-2026-06-03/REPORT.md` — ## Summary; ## Findings; deltas `P0,A2,L1,C1,C2`; yes_for_new_runtime_or_package_claim.
- R006 `reports/aeneas-external-models-nightly-2026-06-03/REPORT.md` — ## Summary; ### Missing external models have an explicit template workflow; deltas `P0,A1,C1,A2,L1,A3,A4,A5,A6`; yes_for_new_runtime_or_package_claim.
- R007 `reports/aeneas-extrinsic-termination-nightly-2026-06-03/REPORT.md` — ## Summary; ### Translation-time and proof-time termination answer different questions; deltas `P0,A1,C1,A2,L1,A5`; yes_for_new_runtime_or_package_claim.
- R009 `reports/aeneas-generated-function-signatures-nightly-2026-06-03/REPORT.md` — ## Summary; ### Generated value arguments come from the pure translated function, not the Rust surface signature verbatim; deltas `P0,A1,C1,A2,L1,A3,A4,A5,A6,C2`; yes_for_new_runtime_or_package_claim.
- R010 `reports/aeneas-generated-function-specifications-nightly-2026-06-03/REPORT.md` — ## Summary; ### The generated function signature is assembled in two stages; deltas `P0,A1,C1,A2,L1,A3,A5,A6,C2`; yes_for_new_runtime_or_package_claim.
- R011 `reports/aeneas-generated-lean-stability-near-nightly-2026-06-03/REPORT.md` — ## Summary; ### Textual generated-source stability and proof-environment stability are separate; deltas `P0,A1,C1,A2,L1,A4,A6,A7,C2`; yes_for_new_runtime_or_package_claim.
- R012 `reports/aeneas-generated-source-determinism-nightly-2026-06-03/REPORT.md` — ## Summary; ### The upstream generated-output tests intentionally do not exercise default parallelism; deltas `P0,A1,C1,A2,L1,A4,A5,A6,C2`; yes_for_new_runtime_or_package_claim.
- R013 `reports/aeneas-generated-source-repeat-run-probe-nightly-2026-06-03/REPORT.md` — ## Summary; ### Proposed bounded follow-up probe; deltas `P0,A1,C1,A2,L1,C2`; yes_for_new_runtime_or_package_claim.
- R014 `reports/aeneas-incremental-translation-feasibility-nightly-2026-06-03/REPORT.md` — ## Summary; ### The source's use of “incremental” inside the interpreter is unrelated to incremental crate translation; deltas `P0,A1,C1`; yes_for_new_runtime_or_package_claim.
- R015 `reports/aeneas-infinite-diverging-execution-nightly-2026-06-03/REPORT.md` — ## Summary; ## Findings; deltas `P0,A1,C1,A2,L1,A5`; yes_for_new_runtime_or_package_claim.
- R016 `reports/aeneas-lean-project-package-anatomy-nightly-2026-06-03/REPORT.md` — ## Summary; ### Upstream documentation expects the consumer to create a Lean project around generated files; deltas `P0,A1,C1,A2,L1,A6`; yes_for_new_runtime_or_package_claim.
- R017 `reports/aeneas-library-process-architecture-nightly-2026-06-03/REPORT.md` — ## Summary; ### The CLI is a thin process boundary around the public library; deltas `P0,A1,C1,A4,A7,C2`; yes_for_new_runtime_or_package_claim.
- R018 `reports/aeneas-loops-nightly-2026-06-03/REPORT.md` — ## Summary; ### Non-structural loops become `loop body initial_state`; deltas `P0,A2,L1,A5`; yes_for_new_runtime_or_package_claim.
- R019 `reports/aeneas-nested-borrow-flaky-repro-nightly-2026-06-03/REPORT.md` — ## Summary; ### The same pinned release still has explicit unsupported nested-borrow paths; deltas `P0,A5`; yes_for_new_runtime_or_package_claim.
- R020 `reports/aeneas-panic-error-unwind-nightly-2026-06-03/REPORT.md` — ## Summary; ### The pure translation turns the symbolic panic channel into `Result.fail`; deltas `P0,A1,C1,A2,L1,A5`; yes_for_new_runtime_or_package_claim.
- R021 `reports/aeneas-partial-functions-nightly-2026-06-03/REPORT.md` — ## Summary; ### Aeneas marks recursive Lean functions with `partial_fixpoint`; deltas `P0,A1,C1,A2,L1,A5,A6`; yes_for_new_runtime_or_package_claim.
- R022 `reports/aeneas-post-monomorphization-errors-nightly-2026-06-03/REPORT.md` — ## Summary; ### The required Aeneas preset does not request full monomorphization; deltas `P0,A3`; yes_for_new_runtime_or_package_claim.
- R023 `reports/aeneas-raw-pointers-nightly-2026-06-03/REPORT.md` — ## Summary; ### Raw pointers survive type translation as marker types; deltas `P0,A2,L1,A3,A5,A6,C1,C2`; yes_for_new_runtime_or_package_claim.
- R024 `reports/aeneas-recursion-termination-nightly-2026-06-03/REPORT.md` — ## Summary; ### Recursive specification proofs have a separate Lean termination check; deltas `P0,A2,L1,A5`; yes_for_new_runtime_or_package_claim.
- R025 `reports/aeneas-release-archive-anatomy-nightly-2026-06-03/REPORT.md` — ## Summary; ### The release archive does not bundle the Lean toolchain; deltas `P0,A2,L1,A6,A7,C2,C1`; yes_for_new_runtime_or_package_claim.
- R026 `reports/aeneas-release-upgrade-checklist-nightly-2026-06-03/REPORT.md` — ## Summary; ### 5. Check the release artifact that Anneal will actually ship; deltas `P0,A2,L1,A3,A7,C2,C1`; yes_for_new_runtime_or_package_claim.
- R027 `reports/aeneas-resource-semantics-nightly-2026-06-03/REPORT.md` — ## Summary; ### The existing lifetime result and this resource boundary are complementary; deltas `P0,A1,C1,A2,L1,A5,A6`; yes_for_new_runtime_or_package_claim.
- R028 `reports/aeneas-rust-comment-preservation-nightly-2026-06-03/REPORT.md` — ## Summary; ### Charon item metadata is richer than Aeneas's generated comment surface; deltas `P0,A1,C1,A2,L1,A4,A5`; yes_for_new_runtime_or_package_claim.
- R029 `reports/aeneas-rust-lean-naming-nightly-2026-06-03/REPORT.md` — ## Summary; ### Types, variants, fields, and constructors use Lean-specific naming rules; deltas `P0,A1,C1,A2,L1,A4,C2`; yes_for_new_runtime_or_package_claim.
- R030 `reports/aeneas-rust-support-failure-matrix-nightly-2026-06-03/REPORT.md` — ## Summary; ### Panic/failure is represented, but this report does not widen that into full unwind support; deltas `P0,A7,C2`; yes_for_new_runtime_or_package_claim.
- R031 `reports/aeneas-rust-to-lean-translation-nightly-2026-06-03/REPORT.md` — ## Summary; ### Per-function Aeneas translation can fail instead of producing a pure declaration; deltas `P0,A1,C1,A2,L1,A5,A7,C2`; yes_for_new_runtime_or_package_claim.
- R032 `reports/aeneas-rust-type-shapes-nightly-2026-06-03/REPORT.md` — ## Summary; ### The core Rust-to-Lean type map at this pin; deltas `P0,A2,L1,C1,C2`; yes_for_new_runtime_or_package_claim.
- R033 `reports/aeneas-semantic-omissions-unsafe-rust-nightly-2026-06-03/REPORT.md` — ## Summary; ### The advertised semantic domain excludes general unsafe and concurrent Rust; deltas `P0,A1,C1,A2,L1,A5,A6`; yes_for_new_runtime_or_package_claim.
- R035 `reports/aeneas-trait-translation-nightly-2026-06-03/REPORT.md` — ## Summary; ### Dynamic trait evidence is rejected in the functional translation; deltas `P0,A1,C1,A2,L1,A3,A4`; yes_for_new_runtime_or_package_claim.
- R036 `reports/aeneas-translation-correctness-obligations-nightly-2026-06-03/REPORT.md` — ## Summary; ### The ordinary functional backend's advertised domain limits the correctness claim; deltas `P0,A1,C1,A2,L1,A5,A6,C2`; yes_for_new_runtime_or_package_claim.
- R037 `reports/aeneas-trusted-base-nightly-2026-06-03/REPORT.md` — ## Summary; ### Charon and rustc are trusted for the Rust-to-LLBC bridge; deltas `P0,A1,C1,A2,L1`; yes_for_new_runtime_or_package_claim.
- R038 `reports/aeneas-type-alias-handling-nightly-2026-06-03/REPORT.md` — ## Summary; ### Generated Lean for `OptNode` contains the underlying type and no alias declaration; deltas `P0,A1,C1,A2,L1,A3,A5,C2`; yes_for_new_runtime_or_package_claim.
- R039 `reports/aeneas-wp-proof-tools-nightly-2026-06-03/REPORT.md` — ## Summary; ### Preconditions are proof obligations, not assumptions silently granted by `step`; deltas `P0,A1,C1,A2,L1,A3,A6`; yes_for_new_runtime_or_package_claim.
- R112 `reports/anneal-3730-acceptance-oracle-matrix-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0,A1,C1,A2,L1,A6`; yes_for_new_runtime_or_package_claim.
- R113 `reports/anneal-3730-aeneas-handoff-memory-vs-files-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0,A1,C1,A2,L1,A6,C2`; yes_for_new_runtime_or_package_claim.
- R114 `reports/anneal-3730-aeneas-identity-manifest-2026-09-29/REPORT.md` — ## Summary; deltas `P0,A1,C1,A2,L1,A3,A4,A5,C2`; yes_for_new_runtime_or_package_claim.
- R115 `reports/anneal-3730-aeneas-manifest-batch-oracle-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0,A1,C1,A2,L1,C2`; yes_for_new_runtime_or_package_claim.
- R116 `reports/anneal-3730-aeneas-namespace-move-proof-context-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0,A1,C1,A2,L1,A4,A6`; yes_for_new_runtime_or_package_claim.
- R117 `reports/anneal-3730-aeneas-process-contract-2026-09-29/REPORT.md` — ## Summary; ### Source API exposes translation stages but not a request-isolated host contract; deltas `P0,A1,C1,A7,C2`; yes_for_new_runtime_or_package_claim.
- R118 `reports/anneal-3730-aeneas-restricted-reuse-2026-09-29/REPORT.md` — ## Summary; ### Observed output graph and reuse fence; deltas `P0,A1,C1,A2,L1,A3,A6,C2`; yes_for_new_runtime_or_package_claim.
- R119 `reports/anneal-3730-aeneas-trait-output-shrink-matrix-2026-09-29/REPORT.md` — ## Summary; ### Translation, output ownership, and fresh consumers; deltas `P0,A1,C1,A2,L1,A3,A4,C2`; yes_for_new_runtime_or_package_claim.
- R126 `reports/anneal-3730-charon-aeneas-boundary-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0,A1,C1,A2,L1,A4,A7,C2`; yes_for_new_runtime_or_package_claim.
- R130 `reports/anneal-3730-charon-shortname-aeneas-impact-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0,A1,C1,A2,L1,A4,C2`; yes_for_new_runtime_or_package_claim.
- R137 `reports/anneal-3730-combined-pipeline-concurrency-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0,A1,C1,A2,L1,A5,A6,C2`; yes_for_new_runtime_or_package_claim.
- R141 `reports/anneal-3730-cross-tool-provenance-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0,A1,C1,A2,L1,A5,A6,C2`; yes_for_new_runtime_or_package_claim.
- R147 `reports/anneal-3730-external-model-without-codegen-change-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0,A1,C1,A2,L1,A6,C2`; yes_for_new_runtime_or_package_claim.
- R162 `reports/anneal-3730-independent-vertical-reproduction-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0,A1,C1,A2,L1,A6`; yes_for_new_runtime_or_package_claim.
- R213 `reports/anneal-3730-pinned-cross-layer-navigation-boundary-2026-09-29/REPORT.md` — opening paragraphs after H1; ## Executed navigation and goal observations; deltas `P0,A1,C1,A4,A5,C2`; yes_for_new_runtime_or_package_claim.
- R225 `reports/anneal-3730-retained-full-chain-byte-timing-inventory-2026-09-29/REPORT.md` — ## Summary; deltas `P0,A1,C1,A2,L1,C2`; yes_for_new_runtime_or_package_claim.
- R228 `reports/anneal-3730-rust-charon-aeneas-lean-golden-vertical-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0,A2,L1,C1,C2`; yes_for_new_runtime_or_package_claim.
- R237 `reports/anneal-3730-shared-generator-batch-live-sinks-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; yes_for_new_runtime_or_package_claim.
- R239 `reports/anneal-3730-source-owned-projection-diagnostic-matrix-2026-09-29/REPORT.md` — ## Summary; ## Unicode and batch/live diagnostic comparison; deltas `P0`; yes_for_new_runtime_or_package_claim.
- R242 `reports/anneal-3730-vertical-acceptance-v4-30-0-rc2/REPORT.md` — ## Summary; ## Findings; deltas `P0,A1,C1,A2,L1,A6`; yes_for_new_runtime_or_package_claim.
- R243 `reports/anneal-3731-aeneas-declaration-block-diff-2026-09-29/REPORT.md` — ## Summary; deltas `P0,A1,C1,A2,L1,A7,C2`; yes_for_new_runtime_or_package_claim.
- R246 `reports/anneal-3731-embedded-proof-generated-model-vertical-v4-30-0-rc2/REPORT.md` — ## Summary; ### One live proof edit against a retained generated context; deltas `P0,A1,C1,A2,L1,A6,C2`; yes_for_new_runtime_or_package_claim.
- R247 `reports/anneal-3731-full-chain-transient-workspace-accounting-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0,A2,L1,C1,C2`; yes_for_new_runtime_or_package_claim.
- R532 `reports/rust-lifetimes-charon-aeneas-nightly-2026-05-31/REPORT.md` — ## Summary; ### Signature lifetimes are converted into region groups and parent relationships; deltas `P0,A7,C2,C1`; yes_for_new_runtime_or_package_claim.
- R533 `reports/rust-llbc-lean-golden-and-aeneas-revision-probes-2026-09-28/REPORT.md` — ## Summary; ### Relation to deterministic-output probes; deltas `P0,A1,C1,A2,L1,A5,A7,C2`; yes_for_new_runtime_or_package_claim.

### paired_charon

- R244 `reports/anneal-3731-charon-relocation-comment-provenance-2026-09-29/REPORT.md` — ## Summary; ### Relocation carries through both artifacts; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R350 `reports/cargo-rust-charon-anneal-coverage-matrix-2026-09-28/REPORT.md` — ## Summary; ## Findings; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R353 `reports/charon-async-coroutines-0-1-210/REPORT.md` — ## Summary; ### `async fn` coverage cannot be inferred from successful translation of its callers; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R354 `reports/charon-cli-invocation-modes-0-1-210/REPORT.md` — ## Summary; ### `charon cargo` delegates the actual build invocation to `cargo build`; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R355 `reports/charon-closures-0-1-210/REPORT.md` — ## Summary; ### Non-capturing closures can be translated to ordinary function-pointer targets; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R356 `reports/charon-closures-nightly-2026-06-03/REPORT.md` — ## Summary; ### Non-capturing closures can be translated to ordinary function-pointer targets; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R357 `reports/charon-constants-statics-associated-constants-0-1-210/REPORT.md` — ## Summary; ### Trait declarations give associated constants typed slots with optional defaults; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R358 `reports/charon-dependency-and-source-coverage-nightly-2026-06-03/REPORT.md` — ## Summary; ### “Whole current crate” is structural coverage, not source-text coverage; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R359 `reports/charon-drop-destructor-semantics-0-1-210/REPORT.md` — ## Summary; ### A synthetic drop-glue body can include the user destructor and field destructors; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R360 `reports/charon-entry-selection-opacity-0-1-210/REPORT.md` — ## Summary; ### Source annotations can only strengthen opacity relative to CLI matching; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R361 `reports/charon-enum-layout-0-1-210/REPORT.md` — ## Summary; ### The pinned layout test checks tagger/discriminator consistency for every inhabited variant; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R362 `reports/charon-extraction-scaling-nightly-2026-06-03/REPORT.md` — ## Summary; ## Findings; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R363 `reports/charon-incremental-capabilities-0-1-210/REPORT.md` — ## Summary; ### Charon item IDs are allocated during the fresh traversal, not presented as a cross-run incremental identity; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R364 `reports/charon-intrinsics-0-1-210/REPORT.md` — ## Summary; ## Findings; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R365 `reports/charon-item-identity-spans-comments-nightly-2026-06-03/REPORT.md` — ## Summary; ### Item metadata carries source identity/provenance information separately; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R366 `reports/charon-library-process-server-0-1-210/REPORT.md` — ## Summary; ### The current library/process split offers three different integration choices; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R367 `reports/charon-library-wire-compatibility-0-1-210/REPORT.md` — ## Summary; ### The wire-version identifier is the Cargo package version; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R368 `reports/charon-llbc-output-goldens-and-revision-diffs-2026-09-27/REPORT.md` — ## Summary; ### Proposed revision-diff harness; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R369 `reports/charon-multi-target-cargo-behavior-0-1-210/REPORT.md` — ## Summary; ### Multi-target merge preserves the first crate name as the merged crate name; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R370 `reports/charon-opaque-nightly-2026-06-03/REPORT.md` — ## Summary; ### `--opaque` patterns are prefix patterns; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R371 `reports/charon-performance-and-revision-probes-2026-09-28/REPORT.md` — ## Summary; ### Charon revision comparison and golden normalization; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R372 `reports/charon-raw-pointers-unsafe-operations-0-1-210/REPORT.md` — ## Summary; ### Unsafe trait and unsafe impl qualifiers are absent from the semantic trait nodes; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R373 `reports/charon-release-upgrade-checklist-0-1-210/REPORT.md` — ## Summary; ### 10. Separate same-revision determinism from upgrade drift; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R374 `reports/charon-serialization-compatibility-api-0-1-210/REPORT.md` — ## Summary; ### Serialization can hash-cons repeated AST values without changing the semantic API; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R375 `reports/charon-start-from-nightly-2026-06-03/REPORT.md` — ## Summary; ### `--start-from` and `--start-from-if-exists` differ only in strictness after parsing; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R376 `reports/charon-support-and-unsoundness-nightly-2026-06-03/REPORT.md` — ## Summary; ### A formerly documented bound-lifetime trait-resolution unsoundness is historical, not pinned-active evidence; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R377 `reports/charon-toolchain-contract-0-1-210/REPORT.md` — ## Summary; ### `charon_lib` without rustc integration has a different toolchain requirement; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R378 `reports/charon-toolchain-requirements-nightly-2026-06-03/REPORT.md` — ## Summary; ## Findings; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R379 `reports/charon-traits-generics-nightly-2026-06-03/REPORT.md` — ## Summary; ### Trait aliases are represented as traits whose content is their implied clauses; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R380 `reports/charon-ullbc-llbc-schema-nightly-2026-06-03/REPORT.md` — ## Summary; ### ULLBC→LLBC reconstructs control flow, including loops and branch joins; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R381 `reports/charon-unions-0-1-210/REPORT.md` — ## Summary; ### Transparent unions have a first-class type-declaration kind; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R382 `reports/charon-zerocopy-library-repeat-order-nightly-2026-05-31/REPORT.md` — ## Summary; ## Findings; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R387 `reports/cross-tool-diagnostic-path-normalization-2026-09-27/REPORT.md` — ## Summary; ### When Charon cannot recover a local path, it uses rustc's macro-scope representation; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R388 `reports/cross-tool-utf8-span-columns-2026-09-27/REPORT.md` — ## Summary; ### Rustc distinguishes byte positions, character columns, and display columns; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.
- R563 `reports/rustc-mir-before-charon-nightly-2026-05-31/REPORT.md` — ## Summary; ### Charon's rustc flags suppress major optimization-only unreachable propagation; deltas `P0,C1,C2`; yes_for_charon_cell_aeneas_downstream_conditional.

### paired_lean

- R142 `reports/anneal-3730-cross-tool-stage-cancellation-cleanup-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R153 `reports/anneal-3730-full-lake-server-chain-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R201 `reports/anneal-3730-m06-generated-lake-source-order-trace-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0,L1,A2`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R325 `reports/anneal-v1-clean-workspace-prebuilt-archive-41f5b37/REPORT.md` — ## Summary; ### The regression test begins from a genuinely fresh consumer workspace; deltas `P0,L1,A2`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R329 `reports/anneal-v1-generated-lean-abi-main-41f5b37/REPORT.md` — ## Summary; ### V1 carries concrete syntax-compatibility patches for generated Aeneas files; deltas `P0,L1,A2`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R415 `reports/lake-behavior-upgrade-checklist-v4-30-0-rc2/REPORT.md` — ## Summary; ### 9. Revalidate `lake serve` and `lake setup-file` as a distinct interactive path; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R431 `reports/lake-package-tree-pruning-v4-30-0-rc2/REPORT.md` — ## Summary; ### The safe pruning unit is a consumer contract, not a package directory; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R452 `reports/lean-generated-file-interactive-workflows-v4-30-0-rc2/REPORT.md` — ## Summary; ### Interactive services need an explicit generated-package generation; deltas `P0,L1,A2`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R459 `reports/lean-lake-cross-platform-artifact-portability-v4-30-0-rc2/REPORT.md` — ## Summary; ### Lake's cache layers add additional platform fences; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R472 `reports/lean-package-native-artifacts-v4-30-0-rc2/REPORT.md` — ## Summary; ### Native artifacts can live in Lake's artifact cache rather than only in the package tree; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R476 `reports/lean-release-upgrade-checklist-v4-30-0-rc2/REPORT.md` — ## Summary; ## Findings; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R489 `reports/lean-v1-concurrent-workspace-server-reuse-2026-09-28/REPORT.md` — ## Summary; ## Findings; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R491 `reports/leantar-archive-format-v0-1-16-v0-1-19/REPORT.md` — ## Summary; ### `leantar` does not enforce extraction-path containment; deltas `P0,L1,A2`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R495 `reports/mathlib-cache-artifact-format-v4-30-0-rc2/REPORT.md` — ## Summary; ### One cache object corresponds to one module and is named by Mathlib's cache hash; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R497 `reports/mathlib-lake-exe-cache-protocol-v4-30-0-rc2/REPORT.md` — ## Summary; ### The network protocol is simple enough to mirror, but cache correctness is local-state dependent; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.
- R498 `reports/mathlib-release-cache-upgrade-checklist-v4-30-0-rc2/REPORT.md` — ## Summary; ### 3. Treat `lake exe cache` as a versioned Mathlib protocol; deltas `P0,L1`; yes_for_lean_cell_aeneas_regeneration_conditional.

### contextual

- R120 `reports/anneal-3730-agent-workflow-evaluation-v4-30-0-rc2/REPORT.md` — ## Summary; ### The complete agent path; deltas `P0`; conditional_citation_only.
- R121 `reports/anneal-3730-annotation-gap-probes-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0`; conditional_citation_only.
- R122 `reports/anneal-3730-annotation-subject-boundary-matrix-2026-09-29/REPORT.md` — ## Summary; ## Issue and #3730 B-row crosswalk; deltas `P0`; conditional_citation_only.
- R136 `reports/anneal-3730-cli-graceful-cancel-signals-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R138 `reports/anneal-3730-compatible-bundle-upgrade-golden-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R139 `reports/anneal-3730-cross-layer-comparator-mutants-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R140 `reports/anneal-3730-cross-tool-active-cancellation-barriers-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R150 `reports/anneal-3730-filesystem-sharing-apfs-v4-30-0-rc2/REPORT.md` — ## Summary; ## Findings; deltas `P0`; conditional_citation_only.
- R154 `reports/anneal-3730-generated-history-retention-economics-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R157 `reports/anneal-3730-h08-project-switch-router-v4-30-0-rc2/REPORT.md` — ## Summary; ### The project route kept A's unsaved worker state when returning; deltas `P0`; conditional_citation_only.
- R179 `reports/anneal-3730-last-good-model-after-rust-failure-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R180 `reports/anneal-3730-last-good-model-signature-recovery-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R207 `reports/anneal-3730-nested-parallelism-budget-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R209 `reports/anneal-3730-nested-unsaved-recovery-grid-v4-30-0-rc2/REPORT.md` — ## Summary; ## Findings; deltas `P0`; conditional_citation_only.
- R211 `reports/anneal-3730-partial-elaboration-queries-v4-30-0-rc2/REPORT.md` — ## Summary; ## Findings; deltas `P0`; conditional_citation_only.
- R216 `reports/anneal-3730-prefix-edit-cancellation-v4-30-0-rc2/REPORT.md` — ## Summary; ## Findings; deltas `P0`; conditional_citation_only.
- R219 `reports/anneal-3730-projection-provenance-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0`; conditional_citation_only.
- R223 `reports/anneal-3730-resource-economics-2026-09-29/REPORT.md` — ## Summary; ### Relation to remaining #3731 resource questions; deltas `P0`; conditional_citation_only.
- R224 `reports/anneal-3730-resource-soak-contamination-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0`; conditional_citation_only.
- R236 `reports/anneal-3730-shared-cargo-consumer-ownership-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R245 `reports/anneal-3731-compiler-backed-coordinate-bridge-2026-09-29/REPORT.md` — ## Summary; ### Real coordinate specimens; deltas `P0`; conditional_citation_only.
- R279 `reports/anneal-3731-i092-malformed-manifest-preflight-2026-09-30/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R289 `reports/anneal-3731-i147-syntax-equivalent-rebuild-2026-09-29/REPORT.md` — ## Summary; deltas `P0`; conditional_citation_only.
- R291 `reports/anneal-3731-i148-multifunction-translation-repeat-2026-09-29/REPORT.md` — opening paragraphs after H1; deltas `P0`; conditional_citation_only.
- R301 `reports/anneal-3731-reader-owned-generation-lease-v4-30-0-rc2/REPORT.md` — ## Summary; ## Findings; deltas `P0`; conditional_citation_only.
- R302 `reports/anneal-3731-real-generation-gc-lease-v4-30-0-rc2/REPORT.md` — ## Summary; ### Shared lease retains A for a later import; deltas `P0`; conditional_citation_only.
- R303 `reports/anneal-3731-real-generation-publication-v4-30-0-rc2/REPORT.md` — ## Summary; ### Staged publication and pinned old server; deltas `P0`; conditional_citation_only.
- R306 `reports/anneal-archive-read-only-behavior-main-41f5b37/REPORT.md` — ## Summary; ### Current test coverage does not prove every archive subtree is read-only after installation; deltas `P0`; conditional_citation_only.
- R308 `reports/anneal-cross-tool-error-provenance-specimens-v4-30-0-rc2/REPORT.md` — ## Summary; ## Findings; deltas `P0`; conditional_citation_only.
- R309 `reports/anneal-error-provenance-classification-nightly-2026-06-03-v4-30-0-rc2/REPORT.md` — ## Summary; ### Exit status is a stage-local fact, not a universal classification; deltas `P0`; conditional_citation_only.
- R310 `reports/anneal-external-crate-diagnostic-source-recovery-nightly-2026-05-31-main-41f5b37/REPORT.md` — ## Summary; ### There are three materially different recovery cases; deltas `P0`; conditional_citation_only.
- R311 `reports/anneal-host-platform-matrix-main-41f5b37/REPORT.md` — ## Summary; ### The upstream Aeneas release publishes the same four platform families; deltas `P0`; conditional_citation_only.
- R313 `reports/anneal-interactive-pipeline-invalidation-graph-main-41f5b37/REPORT.md` — ## Summary; ### Current V2 supplies identities but not an implemented interactive pipeline; deltas `P0`; conditional_citation_only.
- R314 `reports/anneal-linux-elf-relocation-main-41f5b37/REPORT.md` — ## Summary; ### The final archive deliberately performs its own Linux ELF rewrite; deltas `P0`; conditional_citation_only.
- R315 `reports/anneal-macos-macho-relocation-main-41f5b37/REPORT.md` — ## Summary; ### macOS dynamic loader; deltas `P0`; conditional_citation_only.
- R316 `reports/anneal-nix-fixed-output-downloads-main-41f5b37/REPORT.md` — ## Summary; ### `fetchurl` and recursive fixed-output derivations serve different shapes; deltas `P0`; conditional_citation_only.
- R317 `reports/anneal-nix-ifd-version-extraction-main-41f5b37/REPORT.md` — ## Summary; ### Rust version extraction is only round-tripped, not discovered; deltas `P0`; conditional_citation_only.
- R322 `reports/anneal-toolchain-version-coupling-main-41f5b37/REPORT.md` — ## Summary; ### `packages.test-ifd` does not make the ordinary toolchain fully Aeneas-derived; deltas `P0`; conditional_citation_only.
- R323 `reports/anneal-v1-abs-end-to-end-fail-closed-controls-2026-09-28/REPORT.md` — ## Summary; ### Rust compilation errors and false specifications fail at different stages; deltas `P0`; conditional_citation_only.
- R326 `reports/anneal-v1-contract-mutation-adequacy-2026-09-28/REPORT.md` — ## Summary; ### Mutation outcomes; deltas `P0`; conditional_citation_only.
- R328 `reports/anneal-v1-end-to-end-pipeline-41f5b37/REPORT.md` — ## Summary; ### `prepare_and_run` is the common pipeline spine; deltas `P0`; conditional_citation_only.
- R331 `reports/anneal-v1-integration-test-disk-amplification-f98458e/REPORT.md` — ## Summary; ### The observed disk failure was about the aggregate worker-cache architecture; deltas `P0`; conditional_citation_only.
- R332 `reports/anneal-v1-interactive-dependency-invalidation-2026-09-28/REPORT.md` — ## Summary; ### The accepted result needs dependency identity, not only a document version; deltas `P0`; conditional_citation_only.
- R337 `reports/anneal-v1-orthogonal-progress-correctness-41f5b37/REPORT.md` — ## Summary; ### `wp_prove_orthogonal` decomposes one strong specification into progress plus conditional correctness; deltas `P0`; conditional_citation_only.
- R339 `reports/anneal-v1-source-scanner-versus-rustc-main-41f5b37/REPORT.md` — ## Summary; ### Literal `#[path]` support is narrower than rustc module identity; deltas `P0`; conditional_citation_only.
- R340 `reports/anneal-v1-unsafe-axiom-semantics-41f5b37/REPORT.md` — ## Summary; ### `unsafe(axiom)` selects a distinct AST state, not a proof with relaxed checking; deltas `P0`; conditional_citation_only.
- R342 `reports/anneal-v2-current-source-surface-main-bd0956b-2026-09-29/REPORT.md` — ## Summary; ## Findings; deltas `P0`; conditional_citation_only.
- R390 `reports/diagnostic-format-controls-nightly-2026-05-31-v4-30-0-rc2/REPORT.md` — ## Summary; ### `format.inputWidth` controls generated suggestion/edit text, not batch message width; deltas `P0`; conditional_citation_only.
- R392 `reports/end-to-end-source-correspondence-nightly-2026-06-03-v4-30-0-rc2/REPORT.md` — ## Summary; ### Translation failures create correspondence holes before Lean diagnostics exist; deltas `P0`; conditional_citation_only.
- R403 `reports/generated-rust-visibility-nightly-2026-05-31/REPORT.md` — ## Summary; ### Included generated files can preserve a stronger filesystem provenance; deltas `P0`; conditional_citation_only.
- R525 `reports/rust-drop-elaboration-nightly-2026-05-31/REPORT.md` — ## Summary; ### Drop elaboration computes initializedness from move paths; deltas `P0`; conditional_citation_only.
- R527 `reports/rust-extern-foreign-items-nightly-2026-05-31/REPORT.md` — ## Summary; ### Charon marks foreign functions, but its extern string is not linker-complete; deltas `P0`; conditional_citation_only.
- R529 `reports/rust-inline-global-assembly-nightly-2026-05-31/REPORT.md` — ## Summary; ### Global assembly is a separate compiler item, not a MIR inline-asm terminator; deltas `P0`; conditional_citation_only.
- R537 `reports/rust-nightly-upgrade-checklist-nightly-2026-05-31/REPORT.md` — ## Summary; ### 5. Treat MIR and LLBC behavior as part of the upgrade, not merely process compatibility; deltas `P0`; conditional_citation_only.
- R540 `reports/rust-panic-unwind-abort-divergence-nightly-2026-05-31/REPORT.md` — ## Summary; ### `panic=abort` changes the MIR unwind graph through a required pass; deltas `P0`; conditional_citation_only.
- R550 `reports/rust-source-span-provenance-nightly-2026-05-31/REPORT.md` — ## Summary; ### Full macro provenance cannot be reconstructed from Charon span metadata alone; deltas `P0`; conditional_citation_only.
- R566 `reports/salsa-rustc-query-granularity-2016-2026/REPORT.md` — ## Summary; ### rustc mechanism and history; deltas `P0`; conditional_citation_only.
- R581 `reports/zerocopy-rust-intrinsics-nightly-2026-05-31/REPORT.md` — ## Summary; ### Zerocopy has no direct unstable-intrinsics import boundary; deltas `P0`; conditional_citation_only.

## Execution gate

Before any active comparison, obtain the exact Aeneas September macOS aarch64 release archive, its paired Charon `e435e5f…` build or compatible binary, Rust nightly-2026-09-17 with rustc-dev/llvm-tools/rust-src/miri, and Lean/Lake 4.31.0 with freshly built Aeneas Lean library/OLeans. Library API probes additionally need a working OCaml/Dune toolchain. The standalone Charon September 30 release is a separate lane. No such tools were installed in this tranche.
