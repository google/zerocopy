# Cargo `RUSTC_WRAPPER` Extraction Coverage, Cache-Reuse Boundaries, and Multi-Crate SVH Binding

## Summary

Extracting formal verification models from multi-crate Rust workspaces through Cargo compiler wrappers (`RUSTC_WRAPPER` and `RUSTC_WORKSPACE_WRAPPER`) requires separating compilation planning, compiler-cache reuse, cross-crate artifact binding, and theorem-proving coverage into distinct contracts:

1. **Compilation Coverage vs. Verification Coverage**: Cargo's `--unit-graph` plan, actual `rustc` wrapper invocations, Charon LLBC output, and checked Lean proof obligations answer different coverage questions. In a multi-target workspace fixture (`coverage_app`, `shared`, `proc_macro`, `consumer`), `cargo build --workspace --all-targets` plans 12 units (9 roots) and dispatches 14 `rustc` invocations, whereas verifying `coverage_app --lib --features selected` plans 7 units (1 root) and discharges a theorem only for the annotated function (`selected_feature_subject.spec`). Build-script outputs (`include!` from `OUT_DIR`) and procedural-macro expansions inline into the target crate's LLBC and Aeneas Lean model, whereas normal cross-crate dependencies (`shared::target_value`) remain opaque external calls unless extracted and verified under their own subject identity or joined via verified sidecars.
2. **Build Freshness vs. Semantic Side-Product Freshness**: Cargo unit fingerprints, `rustc` incremental query reuse, and compiler-wrapper caches (`sccache`) validate ordinary compiler outputs (`.rlib`, `.rmeta`, binaries), not out-of-band semantic side products written by `charon-driver` or custom MIR drivers. When Cargo classifies a unit as fresh (or `sccache` serves a cache hit), the underlying extractor wrapper does not run—as observed empirically when re-running `charon cargo` against an already-populated `CARGO_TARGET_DIR` exited `0` without writing the requested LLBC destination file. Sound reuse of extracted models requires an explicit semantic extraction receipt keyed by the compilation subject, toolchain/extractor identities, translation flags, and semantic artifact digest.
3. **Multi-Crate `RUSTC_WRAPPER` Filtering, SVH Closure Binding, and Post-Cleanup Sidecars**: A sound multi-crate `RUSTC_WRAPPER` driver must pass compiler discovery probes (`rustc -vV`, `--print=...`) and host build scripts (`build_script_build`) through unmodified while injecting `-Z mir-preserve-ub`, `-Z always-encode-mir=yes`, and monomorphization collection into target crates. Furthermore, even with `-Z mir-preserve-ub` and `-Z always-encode-mir=yes`, `rustc` serializes post-optimization `MirPhase::Runtime(Optimized)` (`phase_byte = 0x06`) into `.rlib` / `.rmeta` metadata, stripping `PlaceMention` and `StorageLive` / `StorageDead` statements. Cross-crate verification of raw-pointer and storage-liveness obligations therefore requires linking per-crate post-cleanup `.amir` sidecars (`MirPhase::Runtime(PostCleanup)`, `phase_byte = 0x04`) bound to each upstream `.rlib`'s Strict Version Hash (`extern_svh` / `CrateDisambiguator`).
4. **Open Hash-Indexed ADT Capture, Six-Dimension Incremental Keys, and Lean 4 Reduction Scaling**: Supporting arbitrary unseen crates (`--driver-open-hash-mode`) requires indexing functions and ADTs by FNV-1a `DefPathHash`, joining decoded `OpenAdtTable` nominal descriptors against consumer expectations (preventing shape-preserving nominal struct swaps such as `MeterReading(u32)` vs. `LimitThreshold(u32)`), and checking every local variable's type in Charon `.ullbc` declarations (`checkCompleteCharonLocalDomainGate`). Per-function incremental proof caches require a 6-tuple key `(toolchain_id, flags_bitmask, crate_svh, decoded_body_hash, layout_table_hash, callee_contract_digest)`, and capturing `async` coroutine closures before `mir_Optimized` steals them requires hooking `mir_drops_elaborated_and_const_checked` rather than passive `after_analysis` queries. Finally, sharding generated multi-crate Lean obligations into per-case modules and hoisting byte-array parsing into top-level `def` constants keeps Lean 4 kernel checking within a 2,048 MiB heap ceiling (`lean -j1 -M2048 -DElab.async=false`).

## Applicability

This report synthesizes source analysis, empirical Cargo/Charon/Aeneas/Lean execution, and kernel-checked Lean 4 formalizations across the following subjects:

- **Cargo & Rust Toolchains**:
  - `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef` (`1.98.0-nightly`, 2026-05-26) paired with `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, 2026-05-30,observed on both `aarch64-apple-darwin` and `x86_64-unknown-linux-gnu`).
  - `rustc 1.100.0-nightly` (`923c95cdf5ba65cea505aa2ea829f578e1506ed8`, `x86_64-unknown-linux-gnu`), used for the post-audit generated multi-crate consumer pipeline.
  - `rust-lang/cargo@f3865b2a4d1acc5276f6b3c67d0e057f4dab3928` and `rust-lang/rust@7d2cd0fbc092625ea371da704f15f80216d2220e`, examined at the source and compiler-architecture documentation level for unit fingerprinting, wrapper hashing, and `rustc` red-green incremental query reuse.
- **Compiler Cache & Extraction Toolchains**:
  - `mozilla/sccache@54b6f72a5d3583e8ccb8b83d44e5d41400d8039c` (`docs/Caching.md`, `docs/Rust.md`).
  - `AeneasVerif/charon` version `0.1.210` across three examined commits: `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (Cargo coverage matrix), `a535e914f74db4fd9e6be7048f4233270d8945c0` (Anneal-pinned `charon-driver` wrapper source), and `1e08453924610c19d74c245a7308f17c1008e2db` (complete ULLBC local-domain gate experiments).
  - `AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`.
- **Lean 4 & Anneal**:
  - `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`, used for Aeneas/Anneal V1 verification) and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `x86_64-unknown-linux-gnu`, used for the 25-module multi-crate SVH and open-ADT formalization).
  - `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988` (`anneal/v1`) and `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92` (`anneal/PRINCIPLES.md`, `anneal/DESIGN.md`).

### Cross-Version Invariance vs. Version-Specific Behavior

- **Invariant Across Covered `cargo` / `rustc` Versions (`1.98.0-nightly`, `1.100.0-nightly`, and `cargo@f3865b2a4`)**:
  - Cargo unit freshness (`src/compiler/fingerprint/mod.rs`) gates whether `RUSTC_WRAPPER` / `RUSTC_WORKSPACE_WRAPPER` is invoked; a fresh unit skips the wrapper completely.
  - Wrapper nesting order (`$RUSTC_WRAPPER $RUSTC_WORKSPACE_WRAPPER $RUSTC`) and `RUSTC_WORKSPACE_WRAPPER` filename-hash separation (introduced in Cargo 1.50, with wrapper application to `rustc -vV` probes added in Cargo 1.79) hold across all examined versions.
  - On both `rustc 1.98.0-nightly` (`f8a08b688`) and `rustc 1.100.0-nightly` (`923c95cdf`), `.rlib` metadata stores `MirPhase::Runtime(Optimized)` (`0x06`) whereas post-cleanup sidecars capture `MirPhase::Runtime(PostCleanup)` (`0x04`), and `mir_drops_elaborated_and_const_checked` is required to capture un-stolen `async` coroutine closures.
- **Version- and Configuration-Specific Differences**:
  - Raw Charon LLBC and Aeneas `Funs.lean` output bytes are not byte-identical across replays (`support/cargo-rust-charon-anneal-coverage-matrix/replay-results.json`), even when declaration locality and opacity projections match.
  - Under Lean `4.34.1` (`5045d0056`), monolithic `decide` proofs over 71–100 KB multi-crate generated byte arrays peak at ~766–803 MiB RSS and fail under `-M768`, requiring per-case module sharding and `-M2048 -DElab.async=false`.

## Findings

### 1. Compilation Roots, Extracted Declarations, and Checked Obligations Are Distinct Sets

**Basis: execution + derived**

Empirical execution on the dependency-free multi-package workspace in `support/cargo-rust-charon-anneal-coverage-matrix/workspace/Cargo.toml` (recorded in `support/cargo-rust-charon-anneal-coverage-matrix/command-results.json` and `support/cargo-rust-charon-anneal-coverage-matrix/replay-results.json`) separates four coverage layers:

1. **Planned Units vs. Executed `rustc` Invocations**:
   - `cargo -Z unstable-options build --offline --workspace --all-targets --unit-graph` (`support/cargo-rust-charon-anneal-coverage-matrix/unit-graph-default.json`) reports `12` planned units and `9` roots, while `cargo build --offline --workspace --all-targets` dispatches `14` `rustc` invocations (`support/cargo-rust-charon-anneal-coverage-matrix/rustc-workspace.jsonl`, captured via `support/cargo-rust-charon-anneal-coverage-matrix/record-rustc.py`).
   - Selecting only the library target and `selected` feature (`cargo -Z unstable-options build --offline --package coverage_app --lib --features selected --unit-graph`, preserved in `support/cargo-rust-charon-anneal-coverage-matrix/unit-graph-selected.json`) narrows the plan to `7` units and `1` root.
2. **Feature-Resolution Asymmetry Between Source Scanners and `rustc`**:
   - In `unit-graph-default.json`, the `shared` dependency appears in two units with distinct feature sets: a host build-dependency unit with `["build-api"]` and a target/test unit with `["dev-api", "macro-api", "target-api"]`. In `unit-graph-selected.json`, `shared` has `["build-api"]` on the host side and `["target-api"]` on the target side (omitting `"dev-api"`).
   - When `cargo-anneal verify` is invoked without `--features selected` (`support/cargo-rust-charon-anneal-coverage-matrix/anneal-no-feature.stderr`), the Anneal V1 source scanner still discovers the verification annotation inside `#[cfg(feature = "selected")]`, but Charon/`rustc` fails with exit code `1` because `selected_feature_subject` is `cfg`-stripped from the compiled crate.
3. **Build-Script and Procedural-Macro Inlining vs. Cross-Crate Dependency Opacity**:
   - `coverage_app/build.rs` writes `BUILD_VALUE = 17` into `OUT_DIR` and `proc_macro` expands `proc_generated() = 29`. Both enter `coverage_app`'s local LLBC declarations (`support/cargo-rust-charon-anneal-coverage-matrix/charon-aeneas-functions.json`) and Aeneas Lean output (`17#u32` and `29#u32` in `support/cargo-rust-charon-anneal-coverage-matrix/aeneas-Funs-replayed.lean`), although only `selected_feature_subject` has a generated V1 theorem (`selected_feature_subject.spec` with postcondition `ret.val = 101` in `support/cargo-rust-charon-anneal-coverage-matrix/v1-generated-selected-spec.lean`).
   - Conversely, the normal library dependency `shared::target_value` remains an external/opaque call in `coverage_app`'s model, and extracting the downstream `consumer` binary (`support/cargo-rust-charon-anneal-coverage-matrix/charon-consumer-functions.json`) marks `coverage_app::selected_feature_subject` as foreign/opaque with no local body. Compiling or extracting a consumer crate therefore never implies verification of its dependencies.
   - Direct `charon cargo` extraction of the workspace binary (`support/cargo-rust-charon-anneal-coverage-matrix/charon-bin3.stderr`) or integration test (`support/cargo-rust-charon-anneal-coverage-matrix/charon-test2.stderr`) exited `101` with `extern location for coverage_app does not exist` for the expected `.rlib`.

### 2. Cargo Freshness, `rustc` Incremental Reuse, and `sccache` vs. Semantic Extraction Receipts

**Basis: normative + source + documentation + execution + derived**

Source inspection of Cargo (`rust-lang/cargo@f3865b2a4d1acc5276f6b3c67d0e057f4dab3928`, `src/compiler/fingerprint/mod.rs`, `src/compiler/build_runner/compilation_files.rs`, `src/util/rustc.rs`), `rustc` (`rust-lang/rust@7d2cd0fbc092625ea371da704f15f80216d2220e`), `sccache` (`mozilla/sccache@54b6f72a5d3583e8ccb8b83d44e5d41400d8039c`), and Charon (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/src/bin/charon/main.rs`, `charon/src/bin/charon-driver/driver.rs`, indexed in `support/cargo-rustc-cache-reuse-extraction-boundaries-2016-2026/evidence-map.json`) establishes why ordinary build caches cannot serve as verification extraction caches:

| Layer | Reuse Decision Mechanism | Validated Output Domain | What a Cache Hit Fails to Establish |
| :--- | :--- | :--- | :--- |
| **Cargo Unit Freshness** | Unit fingerprint (`fingerprint/mod.rs`), `dep-info`, mtimes/checksums, `RUSTC_WORKSPACE_WRAPPER` filename hash | Ordinary Cargo unit outputs (`.rlib`, `.rmeta`, binaries) | That `RUSTC_WRAPPER` (`charon-driver`) ran on this request, or that an out-of-band `.llbc` / `.amir` file exists and matches current extractor flags. |
| **`rustc` Incremental** | Red-green query dependency graph and persisted query result fingerprints | Compiler-internal query results within an active `rustc` session | That an external wrapper side product was emitted or updated if Cargo or an outer wrapper skipped `rustc`. |
| **`sccache` Wrapper** | Digest of source, `rustc`, host, sysroot shared libraries, `.rlib` deps, and `rustc` flags (requires `incremental = false`) | Cached supported `rustc` outputs (`.rlib`, `.rmeta`) | That an inner `RUSTC_WORKSPACE_WRAPPER` or `rustc_driver` callback executed, or that procedural-macro untracked filesystem reads were captured. |
| **Semantic Extraction Receipt** | Explicit receipt over compilation subject, toolchain/extractor digests, extractor flags, and semantic output digest | The `.llbc` / `.amir` semantic artifact and its downstream verification obligations | Publication currency if a concurrent edit superseded the request (requiring a separate publication-freshness fence). |

This boundary was observed directly during the coverage-matrix replay (`support/cargo-rust-charon-anneal-coverage-matrix/replay-lib.stderr` vs. `support/cargo-rust-charon-anneal-coverage-matrix/replay-lib-clean.stderr` and `support/cargo-rust-charon-anneal-coverage-matrix/replay-results.json`): when `charon cargo` was re-invoked with an already-populated `CARGO_TARGET_DIR`, Cargo considered the library unit fresh, skipped `charon-driver`, and exited `0` without writing the destination LLBC file; providing a clean `CARGO_TARGET_DIR` forced `charon-driver` to run and emit the LLBC artifact.

### 3. Multi-Crate `RUSTC_WRAPPER` Filtering, SVH Closure Binding, and Post-Cleanup `.amir` Sidecars

**Basis: source + execution + derived**

Empirical capture in `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/run_workspace_capture.py` (`support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/workspace-capture-ledger.json`) and `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/run_n5_open_hash_and_rlib_phase.py` (`support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/n5-open-hash-and-rlib-phase-ledger.json`), together with Lean 4 proofs in `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/CargoWorkspaceIntegration.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/CargoWorkspaceIntegrationControls.lean`, and `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean`, establish three multi-crate wrapper invariants:

1. **Per-Invocation Wrapper Filtering and `-Z always-encode-mir=yes`**:
   - Building the two-crate workspace (`dep_layout_core` with a `build.rs` generating `$OUT_DIR/generated_align.rs`, plus `app_verifier_subject`) triggers 6 `RUSTC_WRAPPER` invocations: 3 discovery probes (`crate_name: null` or `"___"`), 1 host build-script compilation (`crate_name: "build_script_build"`, `--crate-type bin`), and 2 target crate compilations (`dep_layout_core` and `app_verifier_subject`). The wrapper passes probes and `build_script_build` through untouched and injects `-Z mir-preserve-ub`, `-Z always-encode-mir=yes`, `--driver-include-const-owners`, `--driver-run-mono-collector`, and `--driver-emit-amir-v3` into target crates (`r7_per_invocation_cargo_binding_and_unused_failing_const_verified`).
   - Without `-Z always-encode-mir=yes`, `rustc` omits non-generic, non-`#[inline]` upstream functions from cross-crate metadata, failing call-graph closure (`default_mir_encoding_rejected_missing_cross_crate_body`).
   - Toggling `--features strict_align` changes `dep_layout_core::REQUIRED_ALIGN` from `4` to `8`, producing distinct 448-byte `.amir` v3 artifacts (`77683ab3...` vs. `a4a72ca6...`) and changing downstream semantics (`feature_toggle_distinct_amir_v3_bytes`, `decoded_amir_v3_feature_toggle_changes_semantics`).
   - Five negative-control theorems (`control1_substituted_rlib_svh_mismatch_rejected` through `control5_per_field_cargo_invocation_binding_rejections`) prove fail-closed rejection when an `.rlib` SVH (`extern_svh`) disagrees with the sidecar's recorded SVH (`144941decff46881` vs. `9999999999999999`), when a transitive `.amir` is missing, when stale feature sidecars are mixed, when `--driver-stop-after-analysis` produces provisional outputs, or when any invocation-binding field is mutated.
2. **Why External `.rlib` `optimized_mir` Cannot Replace Post-Cleanup `.amir` Sidecars**:
   - Even when `ext_phase_lib` is compiled into `libext_phase_lib_preserve_ub.rlib` with both `-Z mir-preserve-ub` and `-Z always-encode-mir=yes`, `tcx.optimized_mir(def_id)` read from `.rlib` metadata has phase `MirPhase::Runtime(Optimized)` (`phase_byte = 0x06`), where optimization passes have stripped `PlaceMention` statements and `StorageLive` / `StorageDead` markers (`n5_external_rlib_optimized_mir_vs_postcleanup_sidecar_discriminator`, `r9_cross_crate_postcleanup_sidecar_vs_rlib_optimized_mir_discriminator`).
   - By contrast, the per-crate post-cleanup `.amir` sidecar (`MirPhase::Runtime(PostCleanup)`, `phase_byte = 0x04`, SHA-256 `3a5a05a63e5de0e02565a3bdd94976f2c51dce6d11100bce45b8fc5ee7578aef`) preserves both `PlaceMention` and storage-liveness markers, and header-bound post-run endorsement (`c2_d2_header_consistent_endorsement_rejects_mismatched_header_q4`, `c2_repaired_endorsement_rejects_inconsistent_header_fingerprint` in `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/PR94AuditCounterexamples.lean`) rejects any non-`0x04` phase or mismatched payload fingerprint.

### 4. Open Hash-Indexed ADT Capture, Six-Dimension Incremental Keys, and Lean 4 Proof-Cost Scaling

**Basis: source + execution + derived**

1. **Open Hash-Indexed Symbol Resolution and Nominal ADT Table Joins**:
   - Under `--driver-open-hash-mode` (`support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/run_n5_open_hash_and_rlib_phase.py`), unseen multi-crate workspaces (`r5_inner_lib`, `r5_outer_lib`, `r5_client_app`, `q3_nominal_pair_lib`, `q3_nominal_pair_client`) are indexed by FNV-1a `DefPathHash` buckets with linear-probing collision resolution (`r5_open_hash_multi_crate_execution_and_refactor_and_collision_verified`), failing closed with exit code `2` on bucket exhaustion, external-body cap overflow, or unsupported ADT field arity (`r5_all_negative_controls_verified`).
   - Because two single-field `#[repr(C)]` structs (`MeterReading(pub u32)` and `LimitThreshold(pub u32)`) share identical size (`4`), alignment (`4`), and field projections, structural MIR evaluation alone cannot detect a return-type swap (`q9_shape_preserving_nominal_return_swap_challenge`). Joining the decoded `OpenAdtTable` (`adtHash`, `variantCount`, `fieldTypes`, `size`, `align`, `isReprC`) against the consumer's expected nominal signature table (`c2_d1_bound_open_adt_table_consumer_join_and_substitutions_verified`, `Post96Consumer.nominal_acceptance_uses_consumed_table` in `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/Post96Consumer.lean`) and universal `#[repr(C)]` layout recurrence (`c2_d3_captured_layout_to_repr_c_recurrence_and_mutations_verified`) rejects nominal swaps and layout mutations.
   - Similarly, `checkCompleteCharonLocalDomainGate` (`c2_d4_complete_charon_local_domain_gate_rejects_both_ctrl6_and_ctrl7_unchecked_local_mutant` in `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/PR94AuditCounterexamples.lean`, backed by `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/portable_pr94_control.py` and `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/pr94-audit-counterexamples-ledger.json`) checks every local variable's type across all Charon `.ullbc` function declarations, rejecting a `u32` $\to$ `u64` mutation in `fun_decls[4].body.locals[2]` that bypassed a partial local-domain check.
2. **Six-Dimension Per-Function Incremental Cache Key and `mir_drops_elaborated` Hook**:
   - In `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/FrontendIncrementalFrontiers.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/FrontendIncrementalControls.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/CostIncrementalAndFrontiers.lean`, and `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/CostIncrementalAndFrontiersControls.lean`, per-function proof reuse across crate revisions (`alpha_rev0` $\to$ `alpha_rev1` internal refactor $\to$ `alpha_rev2` contract change) is proved sound when keyed by the 6-tuple `(toolchain_id, flags_bitmask, crate_svh, decoded_body_hash, layout_table_hash, callee_contract_digest)` (`validateConfiguredProofCache_implies_verified_caller_cache_and_beta_contract`), whereas keying by caller body hash alone or `DefPathHash` alone is unsound (`control_caller_body_only_cache_unsound_when_callee_contract_changes`, `control_def_path_hash_only_cache_unsoundly_accepts_mutated_bodies`).
   - Because `rustc` steals `async` coroutine closure bodies during `mir_Optimized` lowering before `after_analysis` executes (`control_after_analysis_passive_query_loses_async_coroutine_closure`), capturing all 7 language-frontier categories (`dyn Trait` vtables, `async` state machines/cancellation drops, unions, `Pin`, `UnsafeCell`, `extern "C"` FFI, and const generics) requires hooking `mir_drops_elaborated_and_const_checked` (`all_seven_frontiers_captured_in_drops_elaborated_hook`).
3. **Lean 4 Kernel Reduction Memory Scaling**:
   - While `rustc_driver` capture completes in `18–382 ms` and `101–534 MiB` peak RSS, monolithic `decide` proofs over unsharded multi-crate generated byte arrays (`support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/Post96LifecycleGenerated.lean.failed.txt`, 100,586 bytes) and `OpenHashMultiCrateR5R6R9R10.lean` (71,815 bytes, peaking at ~766.2 MiB RSS) exceed a 768 MiB heap cap (`-M768`). Sharding generated obligations into per-case modules (`support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/Post96ConsumerGenerated.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/Post96NativeConsumerGenerated.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/Post96ChallengeGenerated.lean`), hoisting `parseAcceptedMirPackageBytes` into top-level `def` constants, and discharging record equalities with `beq_iff_eq.mpr rfl` allows all 25 modules to verify within `lean -j1 -M2048 -DElab.async=false` (`support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/lean-execution-ledger.json`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/cargo-lean-cost-README.md`).

## Boundaries

- **Not Examined**:
  - Distributed remote execution and remote artifact caching (`sccache` remote storage or Bazel remote execution) where `.llbc` or `.amir` sidecars must be keyed and transported alongside `.rlib` artifacts across machines.
  - Quantitative cache-hit latency benchmarks for `sccache` vs. `rustc` incremental compilation on large production repositories.
  - Verification of procedural-macro host crate implementations as proof subjects (procedural-macro and `build.rs` crates are treated as host build machinery whose expanded outputs enter target crates).
- **Unknown**:
  - Whether future Lean 4 kernel bytecode evaluator optimizations will reduce the RSS of `decide` / `rfl` reductions over 100+ KB generated AST literals below 768 MiB without module sharding.
- **Known Not to Apply**:
  - Cargo unit freshness or an `sccache` compiler-cache hit does not establish that `charon-driver` or a custom `RUSTC_WRAPPER` emitted or updated its out-of-band `.llbc` / `.amir` side product.
  - Reading `tcx.optimized_mir(def_id)` from external `.rlib` metadata cannot be used to verify pre-optimization `PlaceMention` or `StorageLive` / `StorageDead` obligations (`n5_external_rlib_optimized_mir_vs_postcleanup_sidecar_discriminator`).
  - Passive `after_analysis` queries cannot capture `async` coroutine closure bodies stolen during `mir_Optimized` lowering (`control_after_analysis_passive_query_loses_async_coroutine_closure`).
  - Running `lean -j1 -M768` on `OpenHashMultiCrateR5R6R9R10.lean` or the unsharded `Post96LifecycleGenerated.lean.failed.txt` exceeds the 768 MiB heap limit (`803.4 MiB` peak RSS); `-M2048 -DElab.async=false` is required.
- **Unsupported**:
  - Under `--driver-open-hash-mode`, ADTs with more than 3 scalar fields (`r5_control_unsupported_adt_arity_4_reject`), hash-bucket modulus exhaustion (`r5_control_hash_table_exhausted_modulus_4_reject`), and unclosed external call graphs (`r5_control_unclosed_external_cap_2_reject`) fail closed with exit code `2`.

## Evidence

| Category | Preserved Support Artifacts & Upstream Coordinates |
| :--- | :--- |
| **Cargo / Charon / Aeneas / Anneal V1 Coverage Matrix** | `support/cargo-rust-charon-anneal-coverage-matrix/workspace/Cargo.toml`, `support/cargo-rust-charon-anneal-coverage-matrix/unit-graph-default.json`, `support/cargo-rust-charon-anneal-coverage-matrix/unit-graph-selected.json`, `support/cargo-rust-charon-anneal-coverage-matrix/rustc-workspace.jsonl`, `support/cargo-rust-charon-anneal-coverage-matrix/charon-aeneas-functions.json`, `support/cargo-rust-charon-anneal-coverage-matrix/charon-consumer-functions.json`, `support/cargo-rust-charon-anneal-coverage-matrix/aeneas-Funs-replayed.lean`, `support/cargo-rust-charon-anneal-coverage-matrix/v1-generated-selected-spec.lean`, `support/cargo-rust-charon-anneal-coverage-matrix/command-results.json`, `support/cargo-rust-charon-anneal-coverage-matrix/replay-results.json`. |
| **Cache-Reuse & Extraction Receipts** | `support/cargo-rustc-cache-reuse-extraction-boundaries-2016-2026/evidence-map.json`; `rust-lang/cargo@f3865b2a4d1acc5276f6b3c67d0e057f4dab3928` (`src/compiler/fingerprint/mod.rs` blob `ebaa5c34d2d8ff97baee0d86541ce3d96c6be5d4`, `src/compiler/build_runner/compilation_files.rs`, `src/util/rustc.rs`, `doc/book/src/reference/config.md`); `mozilla/sccache@54b6f72a5d3583e8ccb8b83d44e5d41400d8039c` (`docs/Caching.md` blob `0f4ca650ef8af51bb30f813381d98859faf8ed13`, `docs/Rust.md` blob `5d6f98c3cfc535fba674c49cbac7ae8149859f1f`); `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`charon/src/bin/charon/main.rs` blob `b4460ce4cd3baa32308718e79b6e194860b042a6`, `charon/src/bin/charon-driver/driver.rs` blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`); `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92` (`anneal/PRINCIPLES.md`, `anneal/DESIGN.md`). |
| **Multi-Crate SVH Binding, `.rlib` vs. `.amir` Phase, & Open ADT Capture** | `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/run_workspace_capture.py`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/workspace-capture-ledger.json`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/run_n5_open_hash_and_rlib_phase.py`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/n5-open-hash-and-rlib-phase-ledger.json`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/portable_pr94_control.py`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/pr94-audit-counterexamples-ledger.json`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/CargoWorkspaceIntegration.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/CargoWorkspaceIntegrationControls.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/PR92AuditCounterexamples.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/PR94AuditCounterexamples.lean`. |
| **Incremental Frontiers & Lean 4 Proof-Cost Scaling** | `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/lean-execution-ledger.json`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/cargo_lean_cost_run_checks.py`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/cargo-lean-cost-README.md`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/post96-pipeline-README.md`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/Post96LifecycleGenerated.lean.failed.txt`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/FrontendIncrementalFrontiers.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/FrontendIncrementalControls.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/CostIncrementalAndFrontiers.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/CostIncrementalAndFrontiersControls.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/Post96Consumer.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/Post96ConsumerGenerated.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/Post96NativeConsumerGenerated.lean`, `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/Post96ChallengeGenerated.lean`. |

## Revalidation

1. **Re-verifying the 25-Module Lean 4 Multi-Crate Closure**:
   Compile the topological closure under `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/` using Lean `4.34.1` with a 2,048 MiB heap ceiling:
   ```bash
   LEAN_BUILD_DIR="$(mktemp -d)"
   mkdir -p "${LEAN_BUILD_DIR}/AnnealResearch"
   for mod in \
     Execution \
     FrontendIncrementalFrontiers \
     FrontendIncrementalControls \
     SubstantiveMirByteParser \
     CargoWorkspaceIntegration \
     SemanticVerticalSliceCore \
     CargoWorkspaceIntegrationControls \
     OpenHashMultiCrateR5R6R9R10 \
     StatefulGenericLibraryH3H7Core \
     StatefulGenericLibraryH3H7 \
     StatefulGenericLibraryH3H7Controls \
     PR86AuditRepairs \
     BuiltPhaseControlsR1 \
     CharonNativeAndControlsR3R4 \
     PR86AuditCounterexamples \
     PR92AuditCounterexamples \
     PR94AuditCounterexamples \
     Post96Consumer \
     Post96NativeConsumer \
     Post96LifecycleInterface \
     Post96ConsumerGenerated \
     Post96NativeConsumerGenerated \
     Post96ChallengeGenerated \
     CostIncrementalAndFrontiers \
     CostIncrementalAndFrontiersControls; do
     LEAN_PATH="${LEAN_BUILD_DIR}" lean -j1 -M2048 -DElab.async=false \
       -o "${LEAN_BUILD_DIR}/AnnealResearch/${mod}.olean" \
       "support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/AnnealResearch/${mod}.lean"
   done
   ```
   Every module must exit `0` within the 2,048 MiB memory ceiling, matching `support/cargo-rustc-wrapper-multi-crate-svh-binding-and-open-adt-capture/lean-execution-ledger.json`.
2. **Re-verifying Cargo Coverage and Wrapper Elision**:
   From `support/cargo-rust-charon-anneal-coverage-matrix/workspace/Cargo.toml`, run `cargo -Z unstable-options build --offline --workspace --all-targets --unit-graph` and `cargo -Z unstable-options build --offline --package coverage_app --lib --features selected --unit-graph`, then run `charon cargo` against both a clean `CARGO_TARGET_DIR` and a pre-populated `CARGO_TARGET_DIR` to confirm that unit freshness skips `charon-driver` unless an explicit semantic-artifact receipt or target invalidation forces extraction.
