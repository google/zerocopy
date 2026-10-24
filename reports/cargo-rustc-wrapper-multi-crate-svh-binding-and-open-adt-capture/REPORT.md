# Cargo `RUSTC_WRAPPER` Multi-Crate SVH Binding, Open Hash-Indexed ADT Capture, and Lean 4 Proof-Cost Scaling

## Summary

Scaling MIR-based formal verification from single-file `rustc` invocations to real multi-crate Cargo workspaces introduces five systems and proof-engineering boundaries:

1. **Per-invocation Cargo `RUSTC_WRAPPER` filtering and Strict Version Hash (SVH) closure binding**: A Cargo workspace build invokes `rustc` for version/target discovery probes (`rustc -vV`, `--print=...`), host `build.rs` scripts (`--crate-name build_script_build`), and target crates (`dep_layout_core`, `app_verifier_subject`). A sound `RUSTC_WRAPPER` driver must pass discovery probes and host build scripts through unmodified while injecting `-Z mir-preserve-ub`, `-Z always-encode-mir=yes`, and `--driver-run-mono-collector` into target crate invocations, and must bind each upstream `.rlib` / `.rmeta` dependency's `CrateDisambiguator` / SVH (`extern_svh`) to its corresponding `.amir` v3 sidecar (`workspace_amir_v3_artifacts_parse`, `always_encode_mir_workspace_accepted`, `strict_align_workspace_accepted`).
2. **Post-cleanup `.amir` sidecars vs. external `.rlib` `optimized_mir`**: Even when upstream crates are compiled with `-Z always-encode-mir=yes`, `rustc` stores post-optimization `optimized_mir` in `.rlib` / `.rmeta` metadata (`MirPhase::Runtime(Optimized)`), which strips `PlaceMention` and `StorageLive` / `StorageDead` markers (`n5_external_rlib_optimized_mir_vs_postcleanup_sidecar_discriminator`, `r9_cross_crate_postcleanup_sidecar_vs_rlib_optimized_mir_discriminator`). Cross-crate verification of raw-pointer and storage-liveness obligations therefore requires linking per-crate post-cleanup `.amir` sidecars (`MirPhase::Runtime(PostCleanup)`) rather than reading `tcx.optimized_mir(def_id)` from external `.rlib` files.
3. **Open hash-indexed symbol and nominal ADT capture (`--driver-open-hash-mode`)**: Replacing hard-coded symbol/type tables with open FNV-1a `DefPathHash` symbol IDs and open nominal ADT descriptors (`AdtEntry`, `OpenAdtTable`) enables compilation and verification of previously unseen multi-crate workspaces (`r5_inner_lib`, `r5_outer_lib`, `r5_client_app`, `q3_nominal_pair_lib`, `q3_nominal_pair_client`). Soundness requires joining the consumer's nominal ADT expectation table against the decoded `AMIRv3` package's `openAdtTable` (`c2_d1_bound_open_adt_table_consumer_join_and_substitutions_verified`, `Post96Consumer.nominal_acceptance_uses_consumed_table`) so that shape-preserving nominal type swaps (`MeterReading(u32)` vs. `LimitThreshold(u32)`) are rejected.
4. **Six-dimension incremental cache invalidation and `mir_drops_elaborated` hook placement**: Per-function incremental verification caches are sound only when keyed by the full 6-tuple `(toolchain_id, flags_bitmask, crate_svh, decoded_body_hash, layout_table_hash, callee_contract_digest)` (`incremental_reuse_equals_fresh_reconstruction`, `verified_caller_cache_sound`). Furthermore, `async fn` coroutine closure bodies are stolen by `mir_Optimized` before `after_analysis` runs; capturing them requires hooking `mir_drops_elaborated_and_const_checked` (`coroutine_closure_stolen_before_after_analysis_but_captured_in_elaborated_hook`).
5. **Lean 4 kernel reduction scaling on multi-crate generated artifacts**: Monolithic `native_decide` / `decide` proofs over raw multi-crate byte arrays (`Post96LifecycleGenerated.lean.failed.txt`, 100,586 bytes) exceed a 768 MiB memory ceiling during Lean kernel reduction (`OpenHashMultiCrateR5R6R9R10.lean` peaks at ~766.2 MiB RSS). Factoring generated obligations into per-case modules, lifting byte decoding to top-level `def` constants, and replacing monolithic conjunction `decide` calls with `beq_iff_eq.mpr rfl` plus structural projections bounds per-module verification memory within `lean -j1 -M2048 -DElab.async=false`.

## Applicability

These findings apply to multi-crate Rust verification toolchains operating via Cargo's `RUSTC_WRAPPER` protocol and discharging proof obligations in Lean 4:

- **Rust Toolchains**:
  - Primary workspace, open-hash, and incremental frontier experiments: `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `x86_64-unknown-linux-gnu`), Cargo SHA-256 `dda7234360b7f578ca8b0ddcb80145646fa61a67c1720a5abc7051b35c9fcb71`.
  - Post-audit generated consumer pipeline (`post96-pipeline` and `cargo-lean-cost`): `rustc 1.100.0-nightly` (`923c95cdf5ba65cea505aa2ea829f578e1506ed8`, `x86_64-unknown-linux-gnu`).
- **Comparison Extractor**: `charon 0.1.210` (`88542ca0b2bf52429fd5b9f2bf29f0f1183ba2279854567ab13d82bc789a8d47`).
- **Proof Assistant**: Lean `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`), verified with `lean -j1 -M2048 -DElab.async=false`.

## Findings

### 1. Multi-Crate Cargo `RUSTC_WRAPPER` Capture, Feature Toggles, and SVH Closure Binding

**Basis: source | execution | derived**

[`support/run_workspace_capture.py`](support/run_workspace_capture.py) (recorded in [`support/workspace-capture-ledger.json`](support/workspace-capture-ledger.json)) and Lean proofs in [`support/AnnealResearch/CargoWorkspaceIntegration.lean`](support/AnnealResearch/CargoWorkspaceIntegration.lean) and [`support/AnnealResearch/CargoWorkspaceIntegrationControls.lean`](support/AnnealResearch/CargoWorkspaceIntegrationControls.lean) characterize how Cargo orchestrates `rustc` across a multi-crate workspace (`dep_layout_core` with a `build.rs` script generating `$OUT_DIR/generated_align.rs`, consumed by `app_verifier_subject`):

- **Invocation Filtering**: A single `cargo build` issues 6 wrapper invocations: 3 compiler probe invocations (`crate_name: null` or `"___"`), 1 host build-script compilation (`crate_name: "build_script_build"`, `--crate-type bin`), and 2 target crate compilations (`dep_layout_core` and `app_verifier_subject`). The wrapper records every invocation and injects MIR extraction flags (`-Z mir-preserve-ub`, `--driver-include-const-owners`, `--driver-run-mono-collector`, `--driver-emit-amir-v3`) only on non-build-script target crates (`r7_per_invocation_cargo_binding_and_unused_failing_const_verified`).
- **Requirement for `-Z always-encode-mir=yes` on Cross-Crate Dependencies**: Under default `rustc` flags, non-generic, non-`#[inline]` functions in `dep_layout_core` omit MIR from downstream metadata, causing call-graph closure checks to reject the workspace (`default_mir_encoding_rejected_missing_cross_crate_body`). Enabling `-Z always-encode-mir=yes` and linking the per-crate `.amir` v3 packages satisfies cross-crate closure (`always_encode_mir_workspace_accepted`, `strict_align_workspace_accepted`).
- **Feature-Flag Sensitivity (`default` vs. `--features strict_align`)**: Toggling `--features strict_align` changes `dep_layout_core`'s `REQUIRED_ALIGN` constant owner from `4` to `8`, producing distinct `.amir` v3 binaries (`dep_layout_core_default.amir` SHA-256 `77683ab3...` vs. `dep_layout_core_strict_align.amir` SHA-256 `a4a72ca6...`, both 448 bytes) and altering the cross-crate operational semantics of `app_verifier_subject` (`feature_toggle_distinct_amir_v3_bytes`, `decoded_const_owners_reflect_feature_toggle`, `decoded_amir_v3_feature_toggle_changes_semantics`).
- **SVH and Provenance Negative Controls**: [`support/AnnealResearch/CargoWorkspaceIntegrationControls.lean`](support/AnnealResearch/CargoWorkspaceIntegrationControls.lean) proves five fail-closed rejection theorems:
  1. `control1_substituted_rlib_svh_mismatch_rejected`: Rejects an `.amir` sidecar whose recorded dependency SVH (`144941decff46881`) disagrees with a substituted `.rlib` (`9999999999999999`).
  2. `control2_missing_transitive_amir_rejected`: Rejects a workspace missing a transitive dependency's `.amir` package.
  3. `control3_stale_feature_amir_rejected`: Rejects mixing `app_verifier_subject` compiled under `strict_align` with a stale `dep_layout_core` `.amir` compiled under `default` features.
  4. `control4_incomplete_provisional_compilation_rejected`: Rejects artifacts from `--driver-stop-after-analysis` or failed writes.
  5. `control5_per_field_cargo_invocation_binding_rejections`: Proves that mutating any field of the Cargo invocation binding record (toolchain, flags, SVH, `OUT_DIR` hash, or feature set) invalidates admission.

### 2. External `.rlib` `optimized_mir` vs. Post-Cleanup `.amir` Sidecars

**Basis: source | execution | derived**

A natural question for multi-crate Rust verification is whether upstream dependency MIR can be read directly from Cargo's compiled `.rlib` / `.rmeta` files via `tcx.optimized_mir(def_id)` when `-Z always-encode-mir=yes` is enabled, avoiding per-crate sidecar files. Empirical capture in [`support/n5-open-hash-and-rlib-phase-ledger.json`](support/n5-open-hash-and-rlib-phase-ledger.json) (`n5_ext_phase_lib_postcleanup_sidecar` vs. `n5_ext_phase_client_from_default_rlib` and `n5_ext_phase_client_from_preserve_ub_rlib`) and formal proofs in [`support/AnnealResearch/CargoWorkspaceIntegrationControls.lean`](support/AnnealResearch/CargoWorkspaceIntegrationControls.lean) (`n5_external_rlib_optimized_mir_vs_postcleanup_sidecar_discriminator`) and [`support/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean`](support/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean) (`r9_cross_crate_postcleanup_sidecar_vs_rlib_optimized_mir_discriminator`) prove that `.rlib` metadata MIR is insufficient for pre-optimization UB and storage-liveness verification:

- When `ext_phase_lib` is compiled into `/tmp/libext_phase_lib_preserve_ub.rlib` even with `-Z mir-preserve-ub` and `-Z always-encode-mir=yes`, the MIR serialized into the `.rlib` metadata has phase `MirPhase::Runtime(Optimized)` (`phase_byte = 0x06`).
- Optimization passes before `.rlib` metadata serialization strip `PlaceMention` statements and elide `StorageLive` / `StorageDead` intervals, whereas the post-cleanup `.amir` sidecar (`n5_ext_phase_lib_sidecar.amir`, 58 bytes, SHA-256 `3a5a05a63e5de0e02565a3bdd94976f2c51dce6d11100bce45b8fc5ee7578aef`, `MirPhase::Runtime(PostCleanup)`, `phase_byte = 0x04`) retains both the raw-pointer `PlaceMention` and storage markers.
- The post-run endorsement gate (`r6_post_run_endorsement_and_five_controls_verified`, `q4_header_bound_post_run_endorsement_verified`, `c2_d2_header_consistent_endorsement_rejects_mismatched_header_q4`) binds the `.amir` header's `mir_phase` byte (`0x04`) and 16-bit payload fingerprint directly to the sidecar endorsement record, rejecting `Runtime(Initial)` (`0x05`) and `Runtime(Optimized)` (`0x06`) payloads (`endorsement_still_accepts_inconsistent_header_fingerprint` repaired by `c2_repaired_endorsement_rejects_inconsistent_header_fingerprint` in [`support/AnnealResearch/PR94AuditCounterexamples.lean`](support/AnnealResearch/PR94AuditCounterexamples.lean)).

### 3. Open Hash-Indexed Symbol Capture, Nominal ADT Tables, and Complete Charon Local-Domain Gates

**Basis: source | execution | derived**

To verify arbitrary multi-crate programs without pre-registering crate or type names in the compiler driver, [`support/run_n5_open_hash_and_rlib_phase.py`](support/run_n5_open_hash_and_rlib_phase.py) confirms that zero identifiers from the 3-crate open-hash benchmark (`r5_inner_lib`, `r5_outer_lib`, `r5_client_app`, `WindowSpec`, `QuotaPair`, `AuditCounter`, `ScopedTicket`, `MeterReading`, `LimitThreshold`) appear in `direct_mir_driver_v4.rs` (`unseen_identifiers_absent_from_driver_source`). [`support/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean`](support/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean), [`support/AnnealResearch/CharonNativeAndControlsR3R4.lean`](support/AnnealResearch/CharonNativeAndControlsR3R4.lean), [`support/AnnealResearch/PR92AuditCounterexamples.lean`](support/AnnealResearch/PR92AuditCounterexamples.lean), [`support/AnnealResearch/PR94AuditCounterexamples.lean`](support/AnnealResearch/PR94AuditCounterexamples.lean), and [`support/AnnealResearch/Post96Consumer.lean`](support/AnnealResearch/Post96Consumer.lean) establish the open-capture invariants and audit counterexample repairs:

1. **Open Hash Symbol Resolution and Collision / Exhaustion Controls (`r5_open_hash_multi_crate_execution_and_refactor_and_collision_verified`, `r5_all_negative_controls_verified`)**:
   - Under `--driver-open-hash-mode`, function and ADT symbols are indexed by their `DefPathHash`-derived bucket IDs with linear probing on collision (`r5_control_forced_hash_collision_modulus_10`, exit code `0`, SHA-256 `a1ba5277...`).
   - If the hash table modulus is exhausted (`--driver-hash-bucket-modulus 4`, exit code `2`), if external body capture is capped below call closure (`--driver-max-external-bodies 2`, exit code `2`), or if an ADT exceeds the supported field arity (`r5_overwide_adt_reject.rs`, exit code `2`), the driver fails closed and emits no `.amir` file.
2. **Nominal ADT Table Binding Prevents Shape-Preserving Type Swaps (`q3_nominal_pair_cross_crate_challenge_and_four_adt_witness_verified`, `c2_d1_bound_open_adt_table_consumer_join_and_substitutions_verified`, `Post96Consumer.nominal_acceptance_uses_consumed_table`)**:
   - Two distinct single-field `#[repr(C)]` structs (`MeterReading(pub u32)` and `LimitThreshold(pub u32)`) have identical physical size (`4`), alignment (`4`), and field projections, so a structural-only MIR evaluator cannot distinguish a mutated function that swaps their return values (`q9_shape_preserving_nominal_return_swap_challenge`).
   - Binding the decoded `OpenAdtTable` (which records each nominal `adtHash`, `variantCount`, `fieldTypes`, `size`, `align`, and `isReprC`) to the consumer's expected nominal signature table (`checkOpenAdtTableMatchesExpected`) and joining captured layout descriptors to the universal `#[repr(C)]` offset/size recurrence (`c2_d3_captured_layout_to_repr_c_recurrence_and_mutations_verified`, `c2_d3_captured_layout_bound_universal_size_law`) rejects nominal type swaps, field-list substitutions, and layout-table mutations.
3. **Complete Charon ULLBC Local-Domain Validation (`c2_d4_complete_charon_local_domain_gate_rejects_both_ctrl6_and_ctrl7_unchecked_local_mutant`, `Post96Consumer.charon_acceptance_uses_complete_gate`)**:
   - [`support/portable_pr94_control.py`](support/portable_pr94_control.py) and [`support/pr94-audit-counterexamples-ledger.json`](support/pr94-audit-counterexamples-ledger.json) demonstrate that mutating a local variable's type in Charon's `.ullbc` JSON from `u32` (`Deduplicated(29)`) to `u64` (`HashConsedValue(U64)`) in `fun_decls[4].body.locals[2]` produces a 1,019-byte `.amir` mutant (`5342601cf574a1aa4dbc93ed73857f63de8d54e9f6ef125506222e2b0922e66a`) that passes a partial local-type gate checking only a subset of locals (`charon_gate_accepts_unchecked_local_type_change`).
   - The repaired gate `checkCompleteCharonLocalDomainGate` verifies all local variable types across every translated function declaration against the ULLBC local table (`c2_repaired_complete_charon_gate_rejects_unchecked_local_type_change`), and [`support/AnnealResearch/Post96ConsumerGenerated.lean`](support/AnnealResearch/Post96ConsumerGenerated.lean) (`actual_nominal_accepts`), [`support/AnnealResearch/Post96NativeConsumerGenerated.lean`](support/AnnealResearch/Post96NativeConsumerGenerated.lean) (`pointer_bad_argument_all_seeds`), and [`support/AnnealResearch/Post96ChallengeGenerated.lean`](support/AnnealResearch/Post96ChallengeGenerated.lean) (`accepted_graph_outcome`) verify the end-to-end generated artifacts produced by `rustc 1.100.0-nightly` (`923c95cdf5ba65cea505aa2ea829f578e1506ed8`).

### 4. Six-Dimension Incremental Cache Invalidation, Async Coroutine Hooks, and Lean 4 Proof-Cost Scaling

**Basis: source | execution | derived**

[`support/AnnealResearch/FrontendIncrementalFrontiers.lean`](support/AnnealResearch/FrontendIncrementalFrontiers.lean), [`support/AnnealResearch/FrontendIncrementalControls.lean`](support/AnnealResearch/FrontendIncrementalControls.lean), [`support/AnnealResearch/CostIncrementalAndFrontiers.lean`](support/AnnealResearch/CostIncrementalAndFrontiers.lean), and [`support/AnnealResearch/CostIncrementalAndFrontiersControls.lean`](support/AnnealResearch/CostIncrementalAndFrontiersControls.lean) formalize incremental verification reuse, compiler hook placement for 7 language frontiers, and Lean 4 proof-checking resource scaling:

- **Sound Per-Function Incremental Cache Key (`validateConfiguredProofCache_implies_verified_caller_cache_and_beta_contract`)**:
  - In a two-crate revision sequence (`alpha_rev0` $\to$ `alpha_rev1` internal refactor preserving `alpha`'s contract $\to$ `alpha_rev2` contract-breaking edit), caller `beta`'s decoded MIR body is identical across all three revisions (`beta_decoded_body_identical_across_all_revisions`).
  - Keying caller proof reuse on `(toolchain_id, flags_bitmask, crate_svh, decoded_body_hash, layout_table_hash, callee_contract_digest)` allows `beta` at `rev1` to reuse its `rev0` proof (`beta_rev1_verified_by_compositional_reuse`) while invalidating the cached proof at `rev2` when `alpha`'s contract changes (`alpha_rev2_falsifies_old_contract`).
  - Negative controls prove that caching by caller body hash alone is unsound when a callee's contract changes (`control_caller_body_only_cache_unsound_when_callee_contract_changes`), caching by `DefPathHash` alone accepts mutated bodies (`control_def_path_hash_only_cache_unsoundly_accepts_mutated_bodies`), and caching by whole-crate digest falsely invalidates unchanged callers (`control_whole_crate_digest_falsely_invalidates_unchanged_caller`).
- **Compiler Callback Hook Placement for Async Coroutines and Language Frontiers (`coroutine_closure_stolen_before_after_analysis_but_captured_in_elaborated_hook`, `all_seven_frontiers_captured_in_drops_elaborated_hook`)**:
  - Passive queries inside `after_analysis` lose `async` coroutine closure bodies because `rustc` steals the pre-optimization MIR during coroutine lowering (`control_after_analysis_passive_query_loses_async_coroutine_closure`). Hooking `mir_drops_elaborated_and_const_checked` captures all 7 frontier categories (trait dynamic dispatch vtables, `async` state machines and ordinary cancellation drop obligations, unsafe unions, pinning, interior mutability `UnsafeCell`, `extern "C"` FFI boundaries, and const generics).
- **Lean 4 Kernel Reduction Cost vs. Compiler Capture Cost (`lean_proof_checking_dominates_compiler_capture_wall_clock_and_rss`)**:
  - Across workspace and open-hash runs, `rustc_driver` capture completes in `18–382 ms` wall-clock time and `101–534 MiB` peak RSS, whereas Lean 4 kernel proof checking dominates both wall-clock time and memory:
    - In [`support/Post96LifecycleGenerated.lean.failed.txt`](support/Post96LifecycleGenerated.lean.failed.txt) (100,586 bytes, SHA-256 `c88d61017f795633934ec2c733d014899c21cd50887e466ace53d2b0149ad7979`), bundling 5 generated Cargo workspace cases into a single module and invoking monolithic `decide` over raw byte-list decoding exhausted the 768 MiB memory ceiling (`-M768`).
    - Similarly, `OpenHashMultiCrateR5R6R9R10.lean` (71,815 bytes) reaches `803,393,536` bytes (~766.2 MiB) peak RSS ([`support/pr94-audit-counterexamples-ledger.json`](support/pr94-audit-counterexamples-ledger.json)), failing under `-M768` at lines 572/583/605 (`(kernel) excessive memory consumption detected`) and succeeding in `15.45s` under `lean -j1 -M2048 -DElab.async=false` ([`support/lean-execution-ledger.json`](support/lean-execution-ledger.json)).
    - As documented in [`support/cargo-lean-cost-README.md`](support/cargo-lean-cost-README.md) and [`support/cargo_lean_cost_run_checks.py`](support/cargo_lean_cost_run_checks.py), decomposing generated Cargo verification obligations into per-case modules, hoisting `parseAcceptedMirPackageBytes` into top-level definitions, and proving record equality via `beq_iff_eq.mpr rfl` allows all 5 Cargo workspace cases (and the full 84-module repository closure) to verify under `lean -j1 -M2048 -DElab.async=false`.

## Boundaries

- **`not examined`**:
  - Distributed or remote build caching (`sccache`, Bazel remote execution) where `.amir` sidecars must be transported alongside `.rlib` artifacts across machines.
  - Procedural macro (`proc-macro`) host crates as verification subjects (host build scripts and proc-macros are filtered out as host-execution tooling rather than target verification subjects).
- **`unknown`**:
  - Whether future Lean 4 kernel bytecode evaluator improvements will reduce the RSS of `decide` / `rfl` reductions over 100+ KB generated AST literals enough to fit within a 768 MiB cap without per-case module sharding.
- **`known not to apply`**:
  - Reading `tcx.optimized_mir(def_id)` from external `.rlib` metadata cannot be used to verify pre-optimization `PlaceMention` or `StorageLive` / `StorageDead` obligations (`n5_external_rlib_optimized_mir_vs_postcleanup_sidecar_discriminator`).
  - Passive `after_analysis` queries cannot capture un-stolen `async` coroutine closure bodies (`control_after_analysis_passive_query_loses_async_coroutine_closure`).
  - Running `lean -j1 -M768` on `OpenHashMultiCrateR5R6R9R10.lean` or the unsharded `Post96LifecycleGenerated.lean.failed.txt` exceeds the 768 MiB heap limit (`803.4 MiB` peak RSS); `-M2048 -DElab.async=false` is required.
- **`unsupported`**:
  - Under `--driver-open-hash-mode`, ADTs with more than 3 scalar fields (`r5_control_unsupported_adt_arity_4_reject`), hash bucket exhaustion (`r5_control_hash_table_exhausted_modulus_4_reject`), and unclosed external call graphs (`r5_control_unclosed_external_cap_2_reject`) fail closed with exit code `2`.

## Evidence

| Artifact | Path | Description & SHA-256 |
| :--- | :--- | :--- |
| Lean Execution Ledger | [`support/lean-execution-ledger.json`](support/lean-execution-ledger.json) | Fresh Lean `4.34.1` (`-j1 -M2048 -DElab.async=false`) verification ledger across all 25 modules in topological order (`exit_code: 0`). |
| Incremental Frontiers & Controls | [`support/AnnealResearch/FrontendIncrementalFrontiers.lean`](support/AnnealResearch/FrontendIncrementalFrontiers.lean), [`support/AnnealResearch/FrontendIncrementalControls.lean`](support/AnnealResearch/FrontendIncrementalControls.lean), [`support/AnnealResearch/CostIncrementalAndFrontiers.lean`](support/AnnealResearch/CostIncrementalAndFrontiers.lean), [`support/AnnealResearch/CostIncrementalAndFrontiersControls.lean`](support/AnnealResearch/CostIncrementalAndFrontiersControls.lean) | 6-dimension incremental invalidation theorems, torn-write and provisional-certificate controls, and `mir_drops_elaborated` hook proofs. |
| Cargo Workspace Integration & Controls | [`support/AnnealResearch/CargoWorkspaceIntegration.lean`](support/AnnealResearch/CargoWorkspaceIntegration.lean), [`support/AnnealResearch/CargoWorkspaceIntegrationControls.lean`](support/AnnealResearch/CargoWorkspaceIntegrationControls.lean) | Multi-crate `RUSTC_WRAPPER` SVH binding, `build.rs` `OUT_DIR` binding, `strict_align` feature toggle proofs, and 5 workspace negative controls. |
| Open Hash Multi-Crate & Audit Counterexamples | [`support/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean`](support/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean), [`support/AnnealResearch/BuiltPhaseControlsR1.lean`](support/AnnealResearch/BuiltPhaseControlsR1.lean), [`support/AnnealResearch/CharonNativeAndControlsR3R4.lean`](support/AnnealResearch/CharonNativeAndControlsR3R4.lean), [`support/AnnealResearch/PR86AuditCounterexamples.lean`](support/AnnealResearch/PR86AuditCounterexamples.lean), [`support/AnnealResearch/PR92AuditCounterexamples.lean`](support/AnnealResearch/PR92AuditCounterexamples.lean), [`support/AnnealResearch/PR94AuditCounterexamples.lean`](support/AnnealResearch/PR94AuditCounterexamples.lean) | Open `DefPathHash` and `OpenAdtTable` proofs, `.rlib` vs. sidecar phase discriminator, Charon complete local-domain gate, and paired audit counterexamples/repairs. |
| Post-Audit Generated Consumer Pipeline | [`support/AnnealResearch/Post96LifecycleInterface.lean`](support/AnnealResearch/Post96LifecycleInterface.lean), [`support/AnnealResearch/Post96Consumer.lean`](support/AnnealResearch/Post96Consumer.lean), [`support/AnnealResearch/Post96ConsumerGenerated.lean`](support/AnnealResearch/Post96ConsumerGenerated.lean), [`support/AnnealResearch/Post96NativeConsumer.lean`](support/AnnealResearch/Post96NativeConsumer.lean), [`support/AnnealResearch/Post96NativeConsumerGenerated.lean`](support/AnnealResearch/Post96NativeConsumerGenerated.lean), [`support/AnnealResearch/Post96ChallengeGenerated.lean`](support/AnnealResearch/Post96ChallengeGenerated.lean), [`support/Post96LifecycleGenerated.lean.failed.txt`](support/Post96LifecycleGenerated.lean.failed.txt), [`support/post96-pipeline-README.md`](support/post96-pipeline-README.md) | End-to-end generated consumer modules from `rustc 1.100.0-nightly` plus the preserved 100,586-byte unsharded `-M768` failure specimen (`c88d6101...`). |
| Capture Scripts & Ledgers | [`support/run_workspace_capture.py`](support/run_workspace_capture.py), [`support/workspace-capture-ledger.json`](support/workspace-capture-ledger.json), [`support/run_n5_open_hash_and_rlib_phase.py`](support/run_n5_open_hash_and_rlib_phase.py), [`support/n5-open-hash-and-rlib-phase-ledger.json`](support/n5-open-hash-and-rlib-phase-ledger.json), [`support/portable_pr94_control.py`](support/portable_pr94_control.py), [`support/pr94-audit-counterexamples-ledger.json`](support/pr94-audit-counterexamples-ledger.json), [`support/cargo_lean_cost_run_checks.py`](support/cargo_lean_cost_run_checks.py), [`support/cargo-lean-cost-README.md`](support/cargo-lean-cost-README.md) | Empirical capture scripts and JSON ledgers for Cargo workspace builds, open-hash probes, Charon ULLBC local-type mutation controls, and `-M2048` proof-cost checks. |

## Revalidation

To re-verify the complete 25-module Lean 4 closure in [`support/AnnealResearch/`](support/AnnealResearch/) using Lean `4.34.1`:

```bash
mkdir -p /tmp/r17-build/AnnealResearch
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
  LEAN_PATH=/tmp/r17-build lean -j1 -M2048 -DElab.async=false \
    -o "/tmp/r17-build/AnnealResearch/${mod}.olean" \
    "support/AnnealResearch/${mod}.lean"
done
```

Expected outcome: Every module compiles with exit code `0` within the 2,048 MiB heap cap (`children_maxrss_kb <= 843772`), matching [`support/lean-execution-ledger.json`](support/lean-execution-ledger.json).
