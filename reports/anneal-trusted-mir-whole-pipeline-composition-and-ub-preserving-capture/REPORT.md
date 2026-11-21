# Whole-Pipeline `Trusted.MirSemantics` Pass Composition (`MirOptTrace`) and `MirProfileV2` (`PlaceMention` & `Assume`) UB-Preserving Capture Bridge

## Summary

Verifying optimized Rust MIR end-to-end against `Anneal`'s kernel-checked `Trusted.MirSemantics` requires both (a) composing heterogeneous intraprocedural pass families across arbitrary finite pass schedules without losing `WellFormed`, `Behavior`, `Diverges`, or per-item `UnitTheorem` / `CrateTheorem` obligations, and (b) closing two concrete syntax/operational gaps at the `Runtime(PostCleanup)` capture boundary (`compiler/rustc_mir_transform/src/lib.rs:684-691`) and the `Runtime(Optimized)` output boundary (`lib.rs:737, 787`). Directly importing `Trusted.MirAst` and `Trusted.MirSemantics` from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`support/AnnealTrustedMirWholePipelineAndProfileV2.lean`, `22961` lines, `1010855` bytes, SHA-256 `17ad008de106a6099b81341e86666989d9a7cf94345d9319c0c2debe58eb6497`) alongside live execution censuses on `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), `Miri`, and `google/zerocopy@e9bc37a4d2c0ad9be243f25db28ff21624d8102b` establishes four governing results:

1. **Arbitrary-length 5-family `MirOptTrace` composition & `CrateTheorem` / `UnitTheorem` VC transport directly over `Trusted.MirSemantics`.** Unifying dead-after-point `Operand.move -> Operand.copy` (`MirOptStep.moveToCopyDead`), `SimplifyCfg` branch pruning/collapse (`.simplifyCfgBranch`), algebraic `InstSimplify` & flow-sensitive constant propagation (`.instSimplifyAlgAndConst`), `CopyProp` / `DestinationPropagation` / totality-certified `DeadStoreElimination` (`.copyAndDestPropAndDse`), and `SimplifyLocals` trailing unused-local truncation (`.compactUnusedTrailingLocals`) into a single decidable validator `checkMirOptTrace` proves bidirectional `FullSemanticEquiv` (`↔`) and exact `CrateTheorem` / `UnitTheorem` transport (`mirOptTrace_crate_and_unit_vc_transport_iff`) across arbitrary finite pass sequences—demonstrated non-vacuously by a 5-step concrete `Program` witness (`witness_five_family_whole_pipeline_nonvacuous`) shrinking `localDecls` from `8` to `3`. `Basis: execution (Lean kernel)`
2. **Pre-`Runtime(PostCleanup)` `-Zmir-preserve-ub` UB-erasure gap (`RemovePlaceMention`, `lib.rs:687`).** `rustc` schedules `RemovePlaceMention` (`remove_place_mention.rs:12-14`, gated on `!mir_preserve_ub`) and `SimplifyCfg::PreOptimizations` (`simplify.rs:131-132`) *before* `MirPhase::Runtime(PostCleanup)`. Live `Miri` execution (`support/mir_preserve_ub_postcleanup_place_mention_census.json`) confirms that `unsafe { let _ = (*null_pair_ptr).1; }` faults immediate in-bounds pointer-offset UB (`rc = 1`) under default `Miri` (`-Zmir-preserve-ub=yes`), whereas `Miri -Zmir-preserve-ub=no -Zmir-opt-level=0` (matching default `Runtime(PostCleanup)`) erases `PlaceMention` and exits `rc = 0` (and native `-Zub-checks=yes` misses it even *with* `-Zmir-preserve-ub=yes`). Enabling `-Zmir-preserve-ub=yes` across `zerocopy` (`4,663` `PostCleanup` bodies) surfaces **`986` `PlaceMention` statements across `194` bodies (`16` with `*` derefs)**. `Basis: source + execution`
3. **`Runtime(Optimized)` `UnreachablePropagation` `Assume` cliff (`0 -> 385` `assume`s in `zerocopy`) & conservative `MirProfileV2` bridge.** While `zerocopy` `Runtime(PostCleanup)` has `0` `assume` statements, `Inline` (`+65` across `38` bodies) + `UnreachablePropagation` (`unreachable_prop.rs:18-21`, `mir_opt_level >= 2`, `+355` -> **`420` across `66` bodies**, with **`385` surviving across `58` final `Optimized` bodies**) synthesize `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume)` (`support/nondiverging_intrinsics_assume_and_unreachable_prop.json`). Extending `Trusted.MirAst.StatementKind` with `.placeMention` and `.assume` in `MirProfileV2` proves exact 1-to-1 conservative extension over `Trusted.MirSemantics` (`profileV2_conservative_extension_exact`), certified bidirectional soundness of RFC 2582 `RemovePlaceMention` (`removePlaceMention_certified_bidirectional_iff`), and certified bidirectional soundness of `SwitchInt -> .assume` `UnreachablePropagation` (`unreachableProp_switchBoolToAssume_bidirectional_iff`). `Basis: source + execution`
4. **Three-kernel + unmodified `TrustedBoundary.lean` Pass 1 `-M2048` verification.** `support/AnnealTrustedMirWholePipelineAndProfileV2.lean` compiles on `Lean v4.34.1` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` in **`40.9259 s` / `1371.73 MB` RSS** (`2530` module constants: `1075` public + `1455` private, `21 / 24` public theorems strictly `[propext]` and `3 / 24` `[propext, Quot.sound]`, `0` `Classical.choice`, `0` `sorryAx`, `0` `_unsafe_rec`), passes unmodified `TrustedBoundary.lean` `"preflight"` (`ok = true`; frozen `sorry` file rejected `rc = 1`) and Pass 1 `"audit"` under `-M2048` (`ok = true`, `replay = true`, `4111` replayed declarations, `axioms = ["propext", "Quot.sound"]`), and passes `Lean v4.35.0` (`39.4775 s`) + `lean4export 3.1.0` + external Rust `nanoda_bin 0.4.19` (`rc = 0`, `3616` declarations checked in **`2.4882 s` / `95.86 MB` RSS**; paired `[]` probe rejected fail-closed). `Basis: execution`

## Applicability

- **Primary formal target (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, citing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`):** `Trusted.MirAst.Program` and `Trusted.MirSemantics` ($M_{	ext{anneal}}$, `mirProfileVersion = 1`, `pointerWidthBits = 64`), whose operational rules cite upstream `rustc_const_eval` at `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`.
- **Upstream compiler passes & live execution toolchain:** Pass schedules and operational semantics are audited against `rust-lang/rust@412be32a6a189d9a28922beee178bc0abee9d492` (`run_runtime_cleanup_passes` and `run_optimization_passes` at `compiler/rustc_mir_transform/src/lib.rs:684-789`, `RemovePlaceMention` at `remove_place_mention.rs:1-25`, `SimplifyCfg` at `simplify.rs:130-350`, `UnreachablePropagation` at `unreachable_prop.rs:1-151`, and `PlaceMention` evaluation at `compiler/rustc_const_eval/src/interpret/step.rs:119-123`), while live `rustc` + `Miri` execution probes run on `rustc 1.102.0-nightly` (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and full-crate pass censuses measure `google/zerocopy@e9bc37a4d2c0ad9be243f25db28ff21624d8102b`. Between `8144389c895da997dbdecaa635e41d6a50be6ffd` and `412be32a6a189d9a28922beee178bc0abee9d492`, `remove_place_mention.rs`, `simplify.rs`, and `unreachable_prop.rs` are byte-identical (`0` diff), `step.rs:119-123` is unchanged, and `lib.rs` preserves identical relative pass ordering with a `+5`-line offset (`RemovePlaceMention` `L682 -> L687`, `UnreachablePropagation` `L732 -> L737`).
- **Independent Lean 4 kernel & exporter verification pins:** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, primary kernel + `TrustedBoundary.lean` Pass 1 replay), `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`, cross-version kernel), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@f55114afa24efe39e007f62d31b7e8ac4243f2a6` (`0.4.19`).

## Findings

### 1. `zerocopy` Capture-Boundary (`PlaceMention`) & Optimization-Boundary (`Assume`) Censuses

`Basis: source + execution (support/mir_preserve_ub_postcleanup_place_mention_census.json, support/nondiverging_intrinsics_assume_and_unreachable_prop.json)`

| Boundary / Configuration | `zerocopy` Bodies | `PlaceMention` Stmts (Bodies / `*` Derefs) | `Assume` Stmts (Bodies) | `Unreachable` Terminators (Bodies) |
| :--- | :---: | :---: | :---: | :---: |
| `Runtime(PostCleanup)` (`-Zmir-preserve-ub=no`, default) | `4,663` | `0` (`0` / `0`) | `0` (`0`) | `531` (`169`)* |
| `Runtime(PostCleanup)` (`-Zmir-preserve-ub=yes`, UB-preserving) | `4,663` | **`986` (`194` / `16`)** | `0` (`0`) | — |
| `UnreachablePropagation.before` (`-Copt-level=2 -Zmir-opt-level=2`) | `4,302` | `0` | `65` (`38`) | `1,172` (`807`) |
| `UnreachablePropagation.after` (`-Copt-level=2 -Zmir-opt-level=2`) | `4,302` | `0` | **`420` (`66`)** | `1,172` (`807`) |
| `InstSimplify-after-simplifycfg.before` (post-`SimplifyCfg` `lib.rs:738`) | `4,302` | `0` | `420` (`66`) | `780` (`780`, `-392`) |
| `SimplifyLocals-final.after` (`Runtime(Optimized)`) | `4,302` | `0` | **`385` (`58`)** | `768` (`768`) |

*\*Measured on the `4,302`-body `SimplifyCfg-pre-optimizations.after` dump in `support/nondiverging_intrinsics_assume_and_unreachable_prop.json`.*

Under default `rustc` flags (`-Zmir-preserve-ub=no`), `RemovePlaceMention` (`lib.rs:687`) runs inside `run_runtime_cleanup_passes` prior to `MirPhase::Runtime(PostCleanup)`, stripping all `986` `PlaceMention` statements across `194` `zerocopy` bodies (`16` containing `*` dereference projections) and erasing immediate in-bounds pointer-offset UB on `let _ = (*null_pair_ptr).1` (`Miri rc = 1` at `-Zmir-preserve-ub=yes` vs. `rc = 0` at `-Zmir-preserve-ub=no -Zmir-opt-level=0`). Downstream in `run_optimization_passes`, `Inline` introduces `65` `Assume` statements across `38` bodies and `UnreachablePropagation` (`lib.rs:737`, `unreachable_prop.rs:18-21`, enabled at `mir_opt_level >= 2`) synthesizes **`+355` additional `NonDivergingIntrinsic::Assume` statements** (`65 -> 420` across `66` bodies, followed immediately by `SimplifyCfg::AfterUnreachableEnumBranching` at `lib.rs:738` pruning `-392` `Unreachable` terminators and leaving **`385` `Assume`s across `58` bodies** at `Runtime(Optimized)`), establishing why whole-pipeline `PostCleanup -> Optimized` verification requires conservative `.placeMention` and `.assume` support (`MirProfileV2`).

### 2. Core Whole-Pipeline & `MirProfileV2` Theorems (`support/AnnealTrustedMirWholePipelineAndProfileV2.lean`)

`Basis: execution (Lean kernel)`

1. **`mirOptStep_sound_bidirectional_iff`:** Every certified pass family in `MirOptStep` (`.moveToCopyDead`, `.simplifyCfgBranch`, `.instSimplifyAlgAndConst`, `.copyAndDestPropAndDse`, and `.compactUnusedTrailingLocals`) preserves `FullSemanticEquiv` (`WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`, `SatisfiesPost`, and `BodyVerified` `↔`) directly on unmodified `Trusted.MirSemantics`.
2. **`mirOptTrace_sound_bidirectional_iff`:** Inductive composition over arbitrary finite pass schedules `trace : MirOptTrace` preserves `FullSemanticEquiv pPostCleanup pOptimized` (`↔`).
3. **`mirOptTrace_crate_and_unit_vc_transport_iff`:** Transports `CrateTheorem` and `UnitTheorem` (both whole-crate and per-`DefId` unit projections) bidirectionally (`↔`) across any certified `MirOptTrace` whenever `SpecsPropertyInvariant specs` holds.
4. **`profileV2_conservative_extension_exact`:** Embedding any `p : Trusted.MirAst.Program` into `MirProfileV2` steps in exact 1-to-1 lockstep (`mapStepResultV2ToV1 (evalStepV2 (embedProgramV1 p) c s) = evalStep p c s`) and preserves `WellFormed`, `Behavior`, `ReachesResult (.fault _)`, and `Diverges` (`↔`).
5. **`removePlaceMention_certified_bidirectional_iff`:** Erasing certified `.placeMention p` (`isSafePlaceMention p = true`, covering live locals and RFC 2582 zero-offset raw-pointer derefs while rejecting uncertified non-zero `inbounds` field-offset projections) to `.v1 .nop` preserves `FullSemanticEquivV2` (`↔`).
6. **`unreachableProp_switchBoolToAssume_bidirectional_iff`:** Rewriting `bb: stmts; SwitchInt(op) -> [0: bb_empty_unreachable, otherwise: bb_next]` into `bb: stmts ++ [.assume op]; Goto bb_next` on certified `.bool` operands preserves `FullSemanticEquivV2` (`↔`, including `.fault .unreachableExecuted` and `DivergesV2`).

Complete public theorem inventory (`24` theorems):

- `VrustcFormal.F1_9.mirOptStep_sound_bidirectional_iff`
- `VrustcFormal.F1_9.mirOptTrace_sound_bidirectional_iff`
- `VrustcFormal.F1_9.mirOptTrace_crate_and_unit_vc_transport_iff`
- `VrustcFormal.F1_9.profileV2_conservative_extension_exact`
- `VrustcFormal.F1_9.removePlaceMention_certified_bidirectional_iff`
- `VrustcFormal.F1_9.unreachableProp_switchBoolToAssume_bidirectional_iff`
- `VrustcFormal.F1_9.reaches_head_det`
- `VrustcFormal.F1_9.execOutcome_reaches_inv`
- `VrustcFormal.F1_9.execOutcome_terminal`
- `VrustcFormal.F1_9.positiveCanary_of_execReturns`
- `VrustcFormal.F1_9.negativeCanary_of_execFaults`
- `VrustcFormal.F1_9.reachesV2_head_det`
- `VrustcFormal.F1_9.evalBodyV2_reaches_inv`
- `VrustcFormal.F1_9.evalBodyV2_terminal`
- `VrustcFormal.F1_9.positiveCanaryV2_of_execReturnsV2`
- `VrustcFormal.F1_9.negativeCanaryV2_of_execFaultsV2`
- `VrustcFormal.F1_9.ce1_uninit_switchBranch_erases_ub`
- `VrustcFormal.F1_9.ce2_removePlaceMention_null_nonzero_offset_erases_ub`
- `VrustcFormal.F1_9.ce3_rfc2582_zero_offset_raw_deref_placeMention_defined`
- `VrustcFormal.F1_9.ce4_assume_false_faults_unreachableExecuted`
- `VrustcFormal.F1_9.ce5_compactTrailingLocals_referenced_slot_unsound`
- `VrustcFormal.F1_9.ce6_pipeline_clobbered_copyprop_unsound`
- `VrustcFormal.F1_9.witness_five_family_whole_pipeline_nonvacuous`
- `VrustcFormal.F1_9.witness_profileV2_placeMention_and_assume_pipeline`

Composing this unified `MirOptTrace` verifier with the pass-specific formalizations in `reports/anneal-trusted-mir-simplifycfg-branch-folding-and-dead-block-compaction/`, `reports/anneal-trusted-mir-gvn-instsimplify-algebraic-and-discriminant-folding/`, `reports/anneal-trusted-mir-jump-threading-and-dataflow-const-prop/`, `reports/anneal-trusted-mir-copyprop-dse-and-destination-propagation/`, and `reports/anneal-mir-r3-local-compaction-fast-cert-checking-and-scc-olean-sharding/` establishes a continuous machine-checked verification spine from `Runtime(PostCleanup)` to `Runtime(Optimized)`.

## Boundaries

1. **Intraprocedural scalar/unprojected `mirProfileVersion = 1` subset vs. interprocedural `Inline` & aggregate projections (`known not to apply`).** `MirOptStep` operates over `Trusted.MirAst.Program` (where `TerminatorKind.call` and non-empty place projections step fail-closed to `.fault .unsupported`); `PlaceV2.rawDeref` and `PlaceV2.rawDerefFieldOffset` model raw-pointer address/offset checks over scalar pointer slots in `MirProfileV2` without introducing full byte-addressed heap aliasing.
2. **Trailing unused-local truncation vs. arbitrary non-contiguous index compaction.** `.compactUnusedTrailingLocals` truncates unused trailing local declarations `idx >= newCount`; non-contiguous dead-slot reindexing composes via `reports/anneal-mir-r3-local-compaction-fast-cert-checking-and-scc-olean-sharding/`.
3. **Certificate soundness sufficiency vs. semantic completeness.** `checkMirOptStep`, `checkRemovePlaceMentionProgram`, and `checkUnreachablePropAssumeProgram` are decidable sufficiency checkers (`= true -> FullSemanticEquiv`), not complete semantic oracles.

## Evidence

- `support/AnnealTrustedMirWholePipelineAndProfileV2.lean` — `22961`-line zero-`sorry` Lean 4 proof module (`SHA-256 17ad008de106a6099b81341e86666989d9a7cf94345d9319c0c2debe58eb6497`), byte-for-byte faithful to frozen theorem-statement SHA-256 `736eba4848cb0e5984de2874413eafc375e073f8a174a94fd88530216c986b4c`.
- `support/AnnealTrustedMirWholePipelineAndProfileV2.frozen.sha256` — frozen theorem-statement and completed proof SHA-256 digests.
- `support/multi_kernel_verification_summary.json` — multi-kernel (`Lean v4.34.1` `-M2048`, `Lean v4.35.0`, `lean4export 3.1.0`, `nanoda_bin 0.4.19`) and unmodified `TrustedBoundary.lean` `"preflight"` + Pass 1 `"audit"` receipts (`replayedDeclarations = 4111`, `reachableDeclarations = 4966`, `axioms = ["propext", "Quot.sound"]`).
- `support/mir_preserve_ub_postcleanup_place_mention_census.json` — live `rustc 1.102.0-nightly` + `Miri` `-Zmir-preserve-ub` pre-`PostCleanup` execution matrix and `4,663`-body `zerocopy` `PlaceMention` census.
- `support/nondiverging_intrinsics_assume_and_unreachable_prop.json` — live `4,302`-body `zerocopy` `UnreachablePropagation` `Assume` synthesis census and `Miri` `Assume`/`CopyNonOverlapping` execution matrix.

## Revalidation

1. **Synchronous `Lean v4.34.1` & `TrustedBoundary.lean` Pass 1 Audit (`-M2048`):**
   Compile `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, then compile `support/AnnealTrustedMirWholePipelineAndProfileV2.lean` with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`, `0` warnings, `0` `Classical.choice`, `21 / 24` public theorems `[propext]` and `3 / 24` `[propext, Quot.sound]`) and run `TrustedBoundary.lean` in `"preflight"` and `"audit"` modes.
2. **External Rust Kernel Check (`nanoda_bin 0.4.19`):**
   Compile on `Lean v4.35.0`, export public theorems via `leanexport`, and verify with `nanoda_bin` under `permitted_axioms: ["propext", "Quot.sound"]` (`rc = 0`) and `permitted_axioms: []` (`rc != 0`).
