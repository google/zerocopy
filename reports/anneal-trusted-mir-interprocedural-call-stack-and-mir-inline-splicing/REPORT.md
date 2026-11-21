# Interprocedural Call-Stack Semantics and MIR `Inline` CFG Splicing Reduction Directly Into `Anneal`'s `Trusted.MirSemantics`

## Summary

In `Anneal`'s intraprocedural TCB semantics (`Trusted/MirSemantics.lean:1568`, `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`), every `TerminatorKind.call` steps fail-closed to `.fault .unsupported`. Across `google/zerocopy@57cef100c3801df512085bf83ec29bbcaae9efae` (`0.8.48`, `cargo rustc --lib` default features, `4,302` MIR bodies on `rustc 1.102.0-nightly`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), enabling `rustc_mir_transform::inline::Inline` (`CARGO_INCREMENTAL=0 -C opt-level=2`) eliminates **`45.74%` (`-2,491`: `5,446 -> 2,955`)** of all `Call` terminators and raises `100%` call-free bodies from **`56.72%` (`2,440`) to `71.22%` (`3,064`, `+624` bodies)** (`support/mir_inlining_zerocopy_call_census.json`). Directly importing `Trusted.MirAst` and `Trusted.MirSemantics` with zero surrogate MIR AST types (`support/AnnealTrustedMirInterprocCallAndMirInline.lean`, `9821` lines, `415713` bytes, SHA-256 `00a984517497cecb2022d7fe363782f7fcf982fbbc22ecb8af5071d2405962d8`) establishes four core results:

1. **Exact conservative interprocedural call-stack extension over unmodified `Trusted.MirAst.Program` (`interproc_conservative_extension_exact`).** Extending `Trusted.MirSemantics.evalStep` with an explicit call-continuation stack (`InterprocState`, delegating every statement directly to `evalStatement` and every non-`.call`/non-`.return_` terminator to `evalTerminator`) agrees 1-for-1 on single-frame non-`.call` steps and coincides bidirectionally (`↔`) with `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`, `CrateTheorem`, and `UnitTheorem` on every call-free `Program`. `Basis: execution (Lean kernel)`
2. **Certified MIR `Inline` call-site splicing soundness (`mirInlineCallSite_sound_bidirectional_iff` & `mirInlineTrace_sound_bidirectional_iff`).** Mechanizing `rustc_mir_transform::inline::Integrator` (`compiler/rustc_mir_transform/src/inline.rs:864-1355`)—local/block shifting, prologue `StorageLive` + left-to-right argument-binding assignments (preserving `Operand.move` deinitialization and fault ordering), non-cleanup `.return_ -> .goto exitBlock` rewriting, and epilogue `dst = move ⟨localBase, []⟩` + `StorageDead` reset (preserving loop re-entry and recursion safety)—proves bidirectional `FullSemanticEquivInterproc` (`↔`, including constructive `0`-`Classical.choice` `DivergesInterproc`) across arbitrary finite `InlineTrace` sequences. `Basis: source + execution`
3. **Interprocedural-to-intraprocedural reduction and vertical VC transport (`mirInlineTrace_reduces_interproc_to_intraproc_trusted` & `mirInline_then_postInline_vc_transport`).** Whenever a finite `InlineTrace` reduces a multi-function crate `pSrc` to a call-free `pCallFree` (and optionally any post-inline intraprocedural pipeline `pCallFree -> pOpt` certified by `reports/anneal-trusted-mir-whole-pipeline-composition-and-ub-preserving-capture/`), interprocedural `CrateTheoremInterproc ⟨pSrc, specs⟩` and `UnitTheoremInterproc ⟨pSrc, specs⟩` hold if and only if Anneal's unmodified intraprocedural `Trusted.MirSemantics.CrateTheorem` / `UnitTheorem` holds on `pCallFree` (or `pOpt`). Six constructive sharpness counterexamples (`CE1`–`CE6`) and a two-hop loop-re-entry witness (`witness_two_hop_inline_reduces_to_trusted_intraproc`, `main -> helper_a -> helper_b`) verify non-vacuity. `Basis: execution (Lean kernel)`
4. **Three-kernel + unmodified `TrustedBoundary.lean` Pass 1 `-M2048` verification.** `support/AnnealTrustedMirInterprocCallAndMirInline.lean` compiles on `Lean v4.34.1` (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) in **`18.4667 s` / `636.21 MB` RSS** (`911` module constants: `373` public + `538` private, `25 / 25` strictly `[propext]`, `0` `Classical.choice`, `0` `sorryAx`, `0` `_unsafe_rec`), passes unmodified `TrustedBoundary.lean` `"preflight"` (`ok = true`; frozen `sorry` file rejected `rc = 1`) and Pass 1 `"audit"` under `-M2048` (`ok = true`, `replay = true`, `2492` replayed declarations, `axioms = ["propext"]`), and passes `Lean v4.35.0` (`16.8162 s`) + `lean4export 3.1.0` + external Rust `nanoda_bin 0.4.19` (`rc = 0`, `2113` declarations checked in **`1.2662 s` / `65.58 MB` RSS**; paired `[]` check rejected fail-closed). `Basis: execution`

## Applicability

- **Primary formal target (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, citing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`):** Unmodified `Trusted.MirAst.Program` and `Trusted.MirSemantics` ($M_{\text{anneal}}$, `mirProfileVersion = 1`, `pointerWidthBits = 64`), where `TerminatorKind.call` currently faults `.unsupported` (`Trusted/MirSemantics.lean:1568`).
- **Upstream compiler pass & live execution toolchain:** Audited against `rust-lang/rust@412be32a6a189d9a28922beee178bc0abee9d492` (`Inline` at `compiler/rustc_mir_transform/src/inline.rs:44`, `ForceInline` at `L75`, `try_inlining` at `L610`, `inline_call` at `L864`, and `Integrator` at `L1172`; compared with `8144389c895da997dbdecaa635e41d6a50be6ffd`, `inline.rs` differs by 34 lines shifting `Integrator` from `L1162` to `L1172` with identical splicing structure), with live `zerocopy` census measurements on `rustc 1.102.0-nightly` (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and `google/zerocopy@57cef100c3801df512085bf83ec29bbcaae9efae` (`0.8.48`, `--lib` default features).
- **Independent Lean 4 kernel & exporter verification pins:** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, primary kernel + `TrustedBoundary.lean` Pass 1 replay), `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`, cross-version kernel), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@f55114afa24efe39e007f62d31b7e8ac4243f2a6` (`0.4.19`).

## Findings

### 1. `zerocopy` MIR `Inline` Call-Elimination Census

`Basis: execution (support/mir_inlining_zerocopy_call_census.json)`

| Pipeline Point (`cargo rustc --lib`, default features, `CARGO_INCREMENTAL=0 -C opt-level=2`) | `zerocopy` Bodies | `100%` Call-Free Bodies | Call-Free Share | Total `Call` Terminators |
| :--- | :---: | :---: | :---: | :---: |
| `ForceInline.before` | `4,304` | `2,440` | `56.69%` | `5,448` |
| `Inline.before` | `4,302` | `2,440` | `56.72%` | `5,446` |
| `Inline.after` | `4,302` | **`3,064` (`+624`)** | **`71.22%`** | **`2,955` (`-2,491` / `-45.74%`)** |

Enabling MIR `Inline` directly unlocks `+624` additional `zerocopy` bodies into `Anneal`'s unmodified intraprocedural call-free verification envelope without requiring per-callee manual contracts, provided the inlining splice itself is proved bidirectionally faithful to interprocedural call-stack execution.

### 2. Core Interprocedural & MIR `Inline` Reduction Theorems (`support/AnnealTrustedMirInterprocCallAndMirInline.lean`)

`Basis: execution (Lean kernel)`

1. **`interproc_conservative_extension_exact`:** Single-frame non-`.call` steps of `evalStepInterproc` coincide identically with `Trusted.MirSemantics.evalStep`, and on any `isCallFreeProgram p = true` program all semantic judgments (`WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`, `CrateTheorem`, and `UnitTheorem`) match bidirectionally (`↔`).
2. **`mirInlineCallSite_sound_bidirectional_iff` & `mirInlineTrace_sound_bidirectional_iff`:** Certified `Integrator`-style call-site splicing preserves `FullSemanticEquivInterproc` (`↔`) across single and arbitrary finite `InlineTrace` sequences, including loop re-entry (via epilogue `StorageDead` reset on shifted callee locals) and nested calls.
3. **`mirInlineTrace_reduces_interproc_to_intraproc_trusted` & `mirInline_then_postInline_vc_transport`:** When an `InlineTrace` produces a call-free program `pCallFree` (and optionally composes with any post-inline intraprocedural `FullSemanticEquiv pCallFree pOpt`), interprocedural `CrateTheoremInterproc` / `UnitTheoremInterproc` on multi-function `pSrc` reduces bidirectionally (`↔`) to Anneal's unmodified intraprocedural `Trusted.MirSemantics.CrateTheorem` / `UnitTheorem` on `pCallFree` / `pOpt`.

Complete public theorem inventory (`25` theorems):

- `VrustcFormal.F1_10.interproc_conservative_extension_exact`
- `VrustcFormal.F1_10.mirInlineCallSite_sound_bidirectional_iff`
- `VrustcFormal.F1_10.mirInlineTrace_sound_bidirectional_iff`
- `VrustcFormal.F1_10.mirInlineTrace_reduces_interproc_to_intraproc_trusted`
- `VrustcFormal.F1_10.mirInline_then_postInline_vc_transport`
- `VrustcFormal.F1_10.reaches_head_det`
- `VrustcFormal.F1_10.execOutcome_reaches_inv`
- `VrustcFormal.F1_10.execOutcome_terminal`
- `VrustcFormal.F1_10.positiveCanary_of_execReturns`
- `VrustcFormal.F1_10.negativeCanary_of_execFaults`
- `VrustcFormal.F1_10.reachesInterproc_head_det`
- `VrustcFormal.F1_10.evalInterprocFuel_reaches_inv`
- `VrustcFormal.F1_10.evalInterprocFuel_terminal`
- `VrustcFormal.F1_10.positiveCanaryInterproc_of_execReturnsInterproc`
- `VrustcFormal.F1_10.negativeCanaryInterproc_of_execFaultsInterproc`
- `VrustcFormal.F1_10.evalInterprocFuel_append`
- `VrustcFormal.F1_10.evalInterprocChunks_to_fuel`
- `VrustcFormal.F1_10.positiveCanaryInterproc_of_execReturnsInterprocChunks`
- `VrustcFormal.F1_10.ce1_uninit_arg_ub_fires_before_callee_entry`
- `VrustcFormal.F1_10.ce2_unshifted_callee_local_clobbers_caller_state`
- `VrustcFormal.F1_10.ce3_missing_prologue_storageLive_causes_dead_local_ub`
- `VrustcFormal.F1_10.ce4_self_recursive_call_rejected`
- `VrustcFormal.F1_10.ce5_dead_dst_faults_on_return_and_callee_fault_precedes_dst_write`
- `VrustcFormal.F1_10.ce6_callee_storageDead_zero_rejected`
- `VrustcFormal.F1_10.witness_two_hop_inline_reduces_to_trusted_intraproc`

Composing this interprocedural MIR `Inline` bridge with `reports/rustc-mir-inlining-call-graph-splicing-and-incremental-policy-soundness/` and `reports/anneal-trusted-mir-whole-pipeline-composition-and-ub-preserving-capture/` connects multi-function call-graph inlining directly to our verified intraprocedural optimization spine (`SimplifyCfg`, `GVN`/`InstSimplify`, `JumpThreading`/`DataflowConstProp`, `CopyProp`/`DSE`/`DestProp`, and `SimplifyLocals`).

## Boundaries

1. **Direct static `DefId` calls vs. indirect function pointers, virtual dispatch, & unwinding cleanups (`known not to apply`).** `evalStepInterproc` models direct `TerminatorKind.call callee args dst target unwind` over `mirProfileVersion = 1` supported values (`.bool`, `.int`, `.unit`, `.never`, and admitted fieldless `.enum`) with unprojected `dst` and non-cleanup call blocks—including self-recursive calls (`CE4`, 4-frame `rec(3) = 3`) and diverging calls (`target = none`, faulting `.undefined` on return)—while failing closed (`.fault .unsupported`) on indirect calls, unwinding across cleanups (`TerminatorKind.unwindResume`), cleanup call blocks, and projected return destinations (`*ptr` / `slice[idx]`). `checkMirInlineCallSite` additionally requires normal return targets (`target = some retBb`), non-self-recursive call sites (`callerDefId ≠ calleeDefId`, `CE4`), and `bodyHasNoStorageDeadZero calleeSrc` (`CE6`), rejecting all other call shapes fail-closed.
2. **Sufficiency of `checkMirInlineCallSite` vs. semantic completeness.** `checkMirInlineCallSite` certifies `Integrator`-shaped call-site splices; arbitrary interprocedural transformations (such as recursive call unrolling or cross-crate ABI-changing target-feature mismatches) are out of scope.
3. **Inherited `Trusted.MirSemantics` (`mirProfileVersion = 1`) envelope.** Value-only entry parameters (`callerMem = ⟨[]⟩`), `pointerWidthBits = 64`, and fail-closed `.fault .unsupported` on `assert`, `unwindResume`, references, raw pointers, and aggregate projections are inherited unchanged from `Trusted/MirSemantics.lean`.

## Evidence

- `support/AnnealTrustedMirInterprocCallAndMirInline.lean` — `9821`-line zero-`sorry` Lean 4 proof module (`SHA-256 00a984517497cecb2022d7fe363782f7fcf982fbbc22ecb8af5071d2405962d8`), byte-for-byte faithful to frozen theorem-statement SHA-256 `657b896a9155b50d7eda819579839825bef70d80ed283e8008f9edb9796f92c7`.
- `support/AnnealTrustedMirInterprocCallAndMirInline.frozen.sha256` — frozen theorem-statement and completed proof SHA-256 digests.
- `support/multi_kernel_verification_summary.json` — multi-kernel (`Lean v4.34.1` `-M2048`, `Lean v4.35.0`, `lean4export 3.1.0`, `nanoda_bin 0.4.19`) and unmodified `TrustedBoundary.lean` `"preflight"` + Pass 1 `"audit"` receipts (`replayedDeclarations = 2492`, `reachableDeclarations = 3313`, `axioms = ["propext"]`).
- `support/mir_inlining_zerocopy_call_census.json` — live `rustc 1.102.0-nightly` `4,302`-body `zerocopy` MIR `Inline` `Call`-terminator elimination census.

## Revalidation

1. **Synchronous `Lean v4.34.1` & `TrustedBoundary.lean` Pass 1 Audit (`-M2048`):**
   Compile `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, then compile `support/AnnealTrustedMirInterprocCallAndMirInline.lean` with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`, `0` warnings, `25 / 25` strictly `[propext]`, `0` `Classical.choice`) and run `TrustedBoundary.lean` in `"preflight"` and `"audit"` modes.
2. **External Rust Kernel Check (`nanoda_bin 0.4.19`):**
   Compile on `Lean v4.35.0`, export all `25` public theorems via `leanexport`, and verify with `nanoda_bin` under `permitted_axioms: ["propext", "Quot.sound"]` (`rc = 0`) and `permitted_axioms: []` (`rc != 0`).
