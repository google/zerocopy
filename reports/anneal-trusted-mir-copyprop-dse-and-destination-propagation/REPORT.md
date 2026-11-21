# Direct `Trusted.MirSemantics` Verification of `CopyProp`, `DeadStoreElimination`, `Rvalue::is_safe_to_remove` UB-Erasure Guarding, and `DestinationPropagation`

## Summary

Immediately following `SimplifyCfg::Final` (`compiler/rustc_mir_transform/src/lib.rs:771-779`), `rustc_mir_transform` executes `StripDebugInfo`, `CopyProp`, `DeadStoreElimination::Final`, `DestinationPropagation` (or mutually exclusive `TailCopyToMove` + opt-in `MoveElimination` at `lib.rs:777-778`), and `SimplifyLocals::Final` to eliminate intermediate copies, dead assignments, temporary destinations, and unused local declarations. Directly importing `Trusted.MirAst` and `Trusted.MirSemantics` from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`support/AnnealTrustedMirCopyPropDseDestProp.lean`, `13740` lines, `635756` bytes, SHA-256 `297c11c1ce141ed0f6287351140460f9c47b2c5ae8ff42abdd471fd254e72837`) alongside live execution probes on `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), `Miri`, and `google/zerocopy@e9bc37a4d2c0ad9be243f25db28ff21624d8102b` establishes four governing results:

1. **Live `rustc` + `Miri` `-Zmir-preserve-ub` UB-erasure mechanism across `DeadStoreElimination`, `SimplifyLocals`, and `StripDebugInfo` (`statement.rs:775-810`).** Both `DeadStoreElimination` (`dead_store_elimination.rs:95-99`, via `MaybeTransitiveLiveLocals::can_be_removed_if_dead` at `compiler/rustc_mir_dataflow/src/impls/liveness.rs:226-238` calling `rvalue.is_safe_to_remove()` at `L233`) and `SimplifyLocals` (`simplify.rs:581`) gate dead-assignment removal on `Rvalue::is_safe_to_remove()` (`compiler/rustc_middle/src/mir/statement.rs:775-810`), which returns `true` for `Rvalue::Use(Operand::Copy(*p))` (null/dangling dereference) and `Rvalue::BinaryOp(BinOp::Div, ...)` (`x / 0`) without checking `mir_preserve_ub`. Live `Miri` execution (`support/e3_10_copyprop_dse_simplifylocals_miri_and_zerocopy.json`, `10` specimens × `6` flag configurations = `60` runs) proves that surface Rust `let _unused = unsafe { *core::ptr::null::<u32>() };` and `let _unused = unsafe { unchecked_div(10, 0) };` only preserve UB at `-Zmir-opt-level=2 -Zmir-preserve-ub=yes` because THIR->MIR attaches `VarDebugInfo` (`debuginfo_locals`); enabling `-Zmir-strip-debuginfo=locals-in-tiny-functions` (used when building `core`) or executing on compiler-generated / custom-MIR locals without `VarDebugInfo` strips that protection and flips `Miri` from `rc = 1` (`Undefined Behavior`) to **`rc = 0` (`0` diagnostics)**. `Basis: source + execution`
2. **Direct `Trusted.MirSemantics` soundness & certified VC transport for `CopyProp`, `DeadStoreElimination`, and `DestinationPropagation`.** In `support/AnnealTrustedMirCopyPropDseDestProp.lean`, `CopyProp` copy-class propagation and single-use `move`-head unification preserve `FullSemanticEquiv` (`↔`) when source/destination slots are certified live and unmodified across the propagated span; `DeadStoreElimination` is unconditionally forward-sound (`ForwardCodegenRefines`) when the dead RHS does not `move` a live local `l != dst` while requiring flow-sensitive totality/liveness certification for reverse VC transport (`↔`); and `DestinationPropagation` (`_tmp = rval; _dst = move/copy _tmp -> _dst = rval; .nop`) is bidirectionally sound (`↔`) including on self-referential updates (`_tmp = _dst + 1; _dst = move _tmp -> _dst = _dst + 1; .nop`) because `evalStatement` evaluates `evalRvalue` before `writePlace`. `Basis: execution (Lean kernel)`
3. **Full-crate `zerocopy` post-`SimplifyCfg-final` optimization-tail census.** Across `google/zerocopy@e9bc37a4d2c0ad9be243f25db28ff21624d8102b` (`4,302` MIR bodies at `-C opt-level=2`), `CopyProp` eliminates **`-138` total assignments (`12,916 -> 12,778`)**—including **`-133` trivial `copy`/`move` assignments (`-43.3%`: `307 -> 174`)**—and `-299` storage markers, `DeadStoreElimination-final` eliminates `-6` assignments and `-14` storage markers, `DestinationPropagation` eliminates **`-58` assignments (`-33.3%` of remaining `copy`/`move` assignments: `174 -> 116`)** and `-175` storage markers, and `SimplifyLocals-final` then prunes **`-269` unused local declarations (`17,037 -> 16,768`)**. `Basis: execution`
4. **Three-kernel + unmodified `TrustedBoundary.lean` Pass 1 `-M2048` verification.** `support/AnnealTrustedMirCopyPropDseDestProp.lean` compiles on `Lean v4.34.1` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` in **`26.0586 s` / `953.69 MB` RSS** (`1308` module constants: `485` public + `823` private, `0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `_unsafe_rec`), passes unmodified `TrustedBoundary.lean` `"preflight"` (`ok = true`; frozen `sorry` file rejected `rc = 1`) and Pass 1 `"audit"` under `-M2048` (`ok = true`, `replay = true`, `2889` replayed declarations, `axioms = ["propext"]`), and passes `Lean v4.35.0` (`26.7323 s`) + `lean4export 3.1.0` + external Rust `nanoda_bin 0.4.19` (`rc = 0`, `2590` declarations checked in **`1.863 s` / `73.46 MB` RSS**; paired `[]` probe rejected fail-closed). `Basis: execution`

## Applicability

- **Primary formal target (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, citing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`):** `Trusted.MirAst.Program` and `Trusted.MirSemantics` ($M_{	ext{anneal}}$, `mirProfileVersion = 1`, `pointerWidthBits = 64`), whose operational rules (`deinitMovedPlace = true`, checked scalar arithmetic, storage-liveness markers) cite upstream `rustc_const_eval` at `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`.
- **Upstream compiler passes & live execution toolchain:** Pass implementations are audited against `rust-lang/rust@412be32a6a189d9a28922beee178bc0abee9d492` (`StripDebugInfo` at `compiler/rustc_mir_transform/src/strip_debuginfo.rs:12-50`, `CopyProp` at `copy_prop.rs:22-194`, `DeadStoreElimination` at `dead_store_elimination.rs:34-163` + `compiler/rustc_mir_dataflow/src/impls/liveness.rs:226-238`, `DestinationPropagation` at `dest_prop.rs:154-672`, `SimplifyLocals` at `simplify.rs:423-645`, and `Rvalue::is_safe_to_remove` at `compiler/rustc_middle/src/mir/statement.rs:775-810`), while live `rustc` + `Miri` execution probes run on `rustc 1.102.0-nightly` (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and full-crate pass censuses measure `google/zerocopy@e9bc37a4d2c0ad9be243f25db28ff21624d8102b`.
- **Independent Lean 4 kernel & exporter verification pins:** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, primary kernel + `TrustedBoundary.lean` Pass 1 replay), `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`, cross-version kernel), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`0.4.19`).

## Findings

### 1. Live `Miri` `-Zmir-preserve-ub` UB Erasure via `Rvalue::is_safe_to_remove()` + `StripDebugInfo`

`Basis: source + execution (support/e3_10_copyprop_dse_simplifylocals_miri_and_zerocopy.json)`

Neither `DeadStoreElimination::policy` (`dead_store_elimination.rs:151-153`) nor `SimplifyLocals::policy` (`simplify.rs:432-434`) checks `ctx.opts.unstable_opts.mir_preserve_ub`, and both rely on `Rvalue::is_safe_to_remove()` (`statement.rs:775-810`), which excludes only `CastKind::PointerExposeProvenance` while returning `true` for `Rvalue::Use` (including dereferences `*p`), `Rvalue::BinaryOp` (including `Div`/`Rem` by zero and `AddUnchecked`), and `Rvalue::Discriminant`. Live execution across `10` specimens × `6` flag configurations (`60` runs; `6` representative specimens tabulated below) reveals why surface Rust bindings normally appear protected—and when that accidental protection collapses:

| Specimen | `opt0` (`-Zmir-preserve-ub=yes`) | `+SimplifyLocals` / `+DSE` | `opt2` (`-Cdebuginfo=0`) | `opt2 + -Zmir-strip-debuginfo=locals-in-tiny-functions` | Root Cause |
| :--- | :---: | :---: | :---: | :---: | :--- |
| `surface_null_deref_named_binding` (`let _unused = *null;`) | `rc = 1` (UB) | `rc = 1` (UB) | `rc = 1` (UB) | `rc = 1` (`main` ends in `Call`, not `Return`) | `VarDebugInfo` keeps `_unused` in `debuginfo_locals(body)` |
| `surface_null_deref_bitor_unnamed_temp` (`let _ = (*null) \| 0;`) | `rc = 1` (UB) | `rc = 1` (UB) | `rc = 1` (UB) | `rc = 1` (UB) | `let _ = expr` emits `PlaceMention`, and `RemovePlaceMention` (`remove_place_mention.rs:12-14`) checks `!mir_preserve_ub` |
| `surface_tiny_fn_unchecked_div_zero_strip_debuginfo` (`fn tiny_div`) | `rc = 1` (UB) | `rc = 1` (UB) | `rc = 1` (UB) | **`rc = 0` (UB erased!)** | `StripDebugInfo` drops `VarDebugInfo` in 1-BB fn -> `DSE`/`SimplifyLocals` erases `unchecked_div(10, 0)` |
| `surface_tiny_fn_null_deref_strip_debuginfo` (`fn tiny_deref`) | `rc = 1` (UB) | `rc = 1` (UB) | `rc = 1` (UB) | **`rc = 0` (UB erased!)** | `StripDebugInfo` drops `VarDebugInfo` in 1-BB fn -> `DSE`/`SimplifyLocals` erases `*null` |
| `custom_mir_div_zero_dead_local` (`dead = x / z` at `z = 0`) | `rc = 1` (UB) | **`rc = 0` (UB erased!)** | **`rc = 0` (UB erased!)** | **`rc = 0` (UB erased!)** | No `VarDebugInfo` -> `SimplifyLocals` & `DSE` both erase `dead = x / 0` immediately |
| `custom_mir_null_deref_dead_local` (`dead = *null`) | `rc = 1` (UB) | **`rc = 0` (UB erased!)** | **`rc = 0` (UB erased!)** | **`rc = 0` (UB erased!)** | No `VarDebugInfo` -> `SimplifyLocals` & `DSE` both erase `dead = *null` immediately |

### 2. Direct `Trusted.MirSemantics` Soundness & Sharpness Theorems (`support/AnnealTrustedMirCopyPropDseDestProp.lean`)

`Basis: execution (Lean kernel)`

`support/AnnealTrustedMirCopyPropDseDestProp.lean` mechanizes six core pass-soundness and VC-transport theorems alongside fifteen adequacy and sharpness theorems directly over `Trusted.MirAst.Program` and `Trusted.MirSemantics`:

1. **`copyProp_certified_bidirectional_iff`:** Certified `CopyProp` rewriting `.copy tmp` uses to `.copy src` across spans where `src` and `tmp` remain live, initialized, and unmodified preserves `FullSemanticEquiv` (`WellFormed`, `Behavior`, and `Diverges` `↔`).
2. **`moveHeadUnify_certified_bidirectional_iff`:** Certified `CopyProp` single-use `move`-head unification (`_tmp = move _src; ... use(move _tmp) -> .nop; ... use(move _src)`) preserves `FullSemanticEquiv` (`↔`) when `_tmp` is otherwise unread and `_src` is untouched before the unified `move`.
3. **`codegen_dse_moveFree_refines_unconditional`:** Eliminating a dead assignment `_dst = rval -> .nop` whose `_dst` is unread along all reachable paths and whose `rval` contains no `.move l` of a live `l != _dst` is unconditionally forward-sound (`ForwardCodegenRefines`).
4. **`vc_transport_dse_certified_iff`:** Strengthening `DeadStoreElimination` with flow-sensitive `rvalueCertifiedTotal` (`NonZeroAbsSlot` for `/` and `%`, live-initialized operands, non-overflowing checked arithmetic) upgrades refinement to bidirectional `FullSemanticEquiv` (`↔`) so verification conditions transport back to unoptimized MIR without UB erasure.
5. **`destProp_certified_bidirectional_iff`:** Certified `DestinationPropagation` (`_tmp = rval; _dst = move/copy _tmp -> _dst = rval; .nop`, including self-referential `_tmp = _dst + 1; _dst = move _tmp`) preserves `FullSemanticEquiv` (`↔`) when `_tmp` is dead across CFG edges (`isDeadAcrossCfg`) and `_dst` is live at the fused write.
6. **`postSimplifyCfg_tail_crate_and_unit_iff`:** Composing certified `CopyProp`, `MoveHeadUnify`, certified `DeadStoreElimination`, and `DestinationPropagation` transports `Trusted.MirSemantics.CrateTheorem` and `UnitTheorem` bidirectionally (`↔`) whenever `Specs.property` is semantically invariant.

Complete public theorem inventory (`21` theorems, all depending strictly on `[propext]`):

- `VrustcFormal.F1_7.copyProp_certified_bidirectional_iff`
- `VrustcFormal.F1_7.moveHeadUnify_certified_bidirectional_iff`
- `VrustcFormal.F1_7.codegen_dse_moveFree_refines_unconditional`
- `VrustcFormal.F1_7.vc_transport_dse_certified_iff`
- `VrustcFormal.F1_7.destProp_certified_bidirectional_iff`
- `VrustcFormal.F1_7.postSimplifyCfg_tail_crate_and_unit_iff`
- `VrustcFormal.F1_7.reaches_head_det`
- `VrustcFormal.F1_7.execOutcome_reaches_inv`
- `VrustcFormal.F1_7.execOutcome_terminal`
- `VrustcFormal.F1_7.positiveCanary_of_execReturns`
- `VrustcFormal.F1_7.negativeCanary_of_execFaults`
- `VrustcFormal.F1_7.ce_copyprop_clobbered_src_unsound`
- `VrustcFormal.F1_7.ce_copyprop_move_deinit_without_head_elim_unsound`
- `VrustcFormal.F1_7.ce_copyprop_storage_dead_src_unsound`
- `VrustcFormal.F1_7.ce_dse_is_safe_to_remove_div_zero_erases_ub`
- `VrustcFormal.F1_7.ce_dse_is_safe_to_remove_uninit_read_erases_ub`
- `VrustcFormal.F1_7.ce_dse_dead_dst_slot_erases_write_deadlocal_ub`
- `VrustcFormal.F1_7.ce_dse_move_live_src_reverse_unsound`
- `VrustcFormal.F1_7.ce_destprop_hoist_past_reader_unsound`
- `VrustcFormal.F1_7.witness_destprop_self_update_exact`
- `VrustcFormal.F1_7.witness_postSimplifyCfg_tail_pipeline_nonvacuous`

### 3. `zerocopy` Post-`SimplifyCfg-final` Optimization-Tail Shrinkage

`Basis: execution (support/e3_10_copyprop_dse_simplifylocals_miri_and_zerocopy.json)`

| Pass (`compiler/rustc_mir_transform/src/lib.rs:771-779`) | Bodies | Locals (`before -> after`) | Assignments (`before -> after`) | Trivial `copy`/`move` Assigns (`before -> after`) | `StorageLive`/`Dead` (`before -> after`) |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `SimplifyCfg-final` | `4,302` | `17,037 -> 17,037` (`0`) | `12,983 -> 12,916` (`-67`) | `320 -> 307` (`-13`) | `14,463 -> 14,343` (`-120`) |
| `CopyProp` | `4,302` | `17,037 -> 17,037` (`0`) | `12,916 -> 12,778` (`-138`) | `307 -> 174` (**`-133` / `-43.3%`**) | `14,343 -> 14,044` (`-299`) |
| `DeadStoreElimination-final` | `4,302` | `17,037 -> 17,037` (`0`) | `12,778 -> 12,772` (`-6`) | `174 -> 174` (`0`) | `14,044 -> 14,030` (`-14`) |
| `DestinationPropagation` | `4,302` | `17,037 -> 17,037` (`0`) | `12,772 -> 12,714` (`-58`) | `174 -> 116` (**`-58` / `-33.3%`**) | `14,030 -> 13,855` (`-175`) |
| `SimplifyLocals-final` | `4,302` | `17,037 -> 16,768` (**`-269`**) | `12,714 -> 12,714` (`0`) | `116 -> 116` (`0`) | `13,855 -> 13,839` (`-16`) |

Composing `reports/anneal-trusted-mir-simplifycfg-branch-folding-and-dead-block-compaction/` (`SimplifyCfg`), `reports/anneal-trusted-mir-gvn-instsimplify-algebraic-and-discriminant-folding/` (`GVN` & `InstSimplify`), `support/AnnealTrustedMirCopyPropDseDestProp.lean` (`CopyProp`, `DeadStoreElimination`, `DestinationPropagation`), and `reports/anneal-mir-r3-local-compaction-fast-cert-checking-and-scc-olean-sharding/` (`SimplifyLocals` local compaction) covers the post-`SimplifyCfg-final` scalar assignment/local-cleanup tail over `Trusted.MirSemantics` (complementing intermediate branch-specialization passes such as `MatchBranchSimplification`, `JumpThreading`, `DataflowConstProp`, and `TailCopyToMove` at `lib.rs:761-770, 777`).

## Boundaries

1. **Block-local / certified pass scope vs. global SSA dominator/conflict-graph analyses (`not examined` / `known not to apply`).** Upstream `CopyProp` (`ssa.rs`), `DeadStoreElimination` (`MaybeTransitiveLiveLocals` backward dataflow + call-argument `Copy -> Move`), and `DestinationPropagation` (`dest_prop.rs` conflict graph across multi-block lifetimes) also rewrite cross-block SSA classes and `TerminatorKind::Call` operands; `support/AnnealTrustedMirCopyPropDseDestProp.lean` formalizes the certified intraprocedural transformation rules within `mirProfileVersion = 1` (where `TerminatorKind.call` and projected places step fail-closed to `.fault .unsupported`).
2. **Certificate soundness sufficiency vs. semantic completeness.** The computable abstract checkers (`AbsSlot`, `NonZeroAbsSlot` distinguishing unsigned non-zero divisors from signed `INT_MIN / -1` overflow hazards, and `isDeadAcrossCfg`) provide sound decidable sufficiency certificates (`check* = true -> FullSemanticEquiv`), not complete semantic characterizations of every dynamically valid rewrite.
3. **Storage-annotation preservation (`DeadStoreElimination::run_pass` line 157).** Upstream `DeadStoreElimination::run_pass` invokes `UsedInStmtLocals::new(body).remove_unused_storage_annotations(body)` after eliminating dead stores, which—like `SimplifyCfg::Final`—can temporarily flip `hasStorageAnnotation` until `SimplifyLocals::Final` (`lib.rs:779`) prunes the unused local declaration; `support/AnnealTrustedMirCopyPropDseDestProp.lean` rewrites eliminated assignments to `.nop` (preserving `hasStorageAnnotation` directly) so local-declaration pruning composes modularly through `reports/anneal-mir-r3-local-compaction-fast-cert-checking-and-scc-olean-sharding/`.
4. **Functional property invariance (`Specs.property`).** As in `reports/anneal-trusted-mir-simplifycfg-branch-folding-and-dead-block-compaction/` and `reports/anneal-trusted-mir-gvn-instsimplify-algebraic-and-discriminant-folding/`, `Specs.property : Program → Prop` (`Trusted/MirSemantics.lean:1768`) transports across `postSimplifyCfg_tail_crate_and_unit_iff` whenever `Specs.property` is extensional in `WellFormed` / `Behavior` / `Diverges`.

## Evidence

- `support/AnnealTrustedMirCopyPropDseDestProp.lean` — `13740`-line zero-`sorry` Lean 4 proof module (`SHA-256 297c11c1ce141ed0f6287351140460f9c47b2c5ae8ff42abdd471fd254e72837`), byte-for-byte faithful to frozen theorem-statement SHA-256 `b154860c2a136bb877fb974e6481113e507622b0ce06de64d7b35fe9225f8cee`.
- `support/AnnealTrustedMirCopyPropDseDestProp.frozen.sha256` — frozen theorem-statement and completed proof SHA-256 digests.
- `support/multi_kernel_verification_summary.json` — multi-kernel (`Lean v4.34.1` `-M2048`, `Lean v4.35.0`, `lean4export 3.1.0`, `nanoda_bin 0.4.19`) and unmodified `TrustedBoundary.lean` `"preflight"` + Pass 1 `"audit"` receipts (`replayedDeclarations = 2889`, `reachableDeclarations = 3689`, `axioms = ["propext"]`).
- `support/e3_10_copyprop_dse_simplifylocals_miri_and_zerocopy.json` — live `rustc 1.102.0-nightly` + `Miri` `-Zmir-preserve-ub` execution matrix (`10` specimens × `6` flag sets = `60` runs) and `4,302`-body `zerocopy` post-`SimplifyCfg-final` pass-by-pass census.

## Revalidation

1. **Synchronous `Lean v4.34.1` & `TrustedBoundary.lean` Pass 1 Audit (`-M2048`):**
   Compile `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, then compile `support/AnnealTrustedMirCopyPropDseDestProp.lean` with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`, `0` warnings, `0` `Classical.choice`, `0` `Quot.sound`) and run `TrustedBoundary.lean` in `"preflight"` and `"audit"` modes.
2. **External Rust Kernel Check (`nanoda_bin 0.4.19`):**
   Compile on `Lean v4.35.0`, export public theorems via `leanexport`, and verify with `nanoda_bin` under `permitted_axioms: ["propext", "Quot.sound"]` (`rc = 0`) and `permitted_axioms: []` (`rc != 0`).
3. **Live `Miri` `-Zmir-preserve-ub` + `StripDebugInfo` Reproduction:**
   Run `miri -Zmir-opt-level=2 -Zmir-preserve-ub=yes -Zmir-strip-debuginfo=locals-in-tiny-functions -Zub-checks=no` vs. `-Zmir-opt-level=0 -Zmir-preserve-ub=yes` on `tiny_deref(core::ptr::null())` and `tiny_div(10, 0)` to observe `rc = 1` (`Undefined Behavior`) flip to `rc = 0`.
