# Checked Arithmetic (`*WithOverflow`), Flat Tuples, MIR `SROA`, and `TerminatorKind.assert` Panic-Freedom Reduction Directly Into `Anneal`'s `Trusted.MirSemantics`

## Summary

In `Anneal`'s unmodified `mirProfileVersion = 1` TCB semantics (`Trusted/MirSemantics.lean`, `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`), flat tuples (`MirTy.tuple`, `Rvalue.aggregateTuple`, `ProjectionElem.field`), checked-overflow arithmetic (`BinOp.addWithOverflow`, `subWithOverflow`, `mulWithOverflow`), and `TerminatorKind.assert` are already present in `Trusted.MirAst` yet step fail-closed to `.fault .unsupported`. Across `google/zerocopy@57cef100c3801df512085bf83ec29bbcaae9efae` (`0.8.48`, `rustc 1.102.0-nightly`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `-C opt-level=2 -Z mir-opt-level=2`, `4,663 -> 4,302` MIR bodies), crate-local (`CARGO_INCREMENTAL=1`, `Inline` disabled) MIR optimization eliminates all `4 -> 0` crate-local overflow `Assert` terminators (`19 -> 15` `Assert`s across `9 -> 6` bodies, leaving `4,296 / 4,302 = 99.86%` bodies `Assert`-free), whereas non-incremental (`CARGO_INCREMENTAL=0`, `Inline` enabled) MIR inlining splices `#[rustc_inherit_overflow_checks]` `libcore` arithmetic into `zerocopy::byteorder` to produce `341` `Assert` terminators across `292` bodies (`4,010 / 4,302 = 93.21%` `Assert`-free), while `ScalarReplacementOfAggregates` (`SROA`) removes `-87` field projections (`3,724 -> 3,637`) and expands projection-free, borrow-free bodies by `+23` (`2,621 -> 2,644`, `61.46%`) (`support/zerocopy_assert_and_sroa_census.json`). Directly importing unmodified `Trusted.MirAst` and `Trusted.MirSemantics` with zero surrogate AST or `Val` types (`support/AnnealTrustedMirCheckedArithTuplesSroaAssert.lean`, `16553` lines, `737053` bytes, SHA-256 `e64659dd566a57fa776ac26c0a2d2862da2cd0aeb6732aad5f43230747f2969a`) establishes five verified results:

1. **Exact conservative extension over unmodified `Trusted.MirAst.Program` (`tupleAssert_conservative_extension_exact`).** Extending `Trusted.MirSemantics.evalStep` to flat tuples (`LocalSlotExt.liveTuple`, sequential left-to-right in-place `evalAggregateInPlaceExt` matching `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` `Aggregate.lean:67-74`, fail-closed on self-aliasing aggregate writes and whole-tuple self-copy/move matching `Place.lean:352-381`), checked `*WithOverflow` arithmetic across all 12 signed/unsigned scalar widths including `i128`/`u128` (`evalWithOverflowOp`), and `TerminatorKind.assert` (`.continue_ | .terminate => .done (.panic msg)`, `.unreachable => .fault .undefined`, `.cleanup _ => .fault .unsupported`, plus `isSupportedAssertKind` matching `Panic.lean:41-60`) agrees 1-for-1 with `Trusted.MirSemantics.evalStep` on flat assert-free steps and coincides bidirectionally (`↔`) with `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`, `CrateTheorem`, and `UnitTheorem` on every flat assert-free `Program`. `Basis: execution (Lean kernel)`
2. **Certified MIR `SROA` flat-tuple flattening & unsigned `*WithOverflow` lowering (`mirSroaTuple_sound_bidirectional_iff`).** Mechanizing non-escaping flat-tuple `SROA` (`checkMirSroaTuple` / `checkMirSroaTrace`: tombstone `locals[tupLocal] := .unit`, `k >= 1` scalar field locals preserving `hasStorageAnnotation`, direct 1-to-1 sequential lowering of non-aliasing `Rvalue.aggregateTuple` matching `evalAggregateInPlaceExt` fault order, and scratch-temp `ovfTmpBase` lowering for unsigned `addWithOverflow`/`subWithOverflow` preserving self-referential carries and `Operand.move` deinitialization) proves full bidirectional semantic equivalence (`FullSemanticEquivTupleAssert`, including constructive `0`-`Classical.choice` `DivergesTupleAssert`). `Basis: source + execution`
3. **Certified `Assert` constant folding & panic-freedom reduction directly into unmodified `Trusted.MirSemantics` (`mirAssertConstFold_sound_bidirectional_iff`, `mirSroaAndAssertLower_noPanic_reduces_to_trusted_mir`, `mirSroaAssert_then_optPipeline_vc_transport`).** Folding canonical constant-true `Assert`s (`bits == 1` / `bits == 0`, rejecting non-canonical `bits >= 2`) preserves `FullSemanticEquivTupleAssert` regardless of `msg`/`unwind`. Lowering admitted `Assert` terminators to `SwitchInt` + fresh `.unreachable` block (`checkMirAssertLower`, guarding `bodyAllBlocksInBounds`, static `.bool` condition, `isSupportedAssertKind`, and `isSupportedAssertUnwind`) reduces `NoPanicAndWellFormedTupleAssert`, `CrateTheoremNoPanicTupleAssert`, and `UnitTheoremNoPanicTupleAssert` bidirectionally (`↔`) onto Anneal's unmodified `Trusted.MirSemantics.{WellFormed, CrateTheorem, UnitTheorem}`—and transports cleanly across any post-lowering intraprocedural optimization pipeline `FullSemanticEquiv pFlat pOpt`. `Basis: execution (Lean kernel)`
4. **Ten constructive sharpness counterexamples (`CE1`–`CE10`) & end-to-end `checked_add_pair` witness (`0` `sorry`).** Kernel-checked Part IV theorems demonstrate `u32::MAX + 1` overflow & `0_u32 - 1_u32` underflow panicking then lowering to `.fault .undefined` (`CE1`–`CE2`), field-granular `move` deinitialization (`CE3`), escaping-ref `SROA` rejection (`CE4`), `StorageDead`/`StorageLive` field uninit reset (`CE5`), `Assert` polarity & non-canonical bool constant rejection (`CE6`), self-aliasing `aggregateTuple` fail-closed & dead-dest field-0 `DeadLocal` ordering (`CE7`), `.unreachable`/`.cleanup`/`AssertKind.unsupported`/`AssertKind.overflow .bitAnd` fail-closed boundaries (`CE8`), whole-tuple self-copy/move rejection vs. distinct copy (`CE9`), and `i128`/`u128` overflow boundaries + `checked_add_u128` lowering (`CE10`). `Basis: execution (Lean kernel)`
5. **Three-kernel + unmodified `TrustedBoundary.lean` Pass 1 `-M2048` verification.** `support/AnnealTrustedMirCheckedArithTuplesSroaAssert.lean` compiles on `Lean v4.34.1` (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) in **`35.8439 s` / `1010.06 MB` RSS** (`1326` module constants: `562` public + `764` private, `27 / 27` strictly `[propext]`, `0` `Classical.choice`, `0` `sorryAx`, `0` `_unsafe_rec`), passes unmodified `TrustedBoundary.lean` `"preflight"` (`ok = true`; frozen `sorry` file rejected `rc = 1`) and Pass 1 `"audit"` under `-M2048` (`ok = true`, `replay = true`, `2907` replayed declarations, `axioms = ["propext"]`), and passes `Lean v4.35.0` (`33.0752 s`) + `lean4export 3.1.0` + external Rust `nanoda_bin 0.4.19` (`rc = 0`, `2540` declarations checked in **`2.3136 s` / `70.24 MB` RSS**; paired `[]` check rejected fail-closed). `Basis: execution`

## Applicability

- **Primary formal target (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, citing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` and `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):** Unmodified `Trusted.MirAst.Program` and `Trusted.MirSemantics` ($M_{\text{anneal}}$, `mirProfileVersion = 1`, `pointerWidthBits = 64`), where flat tuples, `*WithOverflow`, and `TerminatorKind.assert` are parsed in `MirAst` and fault `.unsupported` in `MirSemantics`.
- **Upstream compiler & live execution census (relation among the three `rust-lang/rust` pins):** `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` is Anneal's pinned `Trusted/MirSemantics.lean` reference revision (`interpret/operator.rs` is byte-identical to `c7d5ba59d8e1`); `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973` is the audited source snapshot for `compiler/rustc_mir_transform/src/sroa.rs` (`L15-427`) and `compiler/rustc_const_eval/src/interpret/step.rs`; and `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`) is the live `rustc` execution toolchain used for the `zerocopy` (`google/zerocopy@57cef100c3801df512085bf83ec29bbcaae9efae`, `0.8.48`) MIR dumps.
- **Independent Lean 4 kernel & exporter verification pins:** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, primary kernel + `TrustedBoundary.lean` Pass 1 replay), `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`, cross-version kernel), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@f55114afa24efe39e007f62d31b7e8ac4243f2a6` (`0.4.19`).

## Findings

### 1. `zerocopy` `Assert` & `SROA` MIR Census

`Basis: execution (support/zerocopy_assert_and_sroa_census.json)`

| Pass / Pipeline Point (`google/zerocopy@57cef100c380`, `0.8.48`, `rustc 1.102.0-nightly`, `-C opt-level=2 -Z mir-opt-level=2`) | Bodies (`Assert`-Free) | Metric | Count / Delta |
| :--- | :---: | :--- | :---: |
| `SimplifyCfg-pre-optimizations` (crate-local pre-`Inline`) | `4,663` (`4,654` = `99.81%`) | Total `Assert` (`bounds` / `overflow` / `div_rem` / `other`) | `19` in `9` bodies (`4` / `4` / `11` / `0`) |
| `SimplifyCfg-final` (`CARGO_INCREMENTAL=1`, `Inline` disabled) | `4,302` (`4,296` = `99.86%`) | Total `Assert` (`bounds` / `overflow` / `div_rem` / `other`) | `15` in `6` bodies (`4` / **`0`** / `11` / `0`) |
| `SimplifyCfg-final` (`CARGO_INCREMENTAL=0`, `Inline` enabled) | `4,302` (`4,010` = `93.21%`) | Total `Assert` (`bounds` / `overflow` / `div_rem` / `other`) | `341` in `292` bodies (`4` / `240` / `97` / `0`) |
| `ScalarReplacementOfAggregates` (`CARGO_INCREMENTAL=0`, `before -> after`) | `4,302` | Field projections / pure unprojected no-ref bodies | `3,724 -> 3,637` (**`-87`**) / `2,621 -> 2,644` (**`+23`**, `61.46%`) |

### 2. Core Checked-Arithmetic, Flat-Tuple `SROA`, & `Assert` Reduction Theorems (`support/AnnealTrustedMirCheckedArithTuplesSroaAssert.lean`)

`Basis: execution (Lean kernel)`

1. **`tupleAssert_conservative_extension_exact`:** Exact 1-step equality and bidirectional (`↔`) semantic agreement across `WellFormed`, `NoPanicAndWellFormed`, `Behavior`, `ReachesResult`, `Diverges`, `SatisfiesPost`, `BodyVerified`, `CrateTheorem`, and `UnitTheorem` on every flat assert-free program.
2. **`mirSroaTuple_sound_bidirectional_iff`:** Certified flat-tuple `SROA` (including unsigned `addWithOverflow`/`subWithOverflow` scratch-temp lowering and sequential in-place `aggregateTuple` flattening) preserves `FullSemanticEquivTupleAssert` (`↔`).
3. **`mirAssertConstFold_sound_bidirectional_iff`:** Canonical constant-true `Assert` folding preserves `FullSemanticEquivTupleAssert` (`↔`).
4. **`mirSroaAndAssertLower_noPanic_reduces_to_trusted_mir` & `mirSroaAssert_then_optPipeline_vc_transport`:** Under `isFlatAssertFreeProgram pFlat = true` (plus `isFlatAssertFreeProgram pOpt = true` and `ProgramMetadataCompat pFlat pOpt = true` for `pOpt`) and `SpecsPropertyNoPanicInvariant specs`, finite `SROA` traces + `AssertConstFold` + `AssertLower` map any defined `Assert` panic in `pSrc` to `.fault .undefined` in `pFlat` and reduce `NoPanicAndWellFormedTupleAssert`, `CrateTheoremNoPanicTupleAssert`, and `UnitTheoremNoPanicTupleAssert` bidirectionally (`↔`) directly into unmodified `Trusted.MirSemantics.{WellFormed, CrateTheorem, UnitTheorem}`, composing vertically with any certified post-lowering intraprocedural optimization pipeline `FullSemanticEquiv pFlat pOpt` (such as `reports/anneal-trusted-mir-whole-pipeline-composition-and-ub-preserving-capture/`).

Complete public theorem inventory (`27` theorems):

- `VrustcFormal.F1_11.tupleAssert_conservative_extension_exact`
- `VrustcFormal.F1_11.mirSroaTuple_sound_bidirectional_iff`
- `VrustcFormal.F1_11.mirAssertConstFold_sound_bidirectional_iff`
- `VrustcFormal.F1_11.mirSroaAndAssertLower_noPanic_reduces_to_trusted_mir`
- `VrustcFormal.F1_11.mirSroaAssert_then_optPipeline_vc_transport`
- `VrustcFormal.F1_11.reaches_head_det`
- `VrustcFormal.F1_11.execOutcome_reaches_inv`
- `VrustcFormal.F1_11.execOutcome_terminal`
- `VrustcFormal.F1_11.positiveCanary_of_execReturns`
- `VrustcFormal.F1_11.negativeCanary_of_execFaults`
- `VrustcFormal.F1_11.reachesTupleAssert_head_det`
- `VrustcFormal.F1_11.evalTupleAssertFuel_reaches_inv`
- `VrustcFormal.F1_11.evalTupleAssertFuel_terminal`
- `VrustcFormal.F1_11.positiveCanaryTupleAssert_of_exec`
- `VrustcFormal.F1_11.panicCanaryTupleAssert_of_exec`
- `VrustcFormal.F1_11.negativeCanaryTupleAssert_of_exec`
- `VrustcFormal.F1_11.ce1_u32_max_add_overflow_panics_then_lowers_to_ub`
- `VrustcFormal.F1_11.ce2_u32_zero_sub_one_underflow_panics_then_lowers_to_ub`
- `VrustcFormal.F1_11.ce3_field_granular_move_deinit_distinct_vs_same_field`
- `VrustcFormal.F1_11.ce4_escaping_tuple_ref_rejected_by_sroa`
- `VrustcFormal.F1_11.ce5_storageDead_then_storageLive_resets_tuple_fields_to_uninit`
- `VrustcFormal.F1_11.ce6_assert_expected_polarity_swaps_return_and_panic_and_const_fold`
- `VrustcFormal.F1_11.ce7_aggregate_self_aliasing_rejected_and_dead_dst_field0_order`
- `VrustcFormal.F1_11.ce8_assert_unwind_and_kind_fail_closed_boundaries`
- `VrustcFormal.F1_11.ce9_whole_tuple_self_copy_move_rejected_vs_distinct_copy_ok`
- `VrustcFormal.F1_11.ce10_i128_u128_with_overflow_boundaries`
- `VrustcFormal.F1_11.witness_checked_add_pair_sroa_assert_reduces_to_trusted`

## Boundaries

1. **Flat scalar-field tuples, `checkMirSroaTuple`, & upstream `sroa.rs` (`known not to apply`).** `M_tupleAssert` admits flat tuples `MirTy.tuple elemTys` (`k >= 1` non-tuple supported scalar/ZST fields), tuple parameters/return `_0`, distinct-local whole-tuple copy/move (`_2 = copy _1`, `CE9`), and non-aliasing `Rvalue.aggregateTuple`, failing closed (`.fault .unsupported`) on empty tuples, nested tuples, self-aliasing `aggregateTuple` writes (`Aggregate.lean:67-74`), whole-tuple self-copy/self-move (`Place.lean:352-381`), and `Rvalue.ref`/`addressOf`. By contrast, `checkMirSroaTuple` restricts each flattened local (`argumentCount < tupLocal < locals.length`) to single-field projections, `StorageLive`/`StorageDead`, non-aliasing `Rvalue.aggregateTuple`, and unsigned `addWithOverflow`/`subWithOverflow` (excluding whole-tuple `Rvalue.use` copies/constants and nested fixed-point flattening in `sroa.rs:33-45, 362-417`, while adding scratch-temp scalarization of unsigned `*WithOverflow` that `sroa.rs:112-122` marks escaping).
2. **Unsigned `addWithOverflow`/`subWithOverflow` lowering in `SROA` vs. signed/mul checked ops.** `evalWithOverflowOp` in `M_tupleAssert` supports all 3 checked ops (`addWithOverflow`, `subWithOverflow`, `mulWithOverflow`) across all 12 signed/unsigned integer widths including `i128`/`u128` (`CE10`), while `checkMirSroaTuple` certifies scalar flattening specifically for unsigned `addWithOverflow` and `subWithOverflow` (where `Trusted.MirAst` has native wrapping `add`/`sub` + `lt`/`gt` overflow predicates without signed overflow UB).
3. **`Assert` unwinding cleanups, erased diagnostic operands, & optional overflow-check mode.** `evalTerminatorExt` maps failing `.assert` unwinds `.continue_ | .terminate` to `.done (.panic msg)`, `.unreachable` to `.fault .undefined`, and `.cleanup _` to `.fault .unsupported`, and validates `isSupportedAssertKind msg`. Because `Trusted.MirAst.AssertKind` erases the diagnostic operands on `AssertKind.{boundsCheck, misalignedPtrDeref}`, `M_tupleAssert` cannot evaluate `index`/`len` or `required`/`found` on **failing** asserts (where `Panic.lean:105-113` `assertPanic` reads them before panicking and faults with UB if dead or uninitialized; `NoPanicAndWellFormedTupleAssert` excludes failing asserts and is unaffected). `evalTerminatorExt` also enforces optional overflow checks unconditionally (`-C overflow-checks=yes`, corresponding to `ignoreOptionalOverflowChecks = false` in `ControlFlow.lean:138-141, 195-201`), which is conservative for `NoPanicAndWellFormedTupleAssert` while differing from `-C overflow-checks=no` wrapping when `#[rustc_inherit_overflow_checks]` `Assert`s remain in MIR.
4. **Inherited `Trusted.MirSemantics` (`mirProfileVersion = 1`) envelope.** Entry memory is empty (`⟨[]⟩`), `pointerWidthBits = 64`, and unsupported MIR constructs (`call`, `unwindResume`, references, raw pointers, ADT aggregates) inherit fail-closed `.fault .unsupported` semantics unchanged.

## Evidence

- `support/AnnealTrustedMirCheckedArithTuplesSroaAssert.lean` — `16553`-line zero-`sorry` Lean 4 proof module (`SHA-256 e64659dd566a57fa776ac26c0a2d2862da2cd0aeb6732aad5f43230747f2969a`), byte-for-byte faithful to frozen theorem-statement SHA-256 `b4f299e914c1ab5f4631aff698dc92876f353744f9d3f470078d9b944b92da8a`.
- `support/AnnealTrustedMirCheckedArithTuplesSroaAssert.frozen.sha256` — frozen theorem-statement and completed proof SHA-256 digests.
- `support/multi_kernel_verification_summary.json` — multi-kernel (`Lean v4.34.1` `-M2048`, `Lean v4.35.0`, `lean4export 3.1.0`, `nanoda_bin 0.4.19`) and unmodified `TrustedBoundary.lean` `"preflight"` + Pass 1 `"audit"` receipts (`replayedDeclarations = 2907`, `reachableDeclarations = 3731`, `axioms = ["propext"]`).
- `support/zerocopy_assert_and_sroa_census.json` — live `rustc 1.102.0-nightly` `zerocopy 0.8.48` `Assert` lifecycle (incremental `Inline`-disabled vs. non-incremental `Inline`-enabled) & `SROA` projection-reduction census.

## Revalidation

1. **Synchronous `Lean v4.34.1` & `TrustedBoundary.lean` Pass 1 Audit (`-M2048`):**
   Compile `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, then compile `support/AnnealTrustedMirCheckedArithTuplesSroaAssert.lean` with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`, `0` warnings, `27 / 27` strictly `[propext]`, `0` `Classical.choice`) and run `TrustedBoundary.lean` in `"preflight"` and `"audit"` modes.
2. **External Rust Kernel Check (`nanoda_bin 0.4.19`):**
   Compile on `Lean v4.35.0`, export all `27` public theorems via `leanexport`, and verify with `nanoda_bin` under `permitted_axioms: ["propext", "Quot.sound"]` (`rc = 0`) and `permitted_axioms: []` (`rc != 0`).
