# Direct `Trusted.MirSemantics` Verification of `JumpThreading`, `MatchBranchSimplification`, `SingleUseConsts`, and `DataflowConstProp`

## Summary

Between `GVN` (`compiler/rustc_mir_transform/src/lib.rs:757`) and `SimplifyCfg::Final` (`lib.rs:771`), `rustc_mir_transform` runs `MatchBranchSimplification`, `DataflowConstProp`, `SingleUseConsts`, `SimplifyConstCondition::AfterConstProp`, and `JumpThreading` (`lib.rs:762-766`) to propagate scalar constants across single-use and control-flow paths, collapse boolean-producing `SwitchInt` diamonds into direct scalar comparisons, and duplicate join blocks whose `SwitchInt` discriminants are statically determined along incoming edges. Directly importing `Trusted.MirAst` and `Trusted.MirSemantics` from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`support/AnnealTrustedMirJumpThreadingConstProp.lean`, `12741` lines, `567998` bytes, SHA-256 `c3d44bb4ff985244020b0322d1b231828559ccfda454e93576d63889897a5338`) alongside live execution probes on `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), `Miri`, and `google/zerocopy@e9bc37a4d2c0ad9be243f25db28ff21624d8102b` establishes four governing results:

1. **`Operand.move` deinitialization asymmetry between upstream `Miri` / codegen and `Anneal`'s `Trusted.MirSemantics` (`deinitMovedPlace = true`).** Live `Miri` execution (`support/e3_14_jump_threading_and_dataflow_const_prop.json`, `support/jt_dfcp_specimens.rs`) and `compiler/rustc_codegen_ssa/src/mir/operand.rs:847-848` (`&Operand::Copy(ref place) | &Operand::Move(ref place)`) show that in upstream `Runtime` MIR (`-Zmir-opt-level=0 -Zmir-preserve-ub=yes`), `Operand::Move(x)` on a `Copy` scalar (`u32`) leaves `x` initialized (`READ_AFTER_MOVE = 14`, `rc = 0`), allowing `SingleUseConsts` (`single_use_consts.rs:28-30`, enabled at `-Zmir-opt-level >= 1` for single syntactic uses), `GVN` (`lib.rs:757`), and `DataflowConstProp` (`dataflow_const_prop.rs:38-40`, enabled at `-Zmir-opt-level >= 3` for multi-use dataflow propagation) to replace `Operand::Move(x)` with `Operand::Constant(c)` unconditionally. Under `Anneal`'s `Trusted.MirSemantics` (`deinitMovedPlace = true`), however, `Operand.move ⟨x, []⟩` transitions non-ZST `locals[x]` to `liveUninitSlot ty` (`.live none`): consequently, propagating a known constant into `Operand.copy` is unconditionally bidirectional (`↔`), whereas propagating into `Operand.move` is forward-refining (`pSrc -> pTgt`) unconditionally and requires all-paths post-move deadness certification of `x` for reverse VC transport (`pTgt -> pSrc`). `Basis: source + execution (Miri & Lean kernel)`
2. **Exact `Trusted.MirSemantics` soundness of `MatchBranchSimplification` and block-duplicating `JumpThreading`.** Collapsing a certified boolean-setting `SwitchInt` diamond into `_dst = BinaryOp(.eq / .ne, .copy _discr, const val); Goto join` preserves `FullSemanticEquiv` (`↔`), and `JumpThreading` via basic-block duplication (`bTgt.basicBlocks = bSrc.basicBlocks_redirected ++ [bbDup]` with `bbDup.statements = bbJoin.statements` and `bbDup.terminator = .goto resolvedTarget`) preserves `hasStorageAnnotation` monotonically, maintains exact 1-to-1 step count across cycles (`Diverges`), and preserves `FullSemanticEquiv` (`↔`) when `bbJoin`'s `SwitchInt` reads `.copy _discr`. `Basis: execution (Lean kernel)`
3. **Full-crate `zerocopy` branch & constant optimization census (`4,302` MIR bodies).** Across `google/zerocopy@e9bc37a4d2c0ad9be243f25db28ff21624d8102b` (`CARGO_INCREMENTAL=0 -C opt-level=2 -Z mir-opt-level=2`), `SingleUseConsts` (`>= 1`) eliminates **`-1,027` assignments** (`+243` `const` tokens), `MatchBranchSimplification` (`>= 2`) eliminates **`-66` basic blocks** and **`-19` `SwitchInt` terminators**, and `JumpThreading` (`>= 2 && !is_like_gpu`) specializes **`+296` duplicated basic blocks** (`+6` `SwitchInt`s, `+288` `Goto`s, `+270` duplicated prefix assignments) prior to `SimplifyCfg::Final`, whereas `DataflowConstProp` (`dataflow_const_prop.rs:38-40`) remains gated off at `mir_opt_level < 3` (`BLOCK_LIMIT = 100`, `PLACE_LIMIT = 100`). `Basis: source + execution`
4. **Three-kernel + unmodified `TrustedBoundary.lean` Pass 1 `-M2048` verification.** `support/AnnealTrustedMirJumpThreadingConstProp.lean` compiles on `Lean v4.34.1` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` in **`23.7856 s` / `858.26 MB` RSS** (`1266` module constants: `455` public + `811` private, `0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `_unsafe_rec`), passes unmodified `TrustedBoundary.lean` `"preflight"` (`ok = true`; frozen `sorry` file rejected `rc = 1`) and Pass 1 `"audit"` under `-M2048` (`ok = true`, `replay = true`, `2847` replayed declarations, `axioms = ["propext"]`), and passes `Lean v4.35.0` (`22.4152 s`) + `lean4export 3.1.0` + external Rust `nanoda_bin 0.4.19` (`rc = 0`, `2594` declarations checked in **`2.1421 s` / `78.16 MB` RSS**; paired `[]` probe rejected fail-closed). `Basis: execution`

## Applicability

- **Primary formal target (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, citing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`):** `Trusted.MirAst.Program` and `Trusted.MirSemantics` ($M_{	ext{anneal}}$, `mirProfileVersion = 1`, `pointerWidthBits = 64`), whose operational rules (`deinitMovedPlace = true`, checked scalar arithmetic, storage-liveness markers) cite upstream `rustc_const_eval` at `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` (whose runtime `Operand::Move` scalar behavior and four audited MIR passes match `412be32a6a189d9a28922beee178bc0abee9d492`).
- **Upstream compiler passes & live execution toolchain:** Pass implementations are audited against `rust-lang/rust@412be32a6a189d9a28922beee178bc0abee9d492` (`MatchBranchSimplification` at `compiler/rustc_mir_transform/src/match_branches.rs:15-565`, `DataflowConstProp` at `dataflow_const_prop.rs:32-1013`, `SingleUseConsts` at `single_use_consts.rs:25-206`, `JumpThreading` at `jump_threading.rs:73-1126`, and `run_optimization_passes` at `lib.rs:757-771`), while live `rustc` + `Miri` execution probes run on `rustc 1.102.0-nightly` (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and full-crate pass censuses measure `google/zerocopy@e9bc37a4d2c0ad9be243f25db28ff21624d8102b`.
- **Independent Lean 4 kernel & exporter verification pins:** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, primary kernel + `TrustedBoundary.lean` Pass 1 replay), `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`, cross-version kernel), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`0.4.19`).

## Findings

### 1. `zerocopy` Branch/Constant Census & `Operand::Move` Deinitialization Asymmetry

`Basis: source + execution (support/e3_14_jump_threading_and_dataflow_const_prop.json, support/jt_dfcp_specimens.rs)`

| Pass (`compiler/rustc_mir_transform/src/lib.rs:762-766`) | `PassPolicy` (`mir_opt_level`) | `zerocopy` (`4,302` bodies) BB Delta | `SwitchInt` Delta | `Goto` Delta | Assignment Delta | `const` Token Delta |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `MatchBranchSimplification` | `>= 2` (`match_branches.rs:18-21`) | **`-66`** | **`-19`** | `-36` | `+7` | `-5` |
| `DataflowConstProp` | `>= 3` (`BLOCK_LIMIT = 100`) | `0` (gated off at `2`) | `0` | `0` | `0` | `0` |
| `SingleUseConsts` | `>= 1` (`single_use_consts.rs:28-30`) | `0` | `0` | `0` | **`-1,027`** | **`+243`** |
| `JumpThreading` | `>= 2 && !is_like_gpu` (`MAX_COST = 100`) | **`+296`** | `+6` | **`+288`** | **`+270`** | `+2` |

Between `SingleUseConsts.after` and `JumpThreading.before`, `SimplifyConstCondition::AfterConstProp` (`lib.rs:765`) immediately folds `11` newly constant-propagated `SwitchInt` terminators into unconditional `Goto`s (`1,105 -> 1,094` `SwitchInt`s, `1,852 -> 1,863` `Goto`s) before `JumpThreading` runs.

On `support/jt_dfcp_specimens.rs`, `custom_jt_preserves_join_prefix` confirms that `JumpThreading` duplicates `bb3` (including its side-effecting prefix statement `acc = a + 5_u32`) into specialized blocks `bb6` (`goto -> bb4`) and `bb7` (`goto -> bb5`), returning `115` and `215` identically across `-Zmir-opt-level=0, 2, 3` in native binaries and `Miri`. Meanwhile `custom_read_after_move_scalar` (`x = 7_u32; y = Move(x); RET = x + y`) leaves `y = Move(x)` untouched under `SingleUseConsts` (`x` has two syntactic uses) while folding `x` under `GVN` (`opt-level=2`) and `DataflowConstProp` (`opt-level=3`), returning `READ_AFTER_MOVE = 14` with `rc = 0` under `miri -Zmir-opt-level=0, 2, 3 -Zmir-preserve-ub=yes`.

### 2. Direct `Trusted.MirSemantics` Soundness & Sharpness Theorems (`support/AnnealTrustedMirJumpThreadingConstProp.lean`)

`Basis: execution (Lean kernel)`

`support/AnnealTrustedMirJumpThreadingConstProp.lean` proves six core pass-soundness and VC-transport theorems alongside fourteen constructive adequacy and sharpness theorems directly over `Trusted.MirAst.Program` and `Trusted.MirSemantics`:

1. **`constPropCopy_certified_bidirectional_iff`:** Rewriting `Operand.copy ⟨x, []⟩` to `Operand.constant c` under a flow-sensitive `ConstAbsSlot` certificate (`checkConstPropCopyProgram`, including `SwitchInt` equality-branch refinement) preserves `FullSemanticEquiv` (`WellFormed`, `Behavior`, and `Diverges` `↔`).
2. **`codegen_constPropMove_certified_refines`:** Rewriting `Operand.move ⟨x, []⟩` to `Operand.constant c` under `checkConstPropMoveProgram` is unconditionally forward-sound (`ForwardCodegenRefines`), even when `x` is read later in `pTgt` (because skipping `deinitMovedPlace = true` leaves `pTgt` strictly more initialized than `pSrc`).
3. **`vc_transport_constPropMove_dead_certified_iff`:** Pairing `isConstPropMoveProgram` with `checkConstPropMoveDeadProgram` (all-paths deadness of `x` after the rewritten `move`) upgrades constant propagation into `Operand.move` to full bidirectional equivalence (`↔`).
4. **`matchBranchSimplify_certified_bidirectional_iff`:** Collapsing a boolean-assigning `SwitchInt (.copy ⟨discr, []⟩)` diamond into `BinaryOp (.eq / .ne)` + `Goto bbJoin` preserves `FullSemanticEquiv` (`↔`) across all integer widths (`u8..u128`, `i8..i128`, `usize`, `isize`) and `bool`.
5. **`jumpThreading_copyDiscr_certified_bidirectional_iff`:** Appending specialized duplicate join blocks `bbDup = { statements := bbJoin.statements, terminator := .goto resolvedTarget }` and redirecting certified `Goto bbJoin` predecessor edges to `Goto bbDup` preserves `FullSemanticEquiv` (`↔`) in exact 1-to-1 step lockstep (including `Diverges`).
6. **`branchAndConstProp_pipeline_crate_and_unit_iff`:** Composing certified `MatchBranchSimplification`, `ConstPropCopy`, dead-after-move `ConstPropMove`, and `JumpThreading` transports `Trusted.MirSemantics.CrateTheorem` and `UnitTheorem` bidirectionally (`↔`) whenever `Specs.property` respects the pipeline endpoints.

Complete public theorem inventory (`20` theorems, all depending strictly on `[propext]`):

- `VrustcFormal.F1_8.constPropCopy_certified_bidirectional_iff`
- `VrustcFormal.F1_8.codegen_constPropMove_certified_refines`
- `VrustcFormal.F1_8.vc_transport_constPropMove_dead_certified_iff`
- `VrustcFormal.F1_8.matchBranchSimplify_certified_bidirectional_iff`
- `VrustcFormal.F1_8.jumpThreading_copyDiscr_certified_bidirectional_iff`
- `VrustcFormal.F1_8.branchAndConstProp_pipeline_crate_and_unit_iff`
- `VrustcFormal.F1_8.reaches_head_det`
- `VrustcFormal.F1_8.execOutcome_reaches_inv`
- `VrustcFormal.F1_8.execOutcome_terminal`
- `VrustcFormal.F1_8.positiveCanary_of_execReturns`
- `VrustcFormal.F1_8.negativeCanary_of_execFaults`
- `VrustcFormal.F1_8.ce_constprop_move_without_deadness_reverse_unsound`
- `VrustcFormal.F1_8.ce_constprop_clobbered_between_def_and_use_unsound`
- `VrustcFormal.F1_8.ce_match_branch_invalid_bool_or_uninit_discr_unsound`
- `VrustcFormal.F1_8.ce_match_branch_mismatched_case_const_unsound`
- `VrustcFormal.F1_8.ce_jumpthread_skipping_join_prefix_stmts_unsound`
- `VrustcFormal.F1_8.ce_jumpthread_move_discr_without_deadness_reverse_unsound`
- `VrustcFormal.F1_8.ce_jumpthread_mutated_discr_in_join_prefix_unsound`
- `VrustcFormal.F1_8.witness_e3_14_jump_threading_preserves_join_prefix_exact`
- `VrustcFormal.F1_8.witness_branchAndConstProp_pipeline_nonvacuous`

## Boundaries

1. **`TOFinder` multi-hop condition chains & non-`Goto` incoming edges vs. certified single-join block duplication (`not examined` / `known not to apply`).** Upstream `JumpThreading` (`TOFinder` at `jump_threading.rs:150-1126`) propagates backward `Condition` sets across multi-block `Chain` paths bounded by `MAX_COST = 100`, redirects non-`Goto` predecessor edges (`SwitchInt` targets via `EdgeEffect`), and avoids loop headers to prevent irreducible CFGs; `support/AnnealTrustedMirJumpThreadingConstProp.lean` verifies the certified single-join `Goto -> bbDup` block-duplication kernel over `Operand.copy` discriminants.
2. **Additional `MatchBranchSimplification` rewrite arms (`not examined`).** Upstream `match_branches.rs` also implements `unify_if_equal_const`, `unify_by_cast`, `unify_transmute_bool`, temporary spilling for `Operand::Move` discriminants, and a trailing `simplify_cfg` pass; `support/AnnealTrustedMirJumpThreadingConstProp.lean` mechanizes the primary `BinOp::Eq` / `BinOp::Ne` boolean-diamond collapse over `Operand.copy` discriminants (`SimplifyCfg` dead-arm compaction composes via `reports/anneal-trusted-mir-simplifycfg-branch-folding-and-dead-block-compaction/`).
3. **Certificate soundness sufficiency vs. semantic completeness.** The computable abstract checkers (`ConstAbsSlot`, `deadAtEntry`, and `checkJumpThreadingProgram`) provide sound decidable sufficiency certificates (`check* = true -> FullSemanticEquiv`), not complete characterizations of every dynamically valid branch or constant rewrite.
4. **Projected place tracking (`TrackElem::Field` / `Variant`, `known not to apply`).** Upstream `DataflowConstProp` and `JumpThreading` also track scalar fields inside aggregates (`rustc_mir_dataflow::value_analysis::Map`), whereas `mirProfileVersion = 1` restricts execution to unprojected locals (`projection = []`), stepping fail-closed to `.fault .unsupported` on projections.
5. **Functional property invariance (`Specs.property`).** As in `reports/anneal-trusted-mir-simplifycfg-branch-folding-and-dead-block-compaction/`, `reports/anneal-trusted-mir-gvn-instsimplify-algebraic-and-discriminant-folding/`, and `reports/anneal-trusted-mir-copyprop-dse-and-destination-propagation/`, `Specs.property : Program → Prop` (`Trusted/MirSemantics.lean:1768`) transports across `branchAndConstProp_pipeline_crate_and_unit_iff` whenever `Specs.property` is extensional in `WellFormed` / `Behavior` / `Diverges`.

## Evidence

- `support/AnnealTrustedMirJumpThreadingConstProp.lean` — `12741`-line zero-`sorry` Lean 4 proof module (`SHA-256 c3d44bb4ff985244020b0322d1b231828559ccfda454e93576d63889897a5338`), byte-for-byte faithful to frozen theorem-statement SHA-256 `d2d45b29aaea7934a5e51372e451931553453f005b4f650b9f41dbe9d184970c`.
- `support/AnnealTrustedMirJumpThreadingConstProp.frozen.sha256` — frozen theorem-statement and completed proof SHA-256 lock digests.
- `support/multi_kernel_verification_summary.json` — multi-kernel (`Lean v4.34.1` `-M2048`, `Lean v4.35.0`, `lean4export 3.1.0`, `nanoda_bin 0.4.19`) and unmodified `TrustedBoundary.lean` `"preflight"` + Pass 1 `"audit"` receipts (`replayedDeclarations = 2847`, `reachableDeclarations = 3668`, `axioms = ["propext"]`).
- `support/e3_14_jump_threading_and_dataflow_const_prop.json` — live `rustc 1.102.0-nightly` + `Miri` execution receipts and `4,302`-body `zerocopy` pass-by-pass deltas.
- `support/jt_dfcp_specimens.rs` — standalone `--edition=2024` Rust specimen suite reproducing `correlated_diamond`, `custom_jt_preserves_join_prefix`, and `custom_read_after_move_scalar`.

## Revalidation

1. **Synchronous `Lean v4.34.1` & `TrustedBoundary.lean` Pass 1 Audit (`-M2048`):**
   Compile `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, then compile `support/AnnealTrustedMirJumpThreadingConstProp.lean` with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`, `0` warnings, `0` `Classical.choice`, `0` `Quot.sound`) and run `TrustedBoundary.lean` in `"preflight"` and `"audit"` modes.
2. **External Rust Kernel Check (`nanoda_bin 0.4.19`):**
   Compile on `Lean v4.35.0`, export public theorems via `leanexport`, and verify with `nanoda_bin` under `permitted_axioms: ["propext", "Quot.sound"]` (`rc = 0`) and `permitted_axioms: []` (`rc != 0`).
3. **Live `Miri` & `JumpThreading` Reproduction:**
   Compile `support/jt_dfcp_specimens.rs` with `--edition=2024 -C opt-level=2 -Z mir-opt-level=2 -Z dump-mir=SingleUseConsts|JumpThreading` (and `-Z mir-opt-level=3` for `DataflowConstProp`) and execute under `miri --edition=2024 -Zmir-preserve-ub=yes`.
