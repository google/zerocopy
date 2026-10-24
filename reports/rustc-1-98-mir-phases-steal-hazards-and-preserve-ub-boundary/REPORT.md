# Rustc 1.98.0-nightly MIR Phase Pipeline, `Steal<Body>` Query Hazards, `-Z mir-preserve-ub` Semantic Boundary, and Built-to-PostCleanup Lowering Validation

## Summary

In `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-30`), mid-level intermediate representation (MIR) bodies progress through five ordered `MirPhase` stages—`Built`, `Analysis(Initial)`, `Analysis(PostCleanup)`, `Runtime(PostCleanup)`, and `Runtime(Optimized)`—distributed across five compiler queries (`mir_built`, `mir_const`, `mir_promoted`, `mir_drops_elaborated_and_const_checked`, and `optimized_mir`) plus on-demand `tcx.mir_shims(InstanceKind::DropGlue(..))`. Empirical instrumentation and Lean `4.34.1` mechanization establish four key properties of this pipeline:

1. **`Steal<Body<'tcx>>` consumption and warm incremental cache silence:** The queries `mir_built`, `mir_const`, `mir_promoted`, and `mir_drops_elaborated_and_const_checked` return `&'tcx Steal<Body<'tcx>>`. Each downstream query calls `.steal()`, permanently consuming the upstream `Body`. Calling `tcx.optimized_mir(def_id)` inside `after_analysis` before reading `tcx.mir_drops_elaborated_and_const_checked(def_id)` steals all `6` local owners in `cleanup_subject.rs` (`all_elab_stolen_before_opt: true`). Conversely, passive `Config::override_queries` hooks alone record `0` events on a warm incremental cache (`-C incremental=...`), whereas combining `override_queries` with active `after_analysis` demand captures all `12` `Built` and `Runtime(PostCleanup)` bodies across cold, warm-incremental, and forced-steal schedules.
2. **Exact `-Z mir-preserve-ub` boundary at `Runtime(PostCleanup)` vs. `Runtime(Optimized)`:** During the transition to `Runtime(PostCleanup)`, `RemovePlaceMention` (`compiler/rustc_mir_transform/src/remove_place_mention.rs`) is gated by `!tcx.sess.opts.unstable_opts.mir_preserve_ub`. Under default flags (without `-Z mir-preserve-ub`), `RemovePlaceMention` strips `StatementKind::PlaceMention` already at `Runtime(PostCleanup)`. While `let _ = *ptr;` lowers at `Built` to `_3 = copy (*_1); PlaceMention(_3);` (so `_3 = copy (*_1)` survives at `Runtime(PostCleanup)` until `optimized_mir` deletes the dead local), `match *ptr { _ => 0 }` and `_ = *ptr;` lower at `Built` to `PlaceMention((*_1))` with *no* copy into a temporary—so default `Runtime(PostCleanup)` erases the `*ptr` place check completely unless `-Z mir-preserve-ub` is enabled.
3. **Lowering of deref chains, local metadata, storage markers, and `DropGlue` shims:** Between `Built` and `Runtime(PostCleanup)`, `Derefer` and `EraseDerefTemps` replace `Rvalue::CopyForDeref(place)` with `Rvalue::Use(Operand::Copy(place), WithRetag::No)` (`use_retag_no: 1` in `<Guard as Drop>::drop` and `partial_init_move_cleanup`; `use_retag_no: 2` in `partial_field_reinit_cleanup`), `ElaborateDrops` synthesizes compiler drop-flag locals (`_20.._23: bool`) with `LocalInfo::Boring`, and `mir_drops_elaborated_and_const_checked` sets `body.local_decls[*].local_info = ClearCrossCrate::Clear`. At `Runtime(Optimized)` under default `-Z mir-opt-level=1`, `RemoveStorageMarkers` strips all `StorageLive`/`StorageDead` statements (`storage_live = 0`, `storage_dead = 0`). Compiler-generated `tcx.mir_shims(InstanceKind::DropGlue(..))` bodies carry `MirPhase::Runtime(Optimized)` and drop struct fields in declaration order (`_1.0` then `_1.1` in `DropGlue<PairGuards>`, `5` basic blocks).
4. **Mechanized `Built` (`0x01`) to `Runtime(PostCleanup)` (`0x03`) lowering validation:** While `Runtime(PostCleanup)` is the primary operational semantics target because it makes drop-flag state and unwind cleanup explicit, `Built` retains user-binding metadata (`LocalInfo::User`) and unelaborated drop intent. A two-sided executable equivalence validator (`validateBuiltToPostCleanupAdmittedQ1` in `support/PR86AuditRepairs.lean`) checks `Built` move-deinitialization and conditional-drop execution against `Runtime(PostCleanup)` drop-flag execution and is proved sound (`validateBuiltToPostCleanupAdmittedQ1_sound`) and refutation-complete across five parsed `Built`-phase mutation controls (`support/BuiltPhaseControlsR1.lean`).

## Applicability

These findings apply to:

- **`rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-30`, LLVM `22.1.6`)** on `x86_64-unknown-linux-gnu`, specifically:
  - `compiler/rustc_middle/src/mir/syntax.rs` (`MirPhase`, `AnalysisPhase`, `RuntimePhase`, `StatementKind`, `Rvalue`, `WithRetag`)
  - `compiler/rustc_mir_transform/src/lib.rs` (`mir_const`, `mir_promoted`, `mir_drops_elaborated_and_const_checked`, `optimized_mir`, `run_analysis_to_runtime_passes`, `run_post_borrowck_cleanup_passes`)
  - `compiler/rustc_mir_transform/src/elaborate_drops.rs`, `derefer.rs`, `erase_deref_temps.rs`, `remove_place_mention.rs`, `simplify.rs`, `remove_storage_markers.rs`, and `shim.rs`
  - `compiler/rustc_public/` (`rustc_public::mir::Body` conversion in `compiler/rustc_public/src/unstable/convert/stable/mir.rs`)
- **Charon `0.1.210`** (`commit 1e08453924610c19d74c245a7308f17c1008e2db`, pinned to `nightly-2026-05-31`), specifically `charon/src/bin/charon-driver/translate/get_mir.rs`.
- **Lean `4.34.1`** (`commit 5045d0056413266e57c625dcd7c365b10e377c52`), used to mechanize the dialect semantics, boundary discriminators, and `Built`-to-`Runtime(PostCleanup)` lowering theorems in `support/*.lean`.

## Findings

### 1. The Five `rustc` MIR Query Stages and `Steal<Body<'tcx>>` / Incremental Cache Hazards

**Basis:** `source`, `execution`

In `compiler/rustc_mir_transform/src/lib.rs`, `rustc` constructs and transforms MIR across five queries:

| Query | Return type | Output `MirPhase` | Key passes executed |
|---|---|---|---|
| `tcx.mir_built(def_id)` | `&'tcx Steal<Body<'tcx>>` | `Built` | Initial THIR-to-MIR construction (`rustc_mir_build`); retains `FakeRead`, `PlaceMention`, `LocalInfo::User`, and unelaborated `TerminatorKind::Drop`. |
| `tcx.mir_const(def_id)` | `&'tcx Steal<Body<'tcx>>` | `Built` | Steals `mir_built`; runs `SimplifyCfg::Initial` and `CheckAlignment`. |
| `tcx.mir_promoted(def_id)` | `(&'tcx Steal<Body<'tcx>>, &'tcx Steal<IndexVec<Promoted, Body<'tcx>>>)` | `Analysis(Initial)` → `Analysis(PostCleanup)` | Steals `mir_const`; runs `PromoteTemps`, `SimplifyCfg::PromoteConsts`, and `Derefer` (inserting `Rvalue::CopyForDeref`). Borrow check (`mir_borrowck`) runs on this body. |
| `tcx.mir_drops_elaborated_and_const_checked(def_id)` | `&'tcx Steal<Body<'tcx>>` | `Runtime(PostCleanup)` | Steals `mir_promoted`; runs `CleanEndRegions`, `CleanupPostBorrowck` (converting `FakeRead` to `Nop`), `RemoveNoopLandingPads`, `SimplifyCfg::EarlyOpt`, `EraseDerefTemps` (converting `CopyForDeref` to `Rvalue::Use(Operand::Copy(_), WithRetag::No)`), `ElaborateDrops`, `RemovePlaceMention` (unless `-Z mir-preserve-ub`), `AddRetag` (if `-Z mir-emit-retag`), `ConstDebugInfo`, `ClearCrossCrate::Clear` on `local_info`, and `SimplifyCfg::ElaborateDrops`. |
| `tcx.optimized_mir(def_id)` | `&'tcx Body<'tcx>` | `Runtime(Optimized)` | Steals `mir_drops_elaborated_and_const_checked`; runs `InstSimplify::BeforeInline`, `Inline`, `RemoveStorageMarkers`, `SimplifyLocals`, `GVN`, `SCCP`, `DeadStoreElimination`, `CheckNull`, `CheckAlignment`, `CheckEnum`, and `SimplifyCfg::Final`. |

Re-validating `support/cleanup_subject.rs` (SHA-256 `04b073d7d46ffd95dee0730259844032959160e8fcc8e67565df5c25704f41c5`, `6` local owners) across five driver and incremental modes (`support/r14-compiler-revalidation.json`) demonstrates two capture hazards:

| Run mode | `override_queries` hook events | `after_analysis` owners read | `all_elab_stolen_before_opt` | `all_elab_stolen_after_opt` |
|---|---|---|---|---|
| `cleanup_direct_default` | `12` (`6 Built` + `6 PostCleanup`) | `6` | `false` | `true` |
| `cleanup_direct_force_opt_before_elab` | `12` (`6 Built` + `6 PostCleanup`) | `6` | **`true`** | `true` |
| `cleanup_incremental_cold` | `12` (`6 Built` + `6 PostCleanup`) | `6` | `false` | `true` |
| `cleanup_incremental_warm_passive` | **`0`** | **`0`** | `false` | `false` |
| `cleanup_incremental_warm_active` | `12` (`6 Built` + `6 PostCleanup`) | `6` | `false` | `false` |

1. **`Steal<Body>` hazard (`cleanup_direct_force_opt_before_elab`):** If a `rustc_driver` callback or prior pass forces `tcx.optimized_mir(def_id)` before reading `tcx.mir_drops_elaborated_and_const_checked(def_id)`, `elab_steal.is_stolen()` is `true` for all `6` owners (`all_elab_stolen_before_opt: true`). Attempting `elab_steal.borrow()` panics; tools that silently fall back to `tcx.optimized_mir(def_id)` (such as Charon's `get_mir.rs` fallback when a requested MIR query is stolen) silently ingest post-optimization `Runtime(Optimized)` MIR (`stolen_query_silent_optimized_fallback_control`).
2. **Warm incremental cache hazard (`cleanup_incremental_warm_passive`):** Because `mir_built` and `mir_drops_elaborated_and_const_checked` are not directly disk-cached queries, when downstream queries (`mir_borrowck`, `optimized_mir`) hit a warm incremental cache, passive `override_queries` providers never fire (`hook_events_count: 0`). Combining `override_queries` with active `after_analysis` query demand (`cleanup_incremental_warm_active`) forces `mir_built` and `mir_drops_elaborated_and_const_checked` on all `6` owners (`12` hook events) (`combined_hook_and_demand_captures_all_modes`).

### 2. The Exact `-Z mir-preserve-ub` Semantic Boundary at `Runtime(PostCleanup)` (`place_mention_probe.rs`)

**Basis:** `source`, `execution`, `derived`

In `compiler/rustc_mir_transform/src/remove_place_mention.rs`, `RemovePlaceMention::is_enabled` returns `!sess.opts.unstable_opts.mir_preserve_ub`, and `RemovePlaceMention` runs inside `run_analysis_to_runtime_passes` (which produces `Runtime(PostCleanup)`). Similarly, in `compiler/rustc_mir_transform/src/simplify.rs`, `SimplifyCfg::PreOptimizations` sets `preserve_switch_reads = tcx.sess.opts.unstable_opts.mir_preserve_ub`.

Running `support/place_mention_probe.rs` (SHA-256 `cb2ae88359d14bb1d308b341e439fccccebb8e25e5e7f6266b1ab1b083b04b10`) with and without `-Z mir-preserve-ub` (`support/r14-compiler-revalidation.json`) exposes a critical distinction between `let _ = *ptr;` and `match *ptr { _ => () }` / `_ = *ptr;`:

| Function (`place_mention_probe.rs`) | Source construct | `Built` (`place_mentions` / `assigns` / `switches`) | `Runtime(PostCleanup)` default | `Runtime(PostCleanup)` `-Z mir-preserve-ub` | `Runtime(Optimized)` default (`-Z mir-opt-level=1`) | `Runtime(Optimized)` `-Z mir-preserve-ub` |
|---|---|---|---|---|---|---|
| `ub_boundary_probe` | `let _ = *ptr; if cond {}` | `1` / `5` / `1` (`_3 = copy (*_1); PlaceMention(_3)`) | **`0`** / `5` / `1` (`_3 = copy (*_1)` retained) | `1` / `5` / `1` | `0` / `1` / `0` (`1` block; load & `switchInt` deleted) | `1` / `2` / `1` (`2` blocks; load & `switchInt` kept) |
| `match_wildcard_probe` | `match *ptr { _ => () }; if cond {}` | `1` / `5` / `1` (`PlaceMention((*_1))`, no copy) | **`0` / `5` / `1` (`*ptr` check erased!)** | **`1` / `5` / `1` (`PlaceMention((*_1))` kept)** | `0` / `1` / `0` (`1` block) | `1` / `1` / `1` (`2` blocks; `PlaceMention((*_1))` kept) |
| `assign_underscore_probe` | `_ = *ptr;` | `1` / `3` / `0` (`PlaceMention((*_1))`, no copy) | **`0` / `3` / `0` (`*ptr` check erased!)** | **`1` / `3` / `0` (`PlaceMention((*_1))` kept)** | `0` / `1` / `0` (`1` block) | `1` / `1` / `0` (`1` block; `PlaceMention((*_1))` kept) |

- **Why `let _ = *ptr;` and `match *ptr { _ => () }` diverge at default `Runtime(PostCleanup)`:** In `rustc_mir_build`, a `let _ = *ptr;` binding with a type annotation or temporary allocation lowers at `Built` to `StorageLive(_3); _3 = copy (*_1); PlaceMention(_3); StorageDead(_3);`. When `RemovePlaceMention` strips `PlaceMention(_3)` at default `Runtime(PostCleanup)`, the value load `_3 = copy (*_1)` remains until `optimized_mir` eliminates dead locals. By contrast, `match *ptr { _ => () }` and `_ = *ptr;` evaluate `*ptr` solely as a place expression (`PlaceMention((*_1))`) without copying `*ptr` into a temporary. Under default flags, `RemovePlaceMention` strips `PlaceMention((*_1))` during `mir_drops_elaborated_and_const_checked`, completely erasing the `*ptr` dereference from `Runtime(PostCleanup)` (`place_mention_discriminator_distinguishes_let_underscore_from_match_and_assign`, `control_conflating_let_underscore_with_match_wildcard_refuted`).
- **Why `-Z mir-preserve-ub` is required for `Runtime(PostCleanup)` place-validity fidelity:** Enabling `-Z mir-preserve-ub` disables `RemovePlaceMention` and sets `preserve_switch_reads = true`, preserving `PlaceMention((*_1))` across `Built`, `Runtime(PostCleanup)`, and `Runtime(Optimized)`.

### 3. Drop Elaboration, `CopyForDeref` Lowering, `LocalInfo` Erasure, and `DropGlue` Shims (`cleanup_subject.rs`)

**Basis:** `source`, `execution`

Inspecting the dumped bodies of `support/cleanup_subject.rs` (`support/r14-compiler-revalidation.json`) across `Built`, `Runtime(PostCleanup)`, `Runtime(Optimized)`, and `tcx.mir_shims` establishes five concrete representation shifts:

1. **Drop elaboration (`ElaborateDrops`) on partial moves and field reinitialization:**
   - In `partial_init_move_cleanup` (`Built`: `16` blocks, `19` locals, `8` drops, `1` `switchInt`), `ElaborateDrops` synthesizes three `bool` drop-flag locals (`_20`, `_21`, `_22`) in `Runtime(PostCleanup)` (`17` blocks, `22` locals, `6` drops, `4` `switchInt`s), replacing unelaborated `drop(_2)` and `drop(_3)` terminators on normal and unwind paths with explicit `switchInt(copy _21) -> [0: .., otherwise: ..]` diamonds.
   - In `partial_field_reinit_cleanup` (`Built`: `16` blocks, `21` locals, `11` drops, `0` `switchInt`s), where `pair.a` (`_2.0`) is moved into `moved_a` (`_7`) and conditionally reinitialized before scope exit, `Built` emits a whole-struct `drop(_2)` terminator. An operational interpreter that treats `Built`'s `drop(_2)` as dropping all fields of `PairGuards` without tracking per-field move state double-drops `_2.0` when `reinit == false` (`analysis_mir_unelaborated_drop_misinterprets_partial_move_control`). At `Runtime(PostCleanup)` (`9` blocks, `24` locals, `3` drops, `1` `switchInt`), `ElaborateDrops` decomposes `drop(_2)` into an unconditional field drop `drop((_2.1: Guard<'_>))` plus a conditional drop of `(_2.0: Guard<'_>)` guarded by synthesized flag `_23: bool`.
2. **`Derefer` and `EraseDerefTemps` (`WithRetag::No` vs. `WithRetag::Yes`):** During `mir_promoted`, `Derefer` rewrites nested dereference projections by introducing temporary pointer copies `Rvalue::CopyForDeref(place)` on locals marked `LocalInfo::DerefTemp`. During `mir_drops_elaborated_and_const_checked`, `EraseDerefTemps` rewrites `Rvalue::CopyForDeref(place)` into `Rvalue::Use(Operand::Copy(place), WithRetag::No)`, while ordinary user copies carry `WithRetag::Yes` (`use_retag_no: 1` in `<Guard as Drop>::drop` and `partial_init_move_cleanup`; `use_retag_no: 2` in `partial_field_reinit_cleanup`). Under `-Z mir-emit-retag`, `AddRetag` skips `WithRetag::No` copies (`erased_with_retag_flag_conflates_deref_temp_with_user_copy`).
3. **`ClearCrossCrate::Clear` on `LocalDecl::local_info`:** At the end of `mir_drops_elaborated_and_const_checked`, `rustc` replaces every `LocalDecl.local_info` with `ClearCrossCrate::Clear`. Consequently, `LocalInfo::User(BindingForm::Var(..))` metadata is present only at `MirPhase::Built` (`local_info_preserved_only_at_mir_built`).
4. **`RemoveStorageMarkers` at default `-Z mir-opt-level=1` (`Runtime(Optimized)`):** Across all `6` functions in `cleanup_subject.rs` and all `3` functions in `place_mention_probe.rs`, `Runtime(PostCleanup)` preserves every `StorageLive` and `StorageDead` marker (`14`/`14` in `partial_init_move_cleanup`, `17`/`17` in `partial_field_reinit_cleanup`), whereas `Runtime(Optimized)` strips all storage markers (`storage_live: 0, storage_dead: 0` across every body, even with `-Z mir-preserve-ub`) and deletes dead loads before divergent loops (`optimized_mir_elides_ub_before_divergence_control`, `optimized_mir_strips_storage_liveness_markers`).
5. **Compiler-generated `DropGlue` shims (`tcx.mir_shims`):** Calling `Instance::resolve_drop_glue(tcx, ty)` and `tcx.mir_shims(drop_inst.def)` for `Guard` and `PairGuards` yields synthesized bodies tagged with `MirPhase::Runtime(Optimized)`: `DropGlue<Guard>` (`2` blocks, calling `<Guard as Drop>::drop`) and `DropGlue<PairGuards>` (`5` blocks, dropping field `(_1.0: Guard<'_>)` first and `(_1.1: Guard<'_>)` second on both normal and unwind paths). Note also that `rustc_public` (`compiler/rustc_public/`) exposes only `optimized_mir` for function bodies (`rustc_public_default_erases_storage_and_unused_load_checks`).

### 4. Mechanized `Built` (`0x01`) to `Runtime(PostCleanup)` (`0x03`) Lowering Validation in Lean `4.34.1`

**Basis:** `execution`, `derived`

The Lean `4.34.1` modules in `support/` (`support/r14-lean-revalidation.json`, all `8` target modules exiting `0`) formalize both the four-way semantic boundary separation and an executable translation validator between `MirPhase::Built` (`0x01`) and `MirPhase::Runtime(PostCleanup)` (`0x03`):

- **Four-way boundary separation (`MirSemanticBoundary.lean`, `ClaimCaptureClosure.lean`):**
  - `analysis_and_elaborated_cleanup_trace_equivalent` and `reinit_cleanup_analysis_and_elaborated_equivalent` prove that an operational semantics over `Built`/`Analysis` that tracks dynamic local and per-field initialization state produces the exact same normal and unwind effect traces (`[10, 30]`, `[10, 99, 20]`, `[10, 40, 20]`) as `Runtime(PostCleanup)` with explicit compiler-synthesized drop-flag locals.
  - `safe_divergent_satisfies_noUB_without_terminal_state` and `unsafe_prefix_before_divergence_admitted_and_rejected_by_noUB` prove that coinductive prefix safety (`Execution.NoUB`) distinguishes safe non-terminating loops from UB-before-divergence, whereas `Runtime(Optimized)` elides the dead load before the loop (`optimized_mir_elides_ub_before_divergence_control`).
  - `four_way_boundary_separation` proves that no two of `{Analysis(PostCleanup), Runtime(PostCleanup) default, Runtime(PostCleanup) -Z mir-preserve-ub, Runtime(Optimized)}` agree on all four discriminators (explicit drop flags without implicit field-liveness state, `PlaceMention` & `SwitchInt` UB preservation, `StorageLive`/`StorageDead` preservation, and dead-load-before-divergence retention).
- **Executable `Built`-to-`Runtime(PostCleanup)` lowering validator (`PR86AuditRepairs.lean`, `BuiltPhaseControlsR1.lean`):**
  - `evalBuiltBodyWithFuel` executes parsed `MirPhase::Built` (`0x01`) bodies directly under move-deinitialization (`consumeMovedLocalBuilt`) and conditional drop semantics (`evalBuiltDropTarget`), while `evalBodyWithFuel` executes parsed `MirPhase::Runtime(PostCleanup)` (`0x03`) bodies using explicit synthesized drop-flag locals (`_6: bool` in `step_generic_slot`, `_4: bool` in `transactional_step`).
  - `validateBuiltToPostCleanupAdmittedQ1_sound` proves that for any admitted `Built` and `Runtime(PostCleanup)` package pair passing the two-sided validator `validateBuiltToPostCleanupAdmittedQ1`, their step-indexed evaluations agree on all inputs in the checked operational domain (`q1_admitted_validator_accepts_real_package`).
  - `r1_all_five_parsed_built_phase_controls_verified` in `support/BuiltPhaseControlsR1.lean` proves that the validator fails closed on five concrete binary `.amir` v3 `Built`-phase mutations: (1) replacing a moved operand with a copy (`ctrl1`), (2) mutating the `Built` drop target local (`ctrl2`), (3) stripping the `Built` unwind cleanup drop (`ctrl3`), (4) omitting the `Built` phase companion (`ctrl4`), and (5) desynchronizing the `Built` normal-return drop from `Runtime(PostCleanup)` (`ctrl5`).

## Boundaries

- **`known not to apply`:** Default `Runtime(PostCleanup)` (without `-Z mir-preserve-ub`) does **not** preserve `StatementKind::PlaceMention` for wildcard matches (`match *ptr { _ => () }`) or underscore assignments (`_ = *ptr;`), because `RemovePlaceMention` runs before `Runtime(PostCleanup)` completes.
- **`known not to apply`:** `Runtime(Optimized)` (`tcx.optimized_mir`) and `rustc_public`'s default body query do **not** preserve `StorageLive`/`StorageDead` markers at default `-Z mir-opt-level=1`, nor do they preserve dead loads preceding divergent loops.
- **`known not to apply`:** Passive `Config::override_queries` hooks alone do **not** capture `mir_built` or `mir_drops_elaborated_and_const_checked` when downstream queries hit a warm incremental compilation cache (`cleanup_incremental_warm_passive` records `0` hook events).
- **`unsupported`:** `async fn` and coroutine state-machine bodies undergo `CoroutineTransform` (`StateTransform`) after `mir_drops_elaborated_and_const_checked`, rewriting yield points into a `Pin<&mut CoroutineState>` dispatch loop (`async_coroutine_requires_hook_before_state_transform_and_blocks_charon`).
- **`not examined`:** Behavior of `-Z mir-opt-level=0` combined with individual `-Z mir-enable-passes=+...` overrides on inline assembly (`TerminatorKind::InlineAsm`) blocks was not examined.
- **`unknown`:** Whether `rustc_public` will expose a stable query for `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`) or `tcx.mir_shims` in future nightly releases is unknown.

## Evidence

- **`support/cleanup_subject.rs`** (SHA-256 `04b073d7d46ffd95dee0730259844032959160e8fcc8e67565df5c25704f41c5`): 6-function probe (`EffectLog::record`, `<Guard as Drop>::drop`, `may_unwind_op`, `partial_init_move_cleanup`, `partial_field_reinit_cleanup`, `ub_boundary_probe`) exercising partial initialization, partial struct-field move and reinitialization, unwind cleanup, and `DropGlue<PairGuards>`.
- **`support/place_mention_probe.rs`** (SHA-256 `cb2ae88359d14bb1d308b341e439fccccebb8e25e5e7f6266b1ab1b083b04b10`): 3-function probe (`ub_boundary_probe`, `match_wildcard_probe`, `assign_underscore_probe`) isolating the exact action of `RemovePlaceMention` and `SimplifyCfg::PreOptimizations` with and without `-Z mir-preserve-ub`.
- **`support/r14-compiler-revalidation.json`**: Fresh execution ledger captured on `2026-10-24` using `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`, recording the 5-mode `Steal<Body>` and incremental cache matrix, the default vs. `-Z mir-preserve-ub` body metrics across `Built`, `Runtime(PostCleanup)`, and `Runtime(Optimized)`, and the `DropGlue` shim summaries.
- **`support/MirCaptureDialects.lean`** (`9e6288f6...`), **`support/MirCaptureDialectControls.lean`** (`ebbd159f...`), **`support/MirSemanticBoundary.lean`** (`b03ccc71...`), **`support/MirSemanticBoundaryControls.lean`** (`3d5194b1...`), **`support/ClaimCaptureClosure.lean`** (`a0332c14...`), **`support/ClaimCaptureClosureControls.lean`** (`1549fa74...`), **`support/PR86AuditRepairs.lean`** (`f41bb03b...`), and **`support/BuiltPhaseControlsR1.lean`** (`a097b644...`): Lean `4.34.1` formalization modules and negative controls.
- **`support/r14-lean-revalidation.json`**: Fresh Lean `4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`) execution ledger captured on `2026-10-24`, confirming `exit_code: 0` for all `8` target modules and their transitive dependencies.

## Revalidation

To reproduce the compiler measurements and Lean `4.34.1` proofs from this package's `support/` directory:

```bash
# 1. Inspect MIR pass dumps on place_mention_probe.rs with and without -Z mir-preserve-ub
rustc +nightly-2026-05-31 --crate-type=lib --edition=2021 \
  -Z dump-mir="RemovePlaceMention|ElaborateDrops" -Z dump-mir-dir=/tmp/mir_default \
  support/place_mention_probe.rs -o /tmp/libpm_default.rlib

rustc +nightly-2026-05-31 --crate-type=lib --edition=2021 -Z mir-preserve-ub \
  -Z dump-mir="RemovePlaceMention|ElaborateDrops" -Z dump-mir-dir=/tmp/mir_preserve_ub \
  support/place_mention_probe.rs -o /tmp/libpm_preserve.rlib

# 2. Inspect ElaborateDrops and DropGlue on cleanup_subject.rs
rustc +nightly-2026-05-31 --crate-type=lib --edition=2021 -Z mir-preserve-ub \
  -Z dump-mir="ElaborateDrops" -Z dump-mir-dir=/tmp/mir_cleanup \
  support/cleanup_subject.rs -o /tmp/libcleanup.rlib

# 3. Re-check the Lean 4.34.1 formalization modules (in topological order)
for mod in MirCaptureDialects MirCaptureDialectControls MirSemanticBoundary \
           MirSemanticBoundaryControls ClaimCaptureClosure ClaimCaptureClosureControls \
           PR86AuditRepairs BuiltPhaseControlsR1; do
  lean -j1 -M768 "support/${mod}.lean"
done
```
