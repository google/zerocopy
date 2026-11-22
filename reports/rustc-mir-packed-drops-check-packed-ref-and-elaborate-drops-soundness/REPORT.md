# `rustc` `#[repr(packed)]` Alignment Safety and Drop Elaboration: `CheckPackedRef`, `AddMovesForPackedDrops`, `RemoveUninitDrops`, `ElaborateDrops`, and the `drop_in_place` `-Z ub-checks` Gap

## Summary

`Basis: normative + source + execution + derived`

Safe destruction and borrowing of fields inside `#[repr(packed)]` / `#[repr(packed(N))]` aggregates in `rustc` rests on a tightly ordered four-pass MIR pipeline spanning MIR building, const-checking preparation, runtime drop lowering, and `drop_glue` shim synthesis. Primary-source inspection across three `rust-lang/rust` revisions (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and `ce66487ebbd7541212d22d01c39a808057d69f1f`), live differential execution across native `rustc`, `-Z ub-checks=yes`, and `Miri` (both Stacked Borrows and Tree Borrows), and a standalone 1,742-line kernel-checked Lean `v4.34.1` development (`support/PackedDropsCheckPackedRefAndElaborateDropsSoundness.lean`, `0` errors, `0` warnings, `0` `_unsafe_rec` helpers, `0` `Classical.choice`/`sorryAx`/`Lean.ofReduceBool`) establish seven load-bearing results:

1. **`CheckPackedRef` (`E0793`) delegates to `rustc_const_eval::util::alignment::place_unalignment` and gates strictly on `PlaceContext::is_borrow()` (`SharedBorrow | MutBorrow`).** The helper `place_unalignment` does **not** live at `compiler/rustc_mir_transform/src/util.rs` (HTTP `404` across all three pinned `rust-lang/rust` revisions); `rustc_mir_transform/src/lib.rs:15` imports `use rustc_const_eval::util;`, resolving to `compiler/rustc_const_eval/src/util/alignment.rs:9-78`. `most_packed_projection` scans projections in reverse, **stops at `ProjectionElem::Deref`** (resetting guaranteed alignment to the dereferenced pointer's ABI alignment), and computes the minimum `pack` across all enclosing packed ADTs. `place_unalignment` returns `None` iff no packed base precedes the last `Deref` or `layout_of(ty)` succeeds with `layout.align <= pack` (`layout.align.abi <= pack` in `14210df0e`) for a sized type or `Slice`/`Str` tail; otherwise it conservatively returns `Some((adt, pack))` (including for unconstrained generic `T` and non-slice unsized tails). Because `PlaceContext::is_borrow()` (`compiler/rustc_middle/src/mir/visit.rs:1392-1398`) matches only `SharedBorrow` and `MutBorrow`—excluding `RawBorrow` (`&raw const`/`&raw mut`) and `FakeBorrow`—`CheckPackedRef` rejects `&p.b` (`E0793`) whenever `align(field) > pack`, accepts `&p.pad` (`align = 1 <= 1`), `&p2.half` (`align = 2 <= 2`), `&raw const p.b`, `&raw mut p.b`, and `&*holder.r` (`Deref` reset), and triggers a compiler `span_bug!` if a builtin `#[derive]` ever produces an unaligned reference. `Basis: normative + source + execution`

2. **`AddMovesForPackedDrops` runs *after* `ElaborateDrops` in `run_runtime_lowering_passes` (and after `DropShimElaborator` in `make_shim`), never before `ElaborateDrops`—and reversing that order is unsound.** In `compiler/rustc_mir_transform/src/lib.rs:659-681` (HEAD; `L626-650` in `14210df0e`), `run_runtime_lowering_passes` executes `ElaborateDrops` (`2-2-004`, `L665`) before `AddMovesForPackedDrops` (`2-2-007`, `L674`, with explicit upstream comment: *"AddMovesForPackedDrops needs to run after drop elaboration"*). Before `ElaborateDrops`, a partially moved packed local `p: PackedNoImplDrop` has only a whole-struct `drop(_p)` terminator with `projections = []` and `align(PackedNoImplDrop) == 1`, so `place_unalignment(_p) == None`; running `AddMovesForPackedDrops` earlier is a complete no-op on `drop(_p)`. Only after `ElaborateDrops` opens `drop(_p)` into per-field `drop((_p.1: AlignedDrop))` and `drop((_p.2: AlignedDrop))` do unaligned field drop places exist for `AddMovesForPackedDrops` (`PassPolicy::Required`) to rewrite into `StorageLive(temp); temp = move place; drop(temp) -> [return: bb_dead, unwind: orig_unwind];` with `bb_dead: StorageDead(temp); goto -> orig_target;`. Notice that `StorageDead(temp)` is inserted only on the normal return edge `bb_dead` (inheriting `is_cleanup`), not on the unwind edge. `Basis: source + execution + derived`

3. **Whole-struct packed drops (`PackedNoImplDrop` vs. `PackedWithImplDrop`) are handled inside `core::ptr::drop_glue` shims built by `build_drop_shim` + `make_shim`.** When `ElaborateDrops` keeps a `Static` whole-struct `drop(_p)` terminator in a user body, `AddMovesForPackedDrops` in the user body leaves `drop(_p)` untouched (`StorageLive` unchanged: `0` added). Instead, `make_shim` (`compiler/rustc_mir_transform/src/shim.rs:125, 186-201`) synthesizes `core::ptr::drop_glue::<T>` via `build_drop_shim` (`DropShimElaborator`, `L258-372`) and then runs `1-1-001.AddMovesForPackedDrops` directly on the shim:
   - For `PackedNoImplDrop { pad: u8, first: AlignedDrop, second: AlignedDrop }`, `build_drop_shim` emits 4 field drops (`(*_1).1` and `(*_1).2` on both normal and cleanup paths; `0` `StorageLive`/`StorageDead`), and `AddMovesForPackedDrops` allocates 4 aligned stack temps `_2.._5` (`StorageLive`: `0 -> 4`, `StorageDead`: `0 -> 4`).
   - For `PackedWithImplDrop { pad: u8, inner: AlignedDrop }` with custom `impl Drop`, `open_drop_for_adt` (`elaborate_drop.rs:1013-1052, 1209-1239`) emits `_2 = &mut (*_1); <PackedWithImplDrop as Drop>::drop(move _2) -> [return: bb5, unwind: bb4]` **first** (valid at any byte address because `align_of::<PackedWithImplDrop>() == 1`), followed by `drop(((*_1).1: AlignedDrop))` on both `bb5` (normal) and `bb4` (cleanup). `AddMovesForPackedDrops` leaves the `Drop::drop` call untouched and extracts both field drops (`bb4`, `bb5`) into aligned stack temps `_4`, `_5` (`StorageLive`: `0 -> 2`, `StorageDead`: `0 -> 2`). Meanwhile, user code attempting to move `p.inner` out of `PackedWithImplDrop` is rejected at borrowck with `E0509` (`move_paths/builder.rs:180-184`), and `wfcheck.rs:1056-1067` rejects packed structs whose unsized tail satisfies `needs_drop` (`E0277`), explaining why `ManuallyDrop<[T]>` is required for droppable packed slice DSTs. `Basis: source + execution`

4. **Manual `core::ptr::drop_in_place(&raw mut p.b)` silently bypasses `-Z ub-checks=yes` (`rc = 0` at both `-O0` and `-O2`) while faulting immediate misaligned-reference UB in `Miri` (`rc = 1`, both Stacked Borrows and Tree Borrows).** `core::ptr::drop_in_place<T: PointeeSized>(to_drop: *mut T)` (`library/core/src/ptr/mod.rs:836-849` HEAD; `L808-821` in `14210df0e`) has body `unsafe { drop_glue(&mut *to_drop) }` with no `assert_unsafe_precondition!`. Three interacting compiler architecture facts create a complete blind spot for `-Z ub-checks=yes` (`CheckAlignment`):
   - **(a) Generic `?Sized` skip in `core`:** When `libcore` is compiled, `T: PointeeSized` is not known to be `Sized`, so `check_pointers.rs:231` (`if !pointee_ty.is_sized(self.tcx, self.typing_env) { return; }`) emits zero alignment checks inside `drop_in_place`.
   - **(b) Pre-inline pass ordering in callers:** In user crates, `CheckAlignment` runs first in `run_optimization_passes` (`lib.rs:711` HEAD / `L695` in `14210df0e`), **before** `ForceInline` (`L723`) and `Inline` (`L725`). At `CheckAlignment`, `main` contains only `TerminatorKind::Call { func: drop_in_place::<AlignedDrop>, args: [move _32] }` with zero `*` dereferences (`0` `MisalignedPointerDereference` assertions emitted), and `CheckAlignment` never re-runs after inlining even at `-C opt-level=2`.
   - **(c) Statements-only visitor & uninstrumented shims:** `check_pointers` (`check_pointers.rs:74-88`) iterates only `basic_blocks[block].statements` (never terminators, despite `should_visit_place` listing `MutatingUseContext::Drop` at `L188`), and `make_shim` (`shim.rs:186-201`) never runs `CheckAlignment` on `DropGlue` shims.
   Live control experiments isolate this gap sharply: on the exact same odd-addressed `*mut AlignedDrop` (`addr % 8 == 1`) under `-Z ub-checks=yes`, direct `&mut *ptr` in `main` aborts immediately (`rc = -6`, `SIGABRT`: `misaligned pointer dereference: address must be a multiple of 0x8`), whereas `core::ptr::drop_in_place(ptr)` prints `RAW_DROP_UB_CHECKS_SURVIVED=true` and exits `0` at both `-O0` and `-O2`, while `Miri` catches `&mut *to_drop` immediately (`rc = 1`, `constructing invalid value of type &mut AlignedDrop: encountered an unaligned reference (required 8 byte alignment but found 1)`). The sound manual replacement—`let val = unsafe { core::ptr::read_unaligned(&raw const p.b) }; drop(val);`—passes native `-Z ub-checks=yes`, `Miri` SB, and `Miri` TB (`rc = 0`, `SAFE_READ_UNALIGNED_DROP=42`). `Basis: normative + source + execution`

5. **`RemoveUninitDrops` runs in `Analysis(PostCleanup)` *only* when `const_precise_live_drops` checking is enabled, and then operates crate-wide across both `const fn` and non-`const` functions.** In `lib.rs:617-628` (HEAD; `L581-592` in `14210df0e`), `RemoveUninitDrops` (`PassPolicy::Required`, `remove_uninit_drops.rs:19-160`) is guarded by `check_consts::post_drop_elaboration::checking_enabled` (`compiler/rustc_const_eval/src/check_consts/post_drop_elaboration.rs:14-26`). On an ordinary crate without `#![feature(const_precise_live_drops)]`, `RemoveUninitDrops` emits `0` MIR dumps and never executes; once `#![feature(const_precise_live_drops)]` is enabled, it executes at `2-2-001.RemoveUninitDrops` (ahead of `2-2-007.ElaborateDrops`) on **both** `const_extract_both` and `runtime_extract_both`, querying `MaybeInitializedPlaces` and rewriting all `5 -> 0` uninitialized `Drop` terminators into `Goto` before `CheckLiveDrops` runs. `Basis: source + execution`

6. **`ElaborateDrops` classifies each `Drop` from `(MaybeInitializedPlaces, MaybeUninitializedPlaces, multipart)` into `Dead` / `Static` / `Conditional` / `Open`, allocating minimal per-leaf stack `bool` flags.** On `partial_move_and_dynamic_drop_flag(take_first, first_tag, second_tag)` over `PackedNoImplDrop`, `ElaborateDrops` (`2-2-004`) allocates **exactly one** stack drop flag `_13: bool` for `p.first` (`(true, true)` -> `DropStyle::Conditional`), leaves `p.second` flag-free (`(true, false)` -> `DropStyle::Static`), initializes `_13 = const false` at `Location::START`, sets `_13 = const true` upon constructing `p`, clears `_13 = const false` on the conditional move `let moved = p.first;`, and emits `switchInt(copy _13) -> [0: bb15, otherwise: bb17]` at scope exit while statically eliminating `p.first` on the unwind pad (`bb19`). Executing `packed_ok` produces exact deterministic `PACKED_DROP_LOG=1637` across native `-O0`, native `-Z ub-checks=yes`, `Miri` Stacked Borrows (`rc = 0`), and `Miri` Tree Borrows (`rc = 0`). `Basis: source + execution`

7. **Kernel-checked Lean `v4.34.1` formalization and Anneal trusted boundary status:** `support/PackedDropsCheckPackedRefAndElaborateDropsSoundness.lean` (`1,742` lines, `59` user `theorem`s, `52` `noncomputable def`s, `19` inductive/structure declarations, `614` kernel constants, `0` `sorry`, `0` forbidden tokens, `0` `_unsafe_rec`, `0` non-`.safe` defs, axioms `[propext]` only—zero `Classical.choice`, zero `Quot.sound`, zero `Lean.ofReduceBool`) mechanizes:
   - `checkPackedRef_implies_all_borrows_aligned` (Section 2) plus six boundary corollaries (`align1_borrow_passes_checkPackedRef`, `raw_borrow_passes_checkPackedRef_even_unaligned`, `deref_resets_packed_projection`, `nested_packed_takes_minimum_pack`, `generic_unknown_layout_rejected_conservatively`, `counterexample_unaligned_borrow_ub`),
   - `addMovesForPackedDrops_eliminates_unaligned_drop_self_ub` (Section 3) plus `drop_in_place_ub_checks_gap_counterexample` and `packedWithImplDrop_before_vs_after_addMoves`,
   - `elaborateDrops_drop_each_live_leaf_once`, `removeUninitDrops_preserves_semantics`, `full_packed_drop_pipeline_soundness`, and `pipeline_order_counterexample` (Sections 4–6).
   At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` maps `TerminatorKind::Drop` (`MirAst.lean:782-784`) and non-fieldless-enum ADTs including packed structs (`MirAst.lean:308-311`) to `.unsupported`, and `Trusted.MirSemantics.evalRvalue` (`MirSemantics.lean:1313`) fails closed on `.ref` and `.addressOf` while setting `deinitMovedPlace = true` on `Operand.move` (`MirSemantics.lean:949-976`). Consequently, the Lean development here is a standalone model over explicit finite structures rather than an import of `Trusted.*`. `Basis: source + execution (Lean kernel) + derived`

## Applicability

`Basis: documentation + source + execution`

### Subjects and How They Relate

This report binds six durable, independently resolvable upstream subjects recorded in `REPORT.json`:

| Subject | Immutable Revision | Role in This Report |
| :--- | :--- | :--- |
| `rust-lang/rust` (HEAD) | `ce66487ebbd7541212d22d01c39a808057d69f1f` | Primary source authority for all current `compiler/` and `library/core/` line citations (`check_packed_ref.rs`, `add_moves_for_packed_drops.rs`, `rustc_const_eval/src/util/alignment.rs`, `remove_uninit_drops.rs`, `elaborate_drops.rs`, `elaborate_drop.rs`, `lib.rs`, `shim.rs`, `check_alignment.rs`, `check_pointers.rs`, `diagnostics.rs`, `post_drop_elaboration.rs`, `visit.rs`, `move_paths/builder.rs`, `wfcheck.rs`, `library/core/src/ptr/mod.rs`). |
| `rust-lang/rust` (`1.102.0-nightly 2026-11-11`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Intermediate nightly revision audited by line-level source diff against both `14210df0e` and `ce66487eb` to verify stability of `PassPolicy::Required`, `diagnostics::UnalignedPackedRef`, `layout.align <= pack`, and pass ordering (`ElaborateDrops` -> `AddMovesForPackedDrops`). |
| `rust-lang/rust` (`1.98.0-nightly 2026-05-31`, LLVM `22.1.6`, Miri `0.1.0`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Exact compiler and Miri binary that produced every live compilation result, MIR dump, `-Z ub-checks=yes` run, and Miri Stacked/Tree Borrows execution in `support/probe_results.json` and `support/mir_excerpts/`. Audited side-by-side against `3ef0c22cd` and `ce66487eb`. |
| `rust-lang/reference` (HEAD) | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative specification for `#[repr(packed(N))]` (`src/type-layout.md`), misaligned-pointer/reference undefined behavior (`src/behavior-considered-undefined.md`), and destructor execution order / `drop_in_place` (`src/destructors.md`). |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Audited solely for how `Trusted.MirAst` and `Trusted.MirSemantics` currently represent (or fail closed on) `Drop`, packed ADTs, `Rvalue::Ref`, `Rvalue::RawPtr`, `StorageLive`/`StorageDead`, and `Operand.move` deinitialization (`deinitMovedPlace = true`). |
| `leanprover/lean4` (`v4.34.1`) | `5045d0056413266e57c625dcd7c365b10e377c52` | Exact Lean 4 compiler and kernel that typechecked `support/PackedDropsCheckPackedRefAndElaborateDropsSoundness.lean` and ran `support/AuditPackedDropsLean.lean` (`support/lean_check_receipt.json`). |

### Cross-Version Comparison Across the Three `rust-lang/rust` Revisions

`Basis: source`

All core algorithmic invariants (pass ordering in `lib.rs` and `shim.rs`, `most_packed_projection` stopping at `Deref`, `PlaceContext::is_borrow()` excluding `RawBorrow`, `AddMovesForPackedDrops` temp extraction, `RemoveUninitDrops` feature gating, and the `CheckAlignment` blind spot for `core::ptr::drop_in_place`) are **identical** across `14210df0e` (`1.98.0-nightly`), `3ef0c22cd` (`1.102.0-nightly`), and `ce66487eb` (HEAD). The concrete source-level deltas between revisions are confined to API refactorings:

| Component / File | `14210df0e` (`1.98.0-nightly`) | `3ef0c22cd` (`1.102.0-nightly`) | `ce66487eb` (HEAD) | Semantic Impact |
| :--- | :--- | :--- | :--- | :--- |
| `check_packed_ref.rs` | `61` L; `errors::UnalignedPackedRef`; manual `source_info` tracking via `visit_statement` / `visit_terminator` (`L27-37`) + `checker.visit_body(body)`. | `50` L; `diagnostics::UnalignedPackedRef`; loops `basic_blocks.iter_enumerated()`, queries `self.body.source_info(location)` (`L14-16, 32`). | Identical to `3ef0c22cd` (`50` L). | None; identical `E0793` diagnostic and `span_bug!` on builtin derives. |
| `add_moves_for_packed_drops.rs` | `115` L; `fn is_required(&self) -> bool { true }`; `TerminatorKind::Drop` has 6 fields (incl. `async_fut`); `ty::TypingEnv::post_analysis(...)`. | `113` L; `fn policy(&self, _) -> PassPolicy { PassPolicy::Required }`; `Drop` has 5 fields (no `async_fut`); `TerminatorKind::goto(target)`; still `TypingEnv::post_analysis`. | `111` L; replaces `TypingEnv::post_analysis` with `body.typing_env(tcx)` (`L44`), resolving `FIXME(#132279)`. | None for sync packed drops; `async_fut` removed from `Drop` terminator after `14210df0e`. |
| `rustc_const_eval/src/util/alignment.rs` | `78` L; `layout.align.abi <= pack` (`L28`). | `78` L; `layout.align <= pack` (`L28`, post-`AbiAndPrefAlign` simplification). | Identical to `3ef0c22cd` (`78` L). | None; `layout.align` is ABI alignment. |
| `remove_uninit_drops.rs` | `157` L; `is_required() -> true`; calls `field.ty(tcx, *args)`. | `160` L; `policy() -> PassPolicy::Required`; calls `field.ty(tcx, *args).skip_norm_wip()`. | Identical to `3ef0c22cd` (`160` L). | None; identical `MaybeInitializedPlaces` check and `Goto` replacement. |
| `elaborate_drops.rs` / `elaborate_drop.rs` | `521` L / `1,424` L; `is_required() -> true`. | `523` L / `1,671` L; `policy() -> PassPolicy::Required`; async-drop expansions in `elaborate_drop.rs`. | `521` L / `1,671` L; `body.typing_env(tcx)`. | None for sync packed-struct drop flags and open-drop ladders. |
| `library/core/src/ptr/mod.rs` (`drop_in_place`) | `L808-821`: `pub const unsafe fn drop_in_place<T: PointeeSized>(to_drop: *mut T)` -> `unsafe { drop_glue(&mut *to_drop) }` (`L820`). | `L822-835` (`unsafe { drop_glue(&mut *to_drop) }` at `L834`). | `L836-849` (`unsafe { drop_glue(&mut *to_drop) }` at `L848`). | None; zero `assert_unsafe_precondition!` in all three revisions. |
| `compiler/rustc_mir_transform/src/lib.rs` (pass order) | `CheckPackedRef` `L408` -> `RemoveUninitDrops` `L586` -> `ElaborateDrops` `L634` -> `AddMovesForPackedDrops` `L643` -> `CheckAlignment` `L695`. | `CheckPackedRef` `L422` -> `RemoveUninitDrops` `L622` -> `ElaborateDrops` `L663` -> `AddMovesForPackedDrops` `L672` -> `CheckAlignment` `L709`. | `CheckPackedRef` `L422` -> `RemoveUninitDrops` `L622` -> `ElaborateDrops` `L665` -> `AddMovesForPackedDrops` `L674` -> `CheckAlignment` `L711`. | Strictly invariant relative pass ordering across all three revisions. |

### Invocation Environment and Scope of Generalization

- **Execution configuration:** All live executions ran on `x86_64-unknown-linux-gnu`, Rust edition `2021`, `-C opt-level=0 -C debuginfo=0` (plus `-C opt-level=2 -Z ub-checks=yes` for the `drop_in_place` post-inlining check), with `Miri` under both default Stacked Borrows and `-Zmiri-tree-borrows`.
- **What generalizes:** MIR pass ordering, `place_unalignment` logic, `CheckPackedRef` acceptance/rejection, `AddMovesForPackedDrops` rewriting, `RemoveUninitDrops` feature gating, `ElaborateDrops` four-way classification, and the `CheckAlignment` blind spot for `core::ptr::drop_in_place` are target-independent in `rustc_mir_transform` and `rustc_const_eval`. Note however that on targets where `align_of::<u64>() < 8` (e.g., 32-bit x86 SysV where `align_of::<u64>() == 4`), concrete alignment moduli scale with the target's `TargetDataLayout`, and on targets where `tcx.sess.target.max_reliable_alignment() < Align::MAX`, `check_alignment.rs:86-108` further masks the runtime alignment check.
- **Relationship to adjacent corpus packages:** This package complements (without duplicating) `repr-packed-unaligned-references-slice-dst-alignment-and-cell-projections` (which focuses on `SliceDst` rounding algebra, `zerocopy::Unalign`, and `UnsafeCell`/`Cell` Tree Borrows projections) and `rustc-drop-elaboration-drop-flags-and-unwind-cleanup-mir-refinement` (which focuses on general `ElaborateDrops` unwind ladders, double-panic abort windows, reverse-range array open drops, and `AbortUnwindingCalls` without analyzing `CheckPackedRef`, `AddMovesForPackedDrops`, `RemoveUninitDrops`, or the `drop_in_place` `-Z ub-checks` gap). It also grounds the abstract theories in `packed-field-projections-aligned-staging-and-alignment-check-completeness-across-shims` and `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction` directly against concrete `rustc` source lines, live MIR dumps, Miri executions, and a unified Lean `v4.34.1` model of the combined `CheckPackedRef` + `RemoveUninitDrops` + `ElaborateDrops` + `AddMovesForPackedDrops` pipeline.

## Findings

### 1. Exact MIR Pass Pipeline: Where `CheckPackedRef`, `RemoveUninitDrops`, `ElaborateDrops`, `AddMovesForPackedDrops`, `DropGlue`, and `CheckAlignment` Execute

`Basis: source + execution`

A frequent misconception in compiler-verification designs is assuming that `AddMovesForPackedDrops` runs *before* `ElaborateDrops` (e.g., in `Analysis(PostCleanup)`) to pre-clean packed places before drop elaboration. Direct inspection of `compiler/rustc_mir_transform/src/lib.rs` and `compiler/rustc_mir_transform/src/shim.rs` across all three pinned revisions (`14210df0e`, `3ef0c22cd`, `ce66487eb`) refutes that ordering and exposes two distinct execution sites for `AddMovesForPackedDrops`:

```text
User Function Body (compiler/rustc_mir_transform/src/lib.rs, HEAD ce66487eb):
  [1] mir_built (L412-431)
        └── Lint(CheckPackedRef)                        [L422]  --> emits E0793 / derive span_bug!
  [2] mir_promoted -> MirPhase::Analysis(Initial) (L481-486)
        └── mir_borrowck (L553)                         --> emits E0509 on move out of Drop type
  [3] run_analysis_cleanup_passes -> Analysis(PostCleanup) (L642-656)
        └── PostAnalysisNormalize (L655)
  [4] Conditional const-drop pre-pass (L617-628, ONLY if checking_enabled(ConstCx) == true):
        ├── RemoveUninitDrops (PassPolicy::Required)    [L622, dump 2-2-001]
        ├── SimplifyCfg::RemoveFalseEdges               [L623, dump 2-2-002]
        └── Lint(post_drop_elaboration::CheckLiveDrops) [L624, dump 2-2-003]
  [5] run_runtime_lowering_passes -> Runtime(Initial) (L659-681, run_passes_no_validate):
        ├── CriticalCallEdges                           [L662]
        ├── Subtyper                                    [L664]
        ├── ElaborateDrops (PassPolicy::Required)       [L665, dump 2-2-004 (or 2-2-007 with [4])]
        ├── Lint(CheckDropRecursion)                    [L667, dump 2-2-005]
        ├── AbortUnwindingCalls                         [L671, dump 2-2-006]
        └── AddMovesForPackedDrops (PassPolicy::Required)[L674, dump 2-2-007]
  [6] run_runtime_cleanup_passes -> Runtime(PostCleanup) (L684-698)
  [7] run_optimization_passes -> Runtime(Optimized) (L700-745):
        ├── CheckAlignment (-Z ub-checks, optional)     [L711, dump 3-2-001]  <-- BEFORE Inline!
        ├── CheckNull, CheckEnums                       [L712-713]
        ├── InstSimplify::BeforeInline                  [L721]
        ├── ForceInline                                 [L723]
        └── Inline                                      [L725]

Synthesized DropGlue Shim (compiler/rustc_mir_transform/src/shim.rs, HEAD ce66487eb):
  [S1] build_drop_shim (L258-372)
         └── elaborate_drop(&mut DropShimElaborator, (*_1), ...) -> Runtime(Initial)
  [S2] make_shim (L186-201, run_passes_no_validate -> Runtime(Optimized)):
         ├── MentionedItems                             [L190]
         ├── AddMovesForPackedDrops                     [L191, dump 1-1-001]
         ├── RemoveNoopLandingPads, SimplifyCfg::MakeShim, InstSimplify::BeforeInline, ForceInline
         ├── AbortUnwindingCalls, CriticalCallEdges
         └── (NO CheckAlignment!)
```

#### Why `AddMovesForPackedDrops` Must Run After `ElaborateDrops`

`Basis: source + execution + derived`

Consider `partial_move_and_dynamic_drop_flag` (`support/mir_excerpts/packed_ok.partial_move_and_dynamic_drop_flag.2-2-004.ElaborateDrops.before.mir`, `L78-81` and `L96-98`):

```rust
// Before ElaborateDrops (2-2-004.ElaborateDrops.before.mir):
bb7: {
    StorageDead(_9);
    drop(_4) -> [return: bb8, unwind continue];
}
bb11 (cleanup): {
    drop(_4) -> [return: bb13, unwind terminate(cleanup)];
}
```

Here `_4` has type `PackedNoImplDrop` (`#[repr(C, packed)]`, `align_of::<PackedNoImplDrop>() == 1`). Its place `_4` has an **empty projection list** (`projections = []`). Therefore `most_packed_projection(_4)` returns `None` and `place_unalignment(_4)` returns `None`. If `AddMovesForPackedDrops` ran before `ElaborateDrops`, it would inspect `drop(_4)`, compute `place_unalignment(_4) == None`, and leave `bb7` and `bb11` completely unchanged!

When `ElaborateDrops` (`2-2-004`) then opens `drop(_4)` into a field-granular drop ladder (because `_4.1` was conditionally moved out in `bb3`), it synthesizes four *new* `TerminatorKind::Drop` terminators targeting projected packed fields (`2-2-007.AddMovesForPackedDrops.before.mir`, `L113-135`):
- `bb14 (cleanup)`: `drop((_4.2: AlignedDrop))`
- `bb15`: `drop((_4.2: AlignedDrop))`
- `bb17`: `drop((_4.1: AlignedDrop))`
- `bb19 (cleanup)`: `drop((_4.2: AlignedDrop))`

Now every one of those four places has projection `[Field(1 or 2, AlignedDrop)]` out of `PackedNoImplDrop` (`pack = 1`), where `align_of::<AlignedDrop>() == 8 > 1`, so `place_unalignment` returns `Some((PackedNoImplDrop, Align(1)))`. Running `AddMovesForPackedDrops` at `2-2-007` (after `ElaborateDrops`) catches all four newly exposed packed field drops and extracts each into an aligned stack local `_14.._17` (`StorageLive`: `9 -> 13`, `StorageDead`: `9 -> 13`). The exact same structural necessity holds inside `build_drop_shim` (`shim.rs:356` -> `L191`): `DropShimElaborator` first opens `drop(*_1)` into field drops `drop((*_1).1)` and `drop((*_1).2)`, and `make_shim` immediately follows with `1-1-001.AddMovesForPackedDrops`. This necessity is also kernel-proved in Lean via `PackedDropsSoundness.pipeline_order_counterexample`.

---

### 2. `CheckPackedRef` (`E0793`), `util::place_unalignment`, and `PlaceContext::is_borrow()`

`Basis: normative + source + execution`

#### Normative Alignment Rule vs. Compiler Implementation

The Rust Reference (`rust-lang/reference@c9cc32825b03`, `src/type-layout.md:632-660`, `src/behavior-considered-undefined.md:82-98`) defines three distinct rules:
1. **`#[repr(packed(N))]` shallow clamping (`type-layout.md:636-651`):** `N` must be a power of two in `[1, 2^29]` (default `1` for `#[repr(packed)]`). Each direct field is positioned with alignment `min(align(field), N)`, and inter-field padding is the minimum required for that clamped alignment (`0` for `packed(1)`). Internal padding *inside* any field type is untouched.
2. **Misaligned references are immediate UB (`behavior-considered-undefined.md:93-97`):** Forming `&T` or `&mut T` requires the pointer to be aligned to `align_of::<T>()` (*"producing an invalid value"*), even if the reference is never dereferenced or immediately cast to a raw pointer.
3. **Raw address-of is permitted (`behavior-considered-undefined.md:90-91`):** `&raw const place` and `&raw mut place` do not produce a reference and do not trigger misaligned-reference UB (though dereferencing a misaligned raw pointer for a load/store remains UB).

In `rustc`, static rejection of unaligned packed field references happens right after MIR construction in `mir_built` (`lib.rs:422` HEAD) via `Lint(check_packed_ref::CheckPackedRef)`. The complete pass at `rust-lang/rust@ce66487ebbd7541212d22d01c39a808057d69f1f`, `compiler/rustc_mir_transform/src/check_packed_ref.rs:26-50`, is:

```rust
impl<'tcx> Visitor<'tcx> for PackedRefChecker<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if context.is_borrow()
            && let Some((adt, pack)) =
                util::place_unalignment(self.tcx, self.body, self.typing_env, *place)
        {
            let source_info = self.body.source_info(location);
            let def_id = self.body.source.instance.def_id();
            if let Some(impl_def_id) = self.tcx.trait_impl_of_assoc(def_id)
                && self.tcx.is_builtin_derived(impl_def_id)
            {
                span_bug!(source_info.span, "builtin derive created an unaligned reference");
            } else {
                self.tcx.dcx().emit_err(diagnostics::UnalignedPackedRef {
                    span: source_info.span,
                    ty_descr: adt.descr(),
                    align: pack.bytes(),
                });
            }
        }
    }
}
```

#### Exact Semantics of `PlaceContext::is_borrow()` vs. `is_address_of()`

In `compiler/rustc_middle/src/mir/visit.rs:1390-1407` (HEAD `ce66487eb`; identical in `3ef0c22cd` and `14210df0e`), note the exact variant naming (`RawBorrow`, not `AddressOf`):

```rust
    /// Returns `true` if this place context represents a borrow, excluding fake borrows
    /// (which are an artifact of borrowck and not actually borrows in runtime MIR).
    pub fn is_borrow(self) -> bool {
        matches!(
            self,
            PlaceContext::NonMutatingUse(NonMutatingUseContext::SharedBorrow)
                | PlaceContext::MutatingUse(MutatingUseContext::Borrow)
        )
    }

    /// Returns `true` if this place context represents an address-of.
    pub fn is_address_of(self) -> bool {
        matches!(
            self,
            PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow)
                | PlaceContext::MutatingUse(MutatingUseContext::RawBorrow)
        )
    }
```

Thus:
- `&p.b` visits `p.b` with `NonMutatingUse(SharedBorrow)` -> `is_borrow() == true` -> checked by `CheckPackedRef`.
- `&mut p.b` visits `p.b` with `MutatingUse(Borrow)` -> `is_borrow() == true` -> checked by `CheckPackedRef`.
- `&raw const p.b` and `&raw mut p.b` visit `p.b` with `NonMutatingUse(RawBorrow)` / `MutatingUse(RawBorrow)` -> `is_borrow() == false` -> **permitted** by `CheckPackedRef`.
- `FakeBorrow` (inserted for match guards / borrowck) has `is_borrow() == false`, avoiding spurious `E0793` on pattern-matched packed fields that are never actually borrowed at runtime.
- `Copy` (`let x = p.b;` for `Copy` fields) and `Move` (`let m = p.inner;`) have `is_borrow() == false` -> **permitted** (lowered as unaligned memory copies/moves).

#### Exact Semantics of `rustc_const_eval::util::alignment::place_unalignment`

In `compiler/rustc_const_eval/src/util/alignment.rs:9-78` (HEAD `ce66487eb`; `L28` uses `layout.align.abi <= pack` in `14210df0e`):

```rust
pub fn place_unalignment<'tcx, L>(
    tcx: TyCtxt<'tcx>,
    local_decls: &L,
    typing_env: ty::TypingEnv<'tcx>,
    place: Place<'tcx>,
) -> Option<(AdtDef<'tcx>, Align)>
where L: HasLocalDecls<'tcx>
{
    let Some((descr, pack)) = most_packed_projection(tcx, local_decls, place) else {
        return None;
    };
    let ty = place.ty(local_decls, tcx).ty;
    let unsized_tail = || tcx.struct_tail_for_codegen(ty, typing_env);
    match tcx.layout_of(typing_env.as_query_input(ty)) {
        Ok(layout)
            if layout.align <= pack
                && (layout.is_sized()
                    || matches!(unsized_tail().kind(), ty::Slice(..) | ty::Str)) => None,
        _ => Some((descr, pack)),
    }
}

pub fn most_packed_projection<'tcx, L>(
    tcx: TyCtxt<'tcx>,
    local_decls: &L,
    place: Place<'tcx>,
) -> Option<(AdtDef<'tcx>, Align)>
where L: HasLocalDecls<'tcx>
{
    place
        .iter_projections()
        .rev()
        // Stop at `Deref`; standard ABI alignment applies there.
        .take_while(|(_base, elem)| !matches!(elem, ProjectionElem::Deref))
        .filter_map(|(base, _elem)| {
            let adt = base.ty(local_decls, tcx).ty.ty_adt_def()?;
            let pack = adt.repr().pack?;
            Some((adt, pack))
        })
        .min_by_key(|(_, align)| *align)
}
```

Four subtle properties of this 70-line algorithm govern every edge case:
1. **`Deref` boundary reset (`L68`):** Iterating `place.iter_projections().rev().take_while(|(_, elem)| !matches!(elem, Deref))` means any packed struct *outside* a pointer/reference dereference is ignored once a `Deref` is crossed. For `#[repr(C, packed)] struct Q<'a> { a: u8, r: &'a u32 }`, the place `(*q.r)` has projections `[Field(1, &u32), Deref]`; scanning from the end stops immediately at `Deref`, returning `None`. Evaluating `q.r` performs an unaligned copy of the reference value (legal), and the resulting `&'a u32` obeys standard 4-byte reference alignment, so `&*q.r` is guaranteed 4-aligned.
2. **Minimum across nested packed structs (`L77`):** For `#[repr(C, packed(2))] struct Outer { a: u8, i: Inner }` where `#[repr(C, packed(4))] struct Inner { x: u16, y: u32 }`, `&o.i.x` and `&o.i.y` traverse both `Outer` (`pack = 2`) and `Inner` (`pack = 4`). `.min_by_key(|(_, align)| *align)` computes `min(2, 4) = 2`, allowing `&o.i.x` (`align(u16) = 2 <= 2`) while rejecting `&o.i.y` (`align(u32) = 4 > 2`) with `E0793` (`this struct is at most 2-byte aligned`).
3. **Conservative rejection on generic / opaque-unsized fields (`L27-49`):** For `#[repr(packed)] struct G<T>(T); fn bad<T>(g: &G<T>) -> &T { &g.0 }`, `tcx.layout_of(T)` returns `Err(LayoutError::Unknown(_))` in the polymorphic body, hitting the `_ => Some((descr, pack))` fallback and emitting `E0793` even if `G` is later instantiated only with `T = u8`. Likewise, an unsized `dyn Trait` tail fails `layout.is_sized() || matches!(unsized_tail().kind(), Slice(..) | Str)` because the dynamic alignment of a trait object is stored in its vtable and unknown statically.
4. **Live 10-case `CheckPackedRef` empirical matrix (`support/probe_results.json`):** Every case in `CHECK_PACKED_REF_CASES` matched `rustc 1.98.0-nightly (14210df0e)` identically:

| Probe Case | Packed Repr & Field Expression | `most_packed_projection` | `layout.align` vs `pack` | `rustc` Exit Code | Diagnostic |
| :--- | :--- | :---: | :---: | :---: | :--- |
| `e0793_packed1_u32` | `packed(1)`, `&p.b` (`u32`) | `Some(1)` | `4 > 1` | `1` | `error[E0793]` (`1-byte aligned`) |
| `e0793_packed1_mut_u64` | `packed(1)`, `&mut p.b` (`u64`) | `Some(1)` | `8 > 1` | `1` | `error[E0793]` (`1-byte aligned`) |
| `e0793_packed2_u32` | `packed(2)`, `&p.b` (`u32`) | `Some(2)` | `4 > 2` | `1` | `error[E0793]` (`at most 2-byte aligned`) |
| `e0793_generic_unbounded` | `packed(1)` `G<T>`, `&g.0` (`T`) | `Some(1)` | `Err(Unknown)` | `1` | `error[E0793]` (`1-byte aligned`) |
| `e0793_nested_packed_min` | `packed(2)` -> `packed(4)`, `&o.i.y` (`u32`) | `Some(min(2,4)=2)` | `4 > 2` | `1` | `error[E0793]` (`at most 2-byte aligned`) |
| `ok_packed1_u8` | `packed(1)`, `&p.a` (`u8`) | `Some(1)` | `1 <= 1` | `0` | Accepted |
| `ok_packed2_u16` | `packed(2)`, `&p.a` (`u16`) | `Some(2)` | `2 <= 2` | `0` | Accepted |
| `ok_nested_packed_min` | `packed(2)` -> `packed(4)`, `&o.i.x` (`u16`) | `Some(min(2,4)=2)` | `2 <= 2` | `0` | Accepted |
| `ok_packed1_raw_borrows` | `packed(1)`, `&raw const p.b` & `&raw mut p.b` | `Some(1)` (`is_borrow=false`) | Skipped (`RawBorrow`) | `0` | Accepted |
| `ok_packed1_deref_reset` | `packed(1)` `Q`, `&*q.r` (`&u32`) | `None` (stopped at `Deref`) | N/A | `0` | Accepted |

---

### 3. `AddMovesForPackedDrops`, `PackedNoImplDrop` vs. `PackedWithImplDrop`, `E0509`, and `wfcheck`

`Basis: normative + source + execution`

#### Exact MIR Rewrite Performed by `AddMovesForPackedDrops`

In `compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:40-111` (HEAD `ce66487eb`), `AddMovesForPackedDrops` declares `PassPolicy::Required` (*"Implements part of MIR semantics by making implicit packed-drop handling explicit"*, `L70-73`; `fn is_required(&self) -> bool { true }` in `14210df0e`, `L72-74`). For every basic block `bb` whose terminator is `TerminatorKind::Drop { place, target, unwind, replace, drop }` where `util::place_unalignment(tcx, body, typing_env, place).is_some()`, `add_move_for_packed_drop` (`L76-111`) applies a four-part `MirPatch`:

```rust
let ty = place.ty(body, tcx).ty;
let temp = patch.new_temp(ty, source_info.span);
let storage_dead_block = patch.new_block(BasicBlockData::new_stmts(
    vec![Statement::new(source_info, StatementKind::StorageDead(temp))],
    Terminator { source_info, kind: TerminatorKind::goto(target) },
    is_cleanup,
));
patch.add_statement(loc, StatementKind::StorageLive(temp));
patch.add_assign(loc, Place::from(temp), Rvalue::Use(Operand::Move(*place), WithRetag::Yes));
patch.patch_terminator(
    loc.block,
    TerminatorKind::Drop { place: Place::from(temp), target: storage_dead_block, unwind, replace, drop },
);
```

Three structural invariants of this patch merit explicit retention:
1. **Aligned temporary allocation:** `temp` is a fresh stack local of type `ty` (`body.local_decls`), so codegen and Miri allocate `temp` at `align_of::<ty>()`, guaranteeing that `drop(temp)` supplies a properly aligned `&mut ty` to `core::ptr::drop_glue::<ty>`.
2. **Unaligned byte-wise move without intermediate reference:** `temp = move *place` evaluates `Operand::Move(*place)` directly from the packed base local/pointer without constructing `&ty` or `&mut ty`. In LLVM IR this lowers to an unaligned `memcpy` (`align 1` source, `align align_of::<ty>()` destination); in Miri it copies the field's bytes directly without triggering misaligned-reference validity checks.
3. **Asymmetric `StorageDead` placement on normal vs. unwind edges:** `storage_dead_block` inherits `is_cleanup` from `loc.block` and executes `StorageDead(temp); goto -> target;` on the normal return edge, while the terminator's `unwind` edge stays identical to the original `unwind` (no `StorageDead(temp)` cleanup block is spliced onto the unwind edge). On normal execution, `StorageDead(temp)` prevents stack-frame blowup when many packed fields drop sequentially in one function; on unwind, stack storage is reclaimed on frame pop.

#### Verbatim Live MIR: `PackedNoImplDrop` vs. `PackedWithImplDrop` `drop_glue` Shims

Live MIR dumps from `rustc 1.98.0-nightly (14210df0e)` (`support/mir_excerpts/`) confirm the exact interaction between `build_drop_shim` (`shim.rs:258-372`), `open_drop_for_adt` (`elaborate_drop.rs:1013-1052`), and `1-1-001.AddMovesForPackedDrops` (`shim.rs:191`):

- **`core::ptr::drop_glue::<PackedNoImplDrop>` (`support/mir_excerpts/core.ptr-drop_glue.PackedNoImplDrop.1-1-001.AddMovesForPackedDrops.{before,after}.mir`):**
  Before `AddMovesForPackedDrops`, the shim has `4` unaligned field drops (`bb7`: `(*_1).1`, `bb6`: `(*_1).2`, `bb5 (cleanup)`: `(*_1).1`, `bb4 (cleanup)`: `(*_1).2`) and `0` `StorageLive`/`StorageDead`. After `AddMovesForPackedDrops`, all four are rewritten into aligned temporaries `_2.._5 : AlignedDrop` with return-edge `StorageDead` blocks `bb8..bb11`:
  ```rust
  // Excerpt from core.ptr-drop_glue.PackedNoImplDrop.1-1-001.AddMovesForPackedDrops.after.mir:
  bb7: {
      StorageLive(_5);
      _5 = move ((*_1).1: AlignedDrop);
      drop(_5) -> [return: bb11, unwind: bb4];
  }
  bb11: {
      StorageDead(_5);
      goto -> bb6;
  }
  bb6: {
      StorageLive(_4);
      _4 = move ((*_1).2: AlignedDrop);
      drop(_4) -> [return: bb10, unwind: bb2];
  }
  bb4 (cleanup): {
      StorageLive(_2);
      _2 = move ((*_1).2: AlignedDrop);
      drop(_2) -> [return: bb8, unwind terminate(cleanup)];
  }
  ```

- **`core::ptr::drop_glue::<PackedWithImplDrop>` (`support/mir_excerpts/core.ptr-drop_glue.PackedWithImplDrop.1-1-001.AddMovesForPackedDrops.{before,after}.mir`):**
  Per the Rust Reference (`src/destructors.md:8-12`), `<PackedWithImplDrop as Drop>::drop(&mut self)` MUST execute **before** its fields are dropped. Because `align_of::<PackedWithImplDrop>() == 1`, constructing `_2 = &mut (*_1)` at `bb6` is alignment-valid at any byte address and is **not** moved to a temporary. Only after `<PackedWithImplDrop as Drop>::drop` returns (`bb5`) or unwinds (`bb4 (cleanup)`) does `AddMovesForPackedDrops` extract `(*_1).1` into aligned stack locals `_5` and `_4`:
  ```rust
  // Excerpt from core.ptr-drop_glue.PackedWithImplDrop.1-1-001.AddMovesForPackedDrops.after.mir:
  bb6: {
      _2 = &mut (*_1);
      _3 = <PackedWithImplDrop as Drop>::drop(move _2) -> [return: bb5, unwind: bb4];
  }
  bb5: {
      StorageLive(_5);
      _5 = move ((*_1).1: AlignedDrop);
      drop(_5) -> [return: bb8, unwind: bb2];
  }
  bb4 (cleanup): {
      StorageLive(_4);
      _4 = move ((*_1).1: AlignedDrop);
      drop(_4) -> [return: bb7, unwind terminate(cleanup)];
  }
  bb7 (cleanup): {
      StorageDead(_4);
      goto -> bb2;
  }
  bb8: {
      StorageDead(_5);
      goto -> bb3;
  }
  ```

#### Type-System and Borrow-Checker Rules Coupled to Packed Drops (`E0509`, `E0277`, `E0588`)

`Basis: source + execution`

Three compile-time rules enforce preconditions assumed by `AddMovesForPackedDrops` and `ElaborateDrops`, all empirically verified in `support/probe_results.json` (`packed_drop_type_rules`):

1. **`E0509` bans partial moves out of `PackedWithImplDrop` (`compiler/rustc_mir_dataflow/src/move_paths/builder.rs:180-184`):** When `MoveDataBuilder` walks a field projection on `ty::Adt(adt, _)` where `adt.has_dtor(tcx)` is `true`, it refuses to create a child `MovePath` (`return;`), causing borrowck to reject `p.inner` with `error[E0509]: cannot move out of type PackedWithImplDrop, which implements the Drop trait` (`rc = 1`). Combined with `E0793` (`CheckPackedRef`), inside `impl Drop for PackedWithImplDrop` the user can neither move out over-aligned non-`Copy` fields nor borrow `&mut self.inner`; accessing `self.inner` inside `Drop::drop` requires `&raw mut self.inner` plus `ptr::read_unaligned` / `ptr::write_unaligned` (or leaving destruction to `drop_glue`).
2. **`E0277` (`Sized`) bans unsized tails that `needs_drop` inside `#[repr(packed)]` (`compiler/rustc_hir_analysis/src/check/wfcheck.rs:1054-1067`):** Because `AddMovesForPackedDrops` requires allocating a stack local `let temp: FieldTy` and executing `temp = move place`, the dropped field type MUST be `Sized`. Consequently `wfcheck` computes:
   ```rust
   let needs_drop_copy = || {
       packed && {
           let ty = tcx.type_of(variant.tail().did).instantiate_identity().skip_norm_wip();
           let ty = tcx.erase_and_anonymize_regions(ty);
           ty.needs_drop(tcx, wfcx.infcx.typing_env(wfcx.param_env))
       }
   };
   let all_sized = all_sized || variant.fields.is_empty() || needs_drop_copy();
   ```
   Thus `#[repr(C, packed)] struct BadUnsized { pad: u8, tail: [AlignedDrop] }` fails with `error[E0277]` (*"the last field of a packed struct may only have a dynamically sized type if it does not need drop to be run"*, `rc = 1`), whereas wrapping the tail in `ManuallyDrop<[AlignedDrop]>` (`needs_drop == false`) compiles cleanly (`rc = 0`).
3. **`E0588` bans `#[repr(align(N))]` transitively inside `#[repr(C, packed)]`:** `#[repr(C, packed)] struct BadPacked { pad: u8, inner: OverAligned }` where `#[repr(align(8))] struct OverAligned(u64)` fails compilation with `error[E0588]: packed type cannot transitively contain a #[repr(align)] type` (`rc = 1` on `14210df0e`). Naturally aligned types such as `struct AlignedDrop(u64)` (`align = 8` without explicit `#[repr(align)]`) are permitted inside `#[repr(C, packed)]` and exercise the full `AddMovesForPackedDrops` machinery.

---

### 4. The `core::ptr::drop_in_place` `-Z ub-checks=yes` Blind Spot vs. `Miri`

`Basis: normative + source + execution + derived`

When unsafe Rust code bypasses automatic scope drops (e.g., inside `ManuallyDrop<Packed>` or custom containers) and invokes `unsafe { core::ptr::drop_in_place(&raw mut (*anchor.0).b) }` on an unaligned field of `#[repr(C, packed)] struct P { a: u8, b: AlignedDrop }` (where `align_of::<AlignedDrop>() == 8` and `(&raw mut (*anchor.0).b as usize) % 8 == 1`), **immediate undefined behavior occurs**, yet `rustc -Z ub-checks=yes` completely fails to detect it at both `-C opt-level=0` and `-C opt-level=2`.

#### Primary-Source Root Cause (Three Interlocking Compiler Mechanisms)

1. **`library/core/src/ptr/mod.rs:836-859` (HEAD `ce66487eb`; `L808-831` in `14210df0e`, `L822-845` in `3ef0c22cd`):**
   ```rust
   #[inline(always)]
   pub const unsafe fn drop_in_place<T: PointeeSized>(to_drop: *mut T)
   where T: [const] Destruct,
   {
       // Due to historic reasons, `drop_in_place` takes a pointer rather than a reference,
       // which results in worse codegen since we don't apply noalias/dereferenceable llvm
       // attributes to pointer arguments. To workaround this without breaking public
       // interface, `drop_in_place` calls the lang item, rather than being one directly.
       unsafe { drop_glue(&mut *to_drop) }
   }
   ```
   Unlike `core::ptr::read`, `core::ptr::write`, or `core::slice::from_raw_parts`, `drop_in_place` contains **zero** `ub_checks::assert_unsafe_precondition!` alignment check. Instead it directly constructs `&mut *to_drop` and passes it to the `#[lang = "drop_glue"]` intrinsic `drop_glue`.

2. **Why `CheckAlignment` skips `drop_in_place` inside `core` (`compiler/rustc_mir_transform/src/check_pointers.rs:230-234`):**
   `CheckAlignment` (`check_alignment.rs:14-35`, enabled whenever `ctx.ub_checks()` is true) delegates pointer discovery to `check_pointers::PointerFinder::visit_place` (`check_pointers.rs:202-250`):
   ```rust
   // Ideally we'd support this in the future, but for now we are limited to sized types.
   if !pointee_ty.is_sized(self.tcx, self.typing_env) {
       trace!("Raw pointer, but pointee is not known to be sized: {:?}", pointer_ty);
       return;
   }
   ```
   Because `drop_in_place` is polymorphic over `T: PointeeSized` (i.e., `?Sized`), `pointee_ty.is_sized(...)` evaluates to **`false`** when `core` is compiled. Therefore `core::ptr::drop_in_place`'s generic MIR contains **no** `AssertKind::MisalignedPointerDereference` check (furthermore, standard precompiled `libcore.rlib` ships without user-requested `-Z ub-checks=yes` instrumentation on non-`assert_unsafe_precondition!` passes).

3. **Why `CheckAlignment` also misses `drop_in_place` in user crates even at `-C opt-level=2` (`lib.rs:711-725` and `check_pointers.rs:74-88`):**
   - In `run_optimization_passes` (`lib.rs:700-725` HEAD; `L675-710` in `14210df0e`), `CheckAlignment` runs **first** (`3-2-001.CheckAlignment`, `L711`), **before** `ForceInline` (`L723`) and `Inline` (`L725`). At `3-2-001.CheckAlignment`, the caller `main` (`raw_drop_in_place.main.3-2-001.CheckAlignment.after.mir`, `L128-129`) contains only:
     ```rust
     _32 = copy _5;
     _31 = drop_in_place::<AlignedDrop>(move _32) -> [return: bb6, unwind continue];
     ```
     There is no `*` dereference on `_5` or `_32` in `main`, so `CheckAlignment` emits **`0`** `MisalignedPointerDereference` assertions! When `-C opt-level=2` later runs `Inline` (`L725`) and inlines `#[inline(always)] drop_in_place`, exposing `&mut *_32` at monomorphic `AlignedDrop`, `CheckAlignment` has already finished and never re-runs.
   - Independently, `check_pointers` (`check_pointers.rs:74-88`) loops **only** over `basic_blocks[block].statements` (`finder.visit_statement(statement, location)`) and never calls `finder.visit_terminator(...)`—even though `PointerFinder::should_visit_place` (`L188`) lists `MutatingUseContext::Drop`—and `make_shim` (`shim.rs:186-201`) never runs `CheckAlignment` on synthesized `DropGlue` shims.

#### Empirical Differential Proof (`support/probe_results.json`)

| Variant (all on odd `&raw mut (*anchor.0).b`, `addr % 8 == 1`, `align_of::<AlignedDrop>() == 8`) | Native `-O0 -Z ub-checks=yes` | Native `-O2 -Z ub-checks=yes` | `Miri` Stacked Borrows | `Miri` Tree Borrows | `main` `CheckAlignment` asserts |
| :--- | :---: | :---: | :---: | :---: | :---: |
| **`raw_drop_in_place`**: `unsafe { ptr::drop_in_place(ptr) }` | **`rc = 0`** (`RAW_DROP_UB_CHECKS_SURVIVED=true`) | **`rc = 0`** (`RAW_DROP_UB_CHECKS_SURVIVED=true`) | **`rc = 1`** (UB at `core/src/ptr/mod.rs:820:24`: unaligned `&mut AlignedDrop`, required `8`, found `1`) | **`rc = 1`** (identical UB at `core/src/ptr/mod.rs:820:24`) | **`0`** |
| **`direct_mut_deref_control`**: `unsafe { let r: &mut AlignedDrop = &mut *ptr; }` | **`rc = -6` (`SIGABRT`)** (`misaligned pointer dereference: address must be a multiple of 0x8`, non-unwinding panic) | *(caught at `-O0`)* | **`rc = 1`** (UB: unaligned reference) | *(UB)* | `>= 1` |
| **`read_unaligned_safe_drop`**: `let v = unsafe { ptr::read_unaligned(&raw const ...) }; drop(v);` | **`rc = 0`** (`SAFE_READ_UNALIGNED_DROP=42`) | *(UB-free)* | **`rc = 0`** (`SAFE_READ_UNALIGNED_DROP=42`) | **`rc = 0`** (`SAFE_READ_UNALIGNED_DROP=42`) | `0` |

Note the critical engineering consequence for `unsafe` Rust authors and verifier builders: **do not rely on `-Z ub-checks=yes` (or debug builds with UB checks) to catch unaligned `ptr::drop_in_place` calls on packed fields.** Manual destruction of an unaligned `ManuallyDrop<Packed>` field must copy the value out to an aligned stack local via `ptr::read_unaligned(&raw const packed.field)` and then drop the aligned local (reproducing in user code what `AddMovesForPackedDrops` emits automatically for compiler-managed drops).

---

### 5. `RemoveUninitDrops` vs. `ElaborateDrops`: Static Move-Path Pruning and Dynamic Stack Drop Flags

`Basis: source + execution`

#### `RemoveUninitDrops` (`remove_uninit_drops.rs:19-160`) and `const_precise_live_drops` Gating

`RemoveUninitDrops` runs in `run_analysis_to_runtime_passes` (`lib.rs:617-628` HEAD; `L581-592` in `14210df0e`) immediately after `Analysis(PostCleanup)` and **before** `run_runtime_lowering_passes` (`ElaborateDrops`), **if and only if** `check_consts::post_drop_elaboration::checking_enabled(&ConstCx::new(tcx, body))` returns `true`:

```rust
// compiler/rustc_const_eval/src/check_consts/post_drop_elaboration.rs:14-26 (HEAD ce66487eb)
pub fn checking_enabled(ccx: &ConstCx<'_, '_>) -> bool {
    if ccx.enforce_recursive_const_stability() {
        return rustc_allow_const_fn_unstable(
            ccx.tcx,
            ccx.body.source.def_id().expect_local(),
            sym::const_precise_live_drops,
        );
    }
    ccx.tcx.features().const_precise_live_drops()
}
```

Two non-obvious behaviors were established directly from source and confirmed by live MIR dumps (`support/probe_results.json`, `remove_uninit_drops_const`):
1. **Inactive on stable/plain crates:** Compiling an ordinary crate without `#![feature(const_precise_live_drops)]` produces **zero** `RemoveUninitDrops` MIR dumps (`plain_non_const_remove_uninit_drops_dumps: []`); dead drops in ordinary code are erased later by `ElaborateDrops` (`DropStyle::Dead`).
2. **Crate-wide activation under `#![feature(const_precise_live_drops)]`:** Because `checking_enabled` returns `ccx.tcx.features().const_precise_live_drops()` without checking `ccx.const_kind.is_some()` (that check lives inside `check_live_drops`, `L33`), enabling `#![feature(const_precise_live_drops)]` causes `2-2-001.RemoveUninitDrops` to run on **both** `const_extract_both` and `runtime_extract_both`. In `const_extract_both` (`support/mir_excerpts/remove_uninit_drops_const.const_extract_both.2-2-001.RemoveUninitDrops.{before,after}.mir`), moving both fields `(p.a, p.b)` out of `#[repr(C, packed)] struct PackedPair { tag: u8, a: NonCopy, b: NonCopy }` leaves `MaybeInitializedPlaces` empty on both field move paths at all `5` drop terminators (`bb0`: `drop(_3)`, `bb1`: `drop(_2)`, `bb2`: `drop(_1)`, `bb4`: `drop(_2)`, `bb5`: `drop(_1)`). `is_needs_drop_and_init` (`remove_uninit_drops.rs:75-148`) returns `false` for all five (recursing into `PackedPair`'s fields because `adt.has_dtor(tcx)` is `false` and `tag: u8` has `needs_drop == false`), replacing `5 -> 0` `Drop` terminators with `0 -> 5` `Goto` terminators before `CheckLiveDrops` (`2-2-003`) and `ElaborateDrops` (`2-2-007`) run.
3. **Why `RemoveUninitDrops` exists separately from `ElaborateDrops` (`remove_uninit_drops.rs:14-18`):** Running const-checking after full `ElaborateDrops` would couple const acceptance to optimization/elaboration details (issue `#90770`), so `RemoveUninitDrops` performs only monotone `MaybeInitializedPlaces`-based dead-drop erasure without allocating drop flags or opening partial-move ladders (and immediately returns `true` for unions, `ManuallyDrop`, and ADTs with `adt.has_dtor(tcx)` at `L101-104`).

#### `ElaborateDrops` (`elaborate_drops.rs:51-521`): Four-Way Classification and Minimal Stack Drop Flags

In `ElaborateDrops::run_pass` (`elaborate_drops.rs:53-87`), `rustc` runs three analyses and four patch phases:
1. **`MoveData::gather_moves(body, tcx, |ty| ty.needs_drop(tcx, typing_env))` (`L58`):** Builds the move-path tree exclusively over types that `needs_drop` (so `pad: u8` in `PackedNoImplDrop` has no drop move path and never spawns a flag).
2. **Dual dataflow fixpoints (`L62-73`):** Computes `MaybeInitializedPlaces` (with `.exclude_inactive_in_otherwise().skipping_unreachable_unwind()`), derives `dead_unwinds` (`compute_dead_unwinds`, `L98-119`), and then computes `MaybeUninitializedPlaces` (with `.mark_inactive_variants_as_uninit().skipping_unreachable_unwind(dead_unwinds)`).
3. **Minimal flag collection (`collect_drop_flags`, `L290-334`):** Walks every `TerminatorKind::Drop { place }`, looks up `LookupResult::Exact(path)`, and inspects every child move path `child`: a stack local `_flag: bool` is created **if and only if** `maybe_init && maybe_uninit` (`L310-312`).
4. **Four-way `drop_style` decision (`L165-188`):**
   - `(false, _, _)` -> **`DropStyle::Dead`** (replaced with `goto -> target`)
   - `(true, false, _)` -> **`DropStyle::Static`** (unconditional `drop(place)` — no flag test!)
   - `(true, true, false)` -> **`DropStyle::Conditional`** (`switchInt(copy _flag) -> [0: skip, otherwise: drop(place)]`)
   - `(true, true, true)` -> **`DropStyle::Open`** (opens aggregate into per-field drop ladder, recursing on each field's move path)
5. **Flag initialization and updates (`L282-286, 424-520`):**
   - `drop_flags_on_init` (`L424-431`) emits `_flag = const false;` at `Location::START` for every allocated flag;
   - `drop_flags_for_args` (`L453-462`) sets flags to `true` for owned function arguments;
   - `drop_flags_for_locs` (`L464-520`) sets flags to `true` on initialization/assignment and clears them to `false` on moves and `StorageDead` via `rustc_mir_dataflow::drop_flag_effects_for_location`.

#### Verbatim Live MIR Trace: `partial_move_and_dynamic_drop_flag` (`ElaborateDrops` -> `AddMovesForPackedDrops`)

In `packed_ok.partial_move_and_dynamic_drop_flag` (`support/mir_excerpts/packed_ok.partial_move_and_dynamic_drop_flag.2-2-007.AddMovesForPackedDrops.{before,after}.mir`):

```rust
// Key blocks after 2-2-004.ElaborateDrops AND 2-2-007.AddMovesForPackedDrops:
bb0: {
    _13 = const false;                         // drop_flags_on_init for (_4.1: AlignedDrop) ONLY!
    ...
    _13 = const true;                          // drop_flags_for_locs on struct construction
    _4 = PackedNoImplDrop { pad: const 3_u8, first: move _5, second: move _7 };
    goto -> bb1;
}
bb3: {                                         // if take_first == true
    StorageLive(_10);
    _13 = const false;                         // clears drop flag BEFORE moving _4.1 out!
    _10 = move (_4.1: AlignedDrop);
    ...
    _11 = std::mem::drop::<AlignedDrop>(move _12) -> [return: bb4, unwind: bb9];
}
bb18: {                                        // open-drop ladder entry for _4 at scope exit
    switchInt(copy _13) -> [0: bb15, otherwise: bb17];
}
bb17: {                                        // conditional drop of _4.1 (ONLY if _13 == true)
    StorageLive(_16);
    _16 = move (_4.1: AlignedDrop);
    drop(_16) -> [return: bb23, unwind: bb14];
}
bb23: { StorageDead(_16); goto -> bb15; }
bb15: {                                        // STATIC drop of _4.2 (NO flag test!)
    StorageLive(_15);
    _15 = move (_4.2: AlignedDrop);
    drop(_15) -> [return: bb22, unwind: bb12];
}
bb22: { StorageDead(_15); goto -> bb13; }
bb19 (cleanup): {                              // unwind from drop(moved): _4.1 statically Dead!
    StorageLive(_17);
    _17 = move (_4.2: AlignedDrop);
    drop(_17) -> [return: bb24, unwind terminate(cleanup)];
}
```

#### Empirical MIR Transformation Accounting & Cross-Backend Execution (`packed_ok`, `PACKED_DROP_LOG=1637`)

| Function / Shim (`packed_ok`) | MIR Dump Pass | `Drop` Terms | `StorageLive` | `StorageDead` | `switchInt` | `bool` Locals | `goto` Terms |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `core::ptr::drop_glue::<PackedNoImplDrop>` | `1-1-001.AddMovesForPackedDrops` (before -> after) | `4 -> 4` | `0 -> 4` | `0 -> 4` | `0 -> 0` | `0 -> 0` | `2 -> 6` |
| `core::ptr::drop_glue::<PackedWithImplDrop>` | `1-1-001.AddMovesForPackedDrops` (before -> after) | `2 -> 2` | `0 -> 2` | `0 -> 2` | `0 -> 0` | `0 -> 0` | `2 -> 4` |
| `drop_whole_packed` | `2-2-004.ElaborateDrops` (before -> after) | `5 -> 2` | `70 -> 70` | `52 -> 52` | `4 -> 4` | `4 -> 4` | `0 -> 3` |
| `drop_whole_packed` | `2-2-007.AddMovesForPackedDrops` (before -> after) | `2 -> 2` | `70 -> 70` | `52 -> 52` | `4 -> 4` | `4 -> 4` | `2 -> 2` |
| `packed_with_own_drop` | `2-2-004.ElaborateDrops` (before -> after) | `2 -> 1` | `3 -> 3` | `3 -> 3` | `0 -> 0` | `0 -> 0` | `0 -> 1` |
| `packed_with_own_drop` | `2-2-007.AddMovesForPackedDrops` (before -> after) | `1 -> 1` | `3 -> 3` | `3 -> 3` | `0 -> 0` | `0 -> 0` | `1 -> 1` |
| `partial_move_and_dynamic_drop_flag` | `2-2-004.ElaborateDrops` (before -> after) | `8 -> 5` | `9 -> 9` | `9 -> 9` | `1 -> 3` | `1 -> 2` | `2 -> 14` |
| `partial_move_and_dynamic_drop_flag` | `2-2-007.AddMovesForPackedDrops` (before -> after) | `4 -> 4` | `9 -> 13` | `9 -> 13` | `2 -> 2` | `2 -> 2` | `12 -> 16` |
| `const_extract_both` (`const_precise_live_drops`) | `2-2-001.RemoveUninitDrops` (before -> after) | `5 -> 0` | `2 -> 2` | `2 -> 2` | `0 -> 0` | `0 -> 0` | `0 -> 5` |

*(Note: Between `2-2-004.ElaborateDrops.after` and `2-2-007.AddMovesForPackedDrops.before` in `partial_move_and_dynamic_drop_flag`, `2-2-006.AbortUnwindingCalls` / intermediate passes pruned 1 unreachable cleanup drop and 1 dead switch branch (`drop_terminators: 5 -> 4`, `switchInt: 3 -> 2`). Every runtime invocation—native `-O0`, native `-Z ub-checks=yes`, `Miri` Stacked Borrows, and `Miri` Tree Borrows—returned exit code `0` with identical stdout `PACKED_DROP_LOG=1637` (`100 + 200 + 1000 + 300 + 20 + 10 + 2 + 5`) and passed every alignment assertion inside `AlignedDrop::drop` and `PackedWithImplDrop::drop`.)*

---

### 6. Kernel-Checked Lean `v4.34.1` Formalization (`PackedDropsSoundness`)

`Basis: source + execution (Lean kernel) + derived`

The standalone Lean 4 (`v4.34.1`) module `support/PackedDropsCheckPackedRefAndElaborateDropsSoundness.lean` (`1,742` lines, `79,593` bytes, SHA-256 `c2d5cd441ae693e8480b0e19a5b8b8c6bdbdd2d4a1904f22bd8b38d4b621a3c0`) formalizes the alignment arithmetic, `CheckPackedRef` / `place_unalignment`, `AddMovesForPackedDrops` / `drop_glue` / `drop_in_place`, and `RemoveUninitDrops` / `ElaborateDrops` semantics and proves end-to-end soundness plus four sharpness counterexamples.

#### Kernel Purity & Environment Audit Receipt (`support/lean_check_receipt.json`)

Compiled synchronously with full kernel type checking and warnings treated as errors (`lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and walked by `support/AuditPackedDropsLean.lean` across every constant in the module's `.olean` environment:

| Audit Dimension | Verified Measurement |
| :--- | :--- |
| Lean toolchain | `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)` |
| Source metrics | `1,742` lines (`1,600` non-empty), `59` user `theorem`s, `52` `noncomputable def`s, `19` inductive/structure types |
| Forbidden source tokens (`sorry`, `admit`, `omega`, `bv_decide`, `native_decide`, `partial`, `unsafe`, `axiom`, `opaque`, `implemented_by`, `extern`, `Classical`, `_unsafe_rec`) | **`0` across all 13 tokens** (whole-word, case-insensitive, comments included) |
| Compilation | `exit_code = 0`, `0` errors, `0` warnings, `3.321 s` wall time, `551,376 kB` peak RSS, `1,835,800 B` `.olean` |
| Kernel environment walk (`AuditPackedDropsLean.lean`) | `614` constants (`185` kernel theorems incl. equation lemmas, `114` axiom-free; `338` definitions, all `.safe`; `20` inductives; `51` constructors; `20` recursors) |
| `_unsafe_rec` helpers / non-`.safe` defs / axioms / opaque / quot | **`0` violations** (`noncomputable def` suppresses Lean's recursive codegen `_unsafe_rec` helpers while preserving full kernel definitional reduction) |
| Axioms used across entire module | **`[propext]` only** (`0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `Lean.ofReduceBool`) |

#### Design Structure and Theorem Catalog

1. **Section 1 — Constructive Power-of-Two Alignment Exponent Algebra (`L45-225`):**
   Models `rustc_abi::Align` directly by its base-2 exponent `e : Nat` (`alignBytes e := 2 ^ e`), matching `rustc`'s internal log-2 alignment representation. Address alignment is `addrAligned addr e := alignBytes e ∣ addr`. All minimum lattice laws (`natMin_le_left`, `natMin_le_right`, `le_natMin`, `natMin_comm`, `natMin_assoc`, `natMin_le_natMin`), power-of-two divisibility monotonicity (`alignBytes_dvd_of_le`), address monotonicity (`addrAligned_mono`), offset preservation (`addrAligned_add`, `addrAligned_add_min`), and concrete odd-address non-alignment witnesses (`not_addrAligned_one_of_pos`, `not_addrAligned_17_3`) are proved constructively without `omega` or `Classical.choice`.

2. **Section 2 — `CheckPackedRef` & `util::place_unalignment` (`L226-683`):**
   - `PlaceContext` enumerates `sharedBorrow`, `mutBorrow`, `rawBorrowConst`, `rawBorrowMut`, `fakeBorrow`, `copy`, `move_`, `store`, `drop`, with `isBorrow` matching only `sharedBorrow | mutBorrow` and `isAddressOf` matching only `rawBorrowConst | rawBorrowMut` (`visit.rs:1392-1407`).
   - `ProjStep` models `.deref pointeeAlignExp derefTargetAddr` and `.field basePack fieldOffset fieldAlignExp`. `mostPackedProjection` (`mostPackedGo`) resets its accumulator to `none` on every `.deref` and takes `natMin` over all `some p` packed ADT bases after the last `.deref`, directly mirroring `compiler/rustc_const_eval/src/util/alignment.rs:56-78`.
   - `placeUnalignment` mirrors `alignment.rs:9-51`: returns `none` iff `mostPackedProjection = none` or `place.layout` is `.knownSized a` / `.knownSliceOrStr a` with `a ≤ pack`, conservatively returning `some pack` on `.unknownOrOpaqueUnsized`.
   - `WfProjs` and `WfMirPlace` encode Rust's ABI and `#[repr(packed(2^p))]` layout guarantees (aligned base locals, aligned deref target pointers, unpacked offsets divisible by `2^fAlign`, packed offsets divisible by `2^(min fAlign p)`).
   - **Core Theorem 1 (`checkPackedRef_implies_all_borrows_aligned`, `L591`):**
     ```lean
     theorem checkPackedRef_implies_all_borrows_aligned
         {uses : List PlaceUse} (hCheck : checkPackedRef uses = true)
         {u : PlaceUse} (hMem : u ∈ uses) (hBorrow : u.ctx.isBorrow = true)
         {baseAddr reqAlign : Nat} (hwf : WfMirPlace baseAddr u.place reqAlign) :
         addrAligned (evalPlaceAddr baseAddr u.place) reqAlign
     ```
     Proved via `wfProjs_addrAligned`, `wfProjs_finalAlign_eq` (which inductively relates guaranteed runtime alignment to `projectedTypeAlign` and `mostPackedGo`), and `placeUnalignment_none_implies_aligned`.
   - **Boundary & Sharpness Corollaries (`L617-683`):**
     - `align1_borrow_passes_checkPackedRef`: `&p.pad` (`align = 1 <= 1`) accepted;
     - `packed_u32_borrow_rejected_E0793`: `&p.inner` (`align = 4 > 1`) rejected;
     - `raw_borrow_passes_checkPackedRef_even_unaligned`: `&raw const p.inner` and `&raw mut p.inner` accepted even when `placeUnalignment = some 0`;
     - `deref_resets_packed_projection`: `&*holder.r` resets `mostPackedProjection` to `none` and passes;
     - `nested_packed_takes_minimum_pack`: `packed(2)` enclosing `packed(4)` yields `some 1`, accepting `u16` and rejecting `u32`;
     - `generic_unknown_layout_rejected_conservatively`: `.unknownOrOpaqueUnsized` yields `some 0` and fails `checkPackedRef`;
     - `counterexample_unaligned_borrow_ub`: skipping `CheckPackedRef` on `&p.inner` at base `0` yields address `1` with `¬ addrAligned 1 2`.

3. **Section 3 — `AddMovesForPackedDrops`, `PackedWithImplDrop` `drop_glue`, and the `drop_in_place` Gap (`L685-1195`):**
   - `LeafDropOp` (`directDrop`, `stagedAlignedDrop`) and `DropOp` (`leaf`, `customSelfDropThenFields`, `manualDropInPlace`, `directMutDeref`) keep recursion strictly structural (zero nested `List.map` recursion, zero `._unsafe_rec`).
   - `execStagedTemp` explicitly steps a fresh temporary stack slot through `dead -> liveUninit (StorageLive) -> liveInit payload (temp = move place) -> drop(&mut temp)` and verifies return-edge cleanup `-> dead (StorageDead)` on normal return vs. unwind bypass (`execStagedTemp_aligned`, `L955`).
   - `evalDropOp` / `evalDropOps` enforce Rust/Miri reference-alignment validity (`addr % 2^reqAlign == 0`), faulting `.ubMisalignedSelf dtorId addr reqAlign` on any unaligned `&mut self` invocation. `idealDropOp` / `idealDropOps` give the alignment-independent ownership destructor trace (including `<PackedWithImplDrop as Drop>::drop` running first and cleanup field drops running even when custom `Drop` panics).
   - **Core Theorem 2 (`addMovesForPackedDrops_eliminates_unaligned_drop_self_ub`, `L1089`):**
     ```lean
     theorem addMovesForPackedDrops_eliminates_unaligned_drop_self_ub
         {allocAligned : Nat → Nat} (hAlloc : AllocSound allocAligned)
         {ops : List DropOp} (hwf : ∀ op, op ∈ ops → WfCompilerDropOp op) :
         evalDropOps (addMovesForPackedDrops allocAligned ops) = idealDropOps ops ∧
         (∀ d a r, evalDropOps (addMovesForPackedDrops allocAligned ops) ≠ .ubMisalignedSelf d a r)
     ```
   - **Counterexamples (`L1159-1195`):**
     - `drop_in_place_ub_checks_gap_counterexample`: On `&raw mut p.b` at odd address `17` (`reqAlign = 3`), `checkAlignmentCatchesOp (.manualDropInPlace 17 3 1 42) = false`, `evalDropOp (.manualDropInPlace 17 3 1 42) = .ubMisalignedSelf 1 17 3`, control `checkAlignmentCatchesOp (.directMutDeref 17 3) = true`, and safe staged extraction `evalDropOp (.leaf (.stagedAlignedDrop targetPackedB 32)) = .ok [{ dtorId := 1, payload := 42 }]`.
     - `packedWithImplDrop_before_vs_after_addMoves`: At odd base `17`, before `AddMovesForPackedDrops` `PackedWithImplDrop` faults `.ubMisalignedSelf 300 18 3` on its inner field drop; after `AddMovesForPackedDrops` it succeeds with `.ok [{ dtorId := 1000, payload := 1 }, { dtorId := 300, payload := 33 }]` (custom `Drop` first, aligned-temp inner `Drop` second).

4. **Sections 4–6 — `RemoveUninitDrops`, `ElaborateDrops`, Composed Pipeline Soundness, and Pass-Ordering Counterexample (`L1197-1742`):**
   - `DropStyle` (`dead`, `static_`, `conditional`, `open_`) and `classifyDropStyle` mirror `elaborate_drops.rs:165-188`.
   - `FieldInvariant` captures dataflow over-approximation (`live = true → maybeInit = true`, `live = false → maybeUninit = true`) and dynamic flag tracking (`maybeInit = true → maybeUninit = true → flag = live`).
   - **Core Theorem 3 (`elaborateDrops_drop_each_live_leaf_once`, `L1408`):**
     ```lean
     theorem elaborateDrops_drop_each_live_leaf_once
         {fields : List FieldDynState}
         (hInv : ∀ s, s ∈ fields → FieldInvariant s)
         (hNodup : fieldIdsNodup fields) :
         elaboratedDroppedIds fields = sourceDroppedIds fields ∧
         ∀ s, s ∈ fields →
           countId s.spec.fieldId (elaboratedDroppedIds fields) =
             if s.spec.needsDrop && s.live then 1 else 0
     ```
   - **`RemoveUninitDrops` Soundness (`removeUninitDrops_preserves_semantics`, `L1465`, zero axioms `[]`):** Whenever `removeUninitDropsShouldKeep fields = false`, `sourceDroppedIds fields = []`.
   - **Composed Pipeline Theorem (`full_packed_drop_pipeline_soundness`, `L1622`):** For any packed struct at any valid base address (including odd addresses for `pack = 0`), running `ElaborateDrops` (`fieldStateToDropOps`) followed by `AddMovesForPackedDrops` executes with zero misaligned-`self` UB, produces the exact declaration-order trace `.ok (sourceDropEvents fields)`, and drops every live `needsDrop` leaf exactly once.
   - **Concrete Instantiations & Sharpness Witnesses (`L1669-1742`):**
     - `partialMove_takeFirst_true_exact` (`[2]`, tag `10`) and `partialMove_takeFirst_false_exact` (`[1, 2]`, tags `2, 5`), mirroring `partial_move_and_dynamic_drop_flag`;
     - `pipeline_order_counterexample`: `placeUnalignment wholePackedLocal = none` (early `AddMovesForPackedDrops` is a no-op), unlowered post-`ElaborateDrops` field drops fault `.ubMisalignedSelf 2 34 3`, and post-`ElaborateDrops` `AddMovesForPackedDrops` succeeds with `.ok [{ dtorId := 2, payload := 10 }]`;
     - `constExtractBoth_and_staleFlag_counterexample`: `const_extract_both` erases cleanly (`removeUninitDropsShouldKeep = false`, `sourceDroppedIds = []`), while a broken stale drop flag (`live = false, flag = true`) causes double-drop (`[1, 2]` vs. `[2]`).

---

### 7. Implications for Anneal's Trusted Boundary (`joshlf/anneal@c131b320eeeb`)

`Basis: source + derived`

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean`) shows exactly what Anneal's current `Runtime(PostCleanup)` MIR trusted boundary accepts, rejects, and must eventually extend to verify packed-struct drops:

1. **Current fail-closed coverage (`MirAst.lean` & `MirSemantics.lean`):**
   - `MirTy` (`MirAst.lean:312-321`) models `.bool`, `.int`, `.unit`, `.never`, fieldless `.enum`, `.tuple`, `.ref`, `.rawPtr`, and `.unsupported`; **all non-fieldless-enum ADTs (including `#[repr(packed)]` structs) map to `MirTy.unsupported`** (`L308-311`).
   - `TerminatorKind` (`MirAst.lean:782-795`) maps `TerminatorKind::Drop` and `UnwindTerminate` to `TerminatorKind.unsupported` (`L782-784`).
   - `Rvalue` (`MirAst.lean:620-628`) includes `.ref` and `.addressOf` syntactically, but `Trusted.MirSemantics.evalRvalue` (`MirSemantics.lean:1240-1313`) routes both to `.error .unsupported` (`L1313`), and `evalOperandToSlot` (`MirSemantics.lean:949-976`) fails closed on any non-empty `place.projection` (`L953, 962`) while enforcing `deinitMovedPlace = true` on unprojected non-ZST `.move` operands (`L961-971`).
2. **Capture-stage alignment with `Runtime(PostCleanup)` MIR:**
   Because Anneal captures MIR at `MirPhase::Runtime(RuntimePhase::PostCleanup)` (`lib.rs:691`), **both `ElaborateDrops` (`L665`) and `AddMovesForPackedDrops` (`L674`) have already run** on every user body before capture, and `make_shim` (`shim.rs:191`) has already run `AddMovesForPackedDrops` on every `DropGlue` shim. Consequently, once Anneal extends `Trusted.MirAst` and `Trusted.MirSemantics` to structs, projections, and `TerminatorKind::Drop`:
   - Anneal will never need to model conditional pre-elaboration `Drop` semantics or implicit unaligned-field extraction in `Runtime(PostCleanup)` user bodies (they already appear explicitly as `switchInt` over `bool` drop-flag locals + `StorageLive(temp); temp = move p.f; drop(temp); StorageDead(temp)`).
   - **However**, Anneal's memory model **must** preserve byte-level unaligned `Operand::Move` on packed field projections (without requiring `align_of::<FieldTy>()` on the source address) while strictly enforcing `align_of::<T>()` reference validity on `Rvalue::Ref`, `TerminatorKind::Drop` / `drop_glue(&mut T)`, and `core::ptr::drop_in_place` calls—and must NOT assume that `rustc -Z ub-checks=yes` tests guard `drop_in_place` call sites.
   - Note also `Trusted.MirSemantics.evalStatement` (`MirSemantics.lean:1356-1360`): because `AddMovesForPackedDrops` omits `StorageDead(temp)` on the unwind edge of `drop(temp)` (`add_moves_for_packed_drops.rs:93-110`), any future unwinding semantics in `Trusted.MirSemantics` must reclaim frame locals on unwind frame pop rather than assuming every `StorageLive(temp)` is paired with an explicit `StorageDead(temp)` on cleanup paths.

## Boundaries

`Basis: source + execution + derived`

To prevent a future reader from over-generalizing these findings beyond what primary source, execution, and the Lean kernel actually establish, we separate negative space using the four contract categories:

1. **Known not to apply — `AddMovesForPackedDrops` before `ElaborateDrops`:**
   Running `AddMovesForPackedDrops` in `Analysis(PostCleanup)` before `ElaborateDrops` does **not** occur in `rustc` (`14210df0e`, `3ef0c22cd`, or `ce66487eb`), and would leave field-granular drops generated by `ElaborateDrops` on partially moved packed structs unaligned (`pipeline_order_counterexample`). The pass runs at `2-2-007` in `run_runtime_lowering_passes` (after `2-2-004.ElaborateDrops`) and at `1-1-001` in `make_shim` (after `DropShimElaborator`).

2. **Known not to apply — `compiler/rustc_mir_transform/src/util.rs` path:**
   That file path does not exist (`HTTP 404` across `14210df0e`, `3ef0c22cd`, and `ce66487eb`). `place_unalignment` and `most_packed_projection` live in `compiler/rustc_const_eval/src/util/alignment.rs`, imported into `rustc_mir_transform` via `use rustc_const_eval::util;` (`lib.rs:15`).

3. **Known not to apply — `RemoveUninitDrops` on ordinary non-const crates:**
   `RemoveUninitDrops` does **not** execute when `#![feature(const_precise_live_drops)]` (or `#[rustc_allow_const_fn_unstable(const_precise_live_drops)]`) is absent (`plain_non_const_remove_uninit_drops_dumps = []`). Conversely, when `#![feature(const_precise_live_drops)]` *is* enabled on a crate, `checking_enabled` activates `RemoveUninitDrops` crate-wide (on non-`const` functions too, as verified on `runtime_extract_both`), not solely on `const fn` items.

4. **Known not to apply — `-Z ub-checks=yes` as an oracle for `core::ptr::drop_in_place`:**
   `-Z ub-checks=yes` (`CheckAlignment`) does **not** catch misaligned `core::ptr::drop_in_place(&raw mut packed.field)` at either `-O0` or `-O2`, even though it catches direct `&mut *ptr` in user code. Only `Miri` (or an explicit manual alignment check / `ptr::read_unaligned`) catches or avoids this UB.

5. **Known not to apply — Lean formalization vs. `rustc` Rust source and Anneal `Trusted.*`:**
   `support/PackedDropsCheckPackedRefAndElaborateDropsSoundness.lean` is a standalone model over explicit finite Lean types. It is **not** a mechanized proof of `rustc`'s Rust implementation, it does **not** import `joshlf/anneal`'s `Trusted.MirAst` / `Trusted.MirSemantics`, and its `FieldInvariant` hypothesis assumes the upstream dataflow analyses (`MaybeInitializedPlaces` / `MaybeUninitializedPlaces`) and drop-flag updates (`drop_flag_effects_for_location`) satisfy sound over-approximation rather than verifying the iterative bitset fixpoint solver itself.

6. **Not examined — Async drops (`AsyncDropGlue`, `FutureDropPoll`), coroutines, enums, `Box` deref-move, arrays, and unions with `ManuallyDrop`:**
   - Async drop shims (`shim.rs:131-176`, `build_async_drop_shim`) and coroutine drop shims (`shim.rs:100-123`) take separate pass lists in `make_shim` that do **not** pass through `shim.rs:191`'s `AddMovesForPackedDrops` call (notice `async_drop` runs `run_optimization_passes` directly). Whether `build_async_drop_shim` handles packed fields via a separate staging mechanism was **not examined**.
   - Multi-variant `enum` discriminant drops, `Box<T>` partial-move `Deref` drops, array reverse-range open drops (`[a0, a1]` after moving `a0`), and `#[repr(packed)]` unions containing `ManuallyDrop<T>` were **not examined** in our probe or Lean model (general non-packed enum/array/unwind elaboration is covered in peer package `rustc-drop-elaboration-drop-flags-and-unwind-cleanup-mir-refinement`).
   - Non-`x86_64` execution targets (e.g., strict-alignment hardware architectures such as `sparc64` or `armv7` where unaligned native `SIGBUS` traps can occur independently of `-Z ub-checks`, or 32-bit targets where `align_of::<u64>() == 4`) and `max_reliable_alignment() < Align::MAX` targets (`check_alignment.rs:86-108`) were **not examined** empirically.
   - Live execution on `rustc 1.102.0-nightly (3ef0c22cd)` and HEAD (`ce66487eb`): those two revisions were audited by full primary-source inspection and line-by-line diff against `14210df0e`; live compilation/MIR/Miri execution in `support/probe_results.json` ran on `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)` and `miri 0.1.0 (14210df0e2 2026-05-31)`.

7. **Unsupported — `rustc` packed unsized droppable tails & Anneal MIR `Drop` / packed ADTs:**
   - `rustc` explicitly rejects `#[repr(packed)]` structs whose unsized tail satisfies `needs_drop` (`wfcheck.rs:1056-1067`, `E0277`).
   - `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` explicitly fails closed (`.unsupported`) on `TerminatorKind::Drop`, non-fieldless-enum ADTs, projections, `.ref`, and `.addressOf`.

## Evidence

All primary evidence was acquired and verified on `2026-11-22`. Machine-checked receipts and reproducible scripts are preserved inside this package's `support/` directory.

### 1. Verified Upstream Git Commit & File Pins (`support/pin_receipt.json`, `support/verify_pins.py`)

Every 40-hex commit SHA was resolved live against the GitHub API (`36/36` commit and raw-file checks passed):

- **`rust-lang/rust@ce66487ebbd7541212d22d01c39a808057d69f1f`** (`2026-11-22T17:08:30Z`, HEAD):
  - `compiler/rustc_mir_transform/src/check_packed_ref.rs:1-50` (`CheckPackedRef`, `PackedRefChecker::visit_place`, `span_bug!` on builtin derive, `diagnostics::UnalignedPackedRef`)
  - `compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:1-111` (`AddMovesForPackedDrops`, `PassPolicy::Required`, `body.typing_env(tcx)`, `add_move_for_packed_drop`)
  - `compiler/rustc_mir_transform/src/util.rs` — verified HTTP **`404`** (absent)
  - `compiler/rustc_const_eval/src/util/alignment.rs:1-78` (`place_unalignment` `L9-51`, `most_packed_projection` `L56-78`, `layout.align <= pack` `L28`, `Deref` cutoff `L68`)
  - `compiler/rustc_mir_transform/src/remove_uninit_drops.rs:1-160` (`RemoveUninitDrops`, `PassPolicy::Required`, `is_needs_drop_and_init` `L75-148`)
  - `compiler/rustc_mir_transform/src/elaborate_drops.rs:1-521` (`ElaborateDrops`, `PassPolicy::Required`, `drop_style` `L165-188`, `collect_drop_flags` `L290-334`, `drop_flags_on_init` `L424-431`, `drop_flags_for_locs` `L464-520`)
  - `compiler/rustc_mir_transform/src/elaborate_drop.rs:1012-1068, 1208-1254` (`open_drop_for_adt`, `open_drop_for_adt_contents`, `destructor_call_block_sync`)
  - `compiler/rustc_mir_transform/src/lib.rs:15, 422, 608-681, 700-745` (`use rustc_const_eval::util`, `CheckPackedRef`, `RemoveUninitDrops` gating `L617-628`, `ElaborateDrops` `L665` -> `AddMovesForPackedDrops` `L674`, `CheckAlignment` `L711` -> `ForceInline` `L723` -> `Inline` `L725`)
  - `compiler/rustc_mir_transform/src/shim.rs:125, 186-205, 258-408` (`build_drop_shim`, `DropShimElaborator`, `make_shim` running `AddMovesForPackedDrops` `L191` with no `CheckAlignment`)
  - `compiler/rustc_mir_transform/src/check_alignment.rs:1-148` (`CheckAlignment`, `PassPolicy::optional(ctx.ub_checks())`, `insert_alignment_check`)
  - `compiler/rustc_mir_transform/src/check_pointers.rs:1-251` (statements-only loop `L74-88`, `should_visit_place` `L182-198`, `!pointee_ty.is_sized(...)` skip `L231-234`)
  - `compiler/rustc_mir_transform/src/diagnostics.rs:56-75` (`UnalignedPackedRef`, `code = E0793`)
  - `compiler/rustc_const_eval/src/check_consts/post_drop_elaboration.rs:14-48` (`checking_enabled`, `check_live_drops`)
  - `compiler/rustc_middle/src/mir/visit.rs:1383-1417` (`PlaceContext::is_borrow`, `PlaceContext::is_address_of` with `RawBorrow`)
  - `compiler/rustc_mir_dataflow/src/move_paths/builder.rs:180-188` (`if adt.has_dtor(tcx) { return; }`)
  - `compiler/rustc_hir_analysis/src/check/wfcheck.rs:979-1067` (`packed` + `needs_drop_copy` forcing `Sized` on trailing field)
  - `library/core/src/ptr/mod.rs:832-859` (`pub const unsafe fn drop_in_place<T: PointeeSized>` calling `drop_glue(&mut *to_drop)` at `L848`)
- **`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`** (`2026-11-11T17:59:24Z`, `1.102.0-nightly`):
  - `check_packed_ref.rs` (`50` L), `add_moves_for_packed_drops.rs` (`113` L, `PassPolicy::Required`, `TypingEnv::post_analysis`), `rustc_const_eval/src/util/alignment.rs` (`78` L, `layout.align <= pack`), `lib.rs` (`CheckPackedRef` `L422`, `RemoveUninitDrops` `L622`, `ElaborateDrops` `L663`, `AddMovesForPackedDrops` `L672`, `CheckAlignment` `L709`), `library/core/src/ptr/mod.rs:822-845` (`L834`).
- **`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (`2026-05-31T20:13:59Z`, `1.98.0-nightly`, host `x86_64-unknown-linux-gnu`, LLVM `22.1.6`, `miri 0.1.0`):
  - `check_packed_ref.rs` (`61` L, `errors::UnalignedPackedRef`), `add_moves_for_packed_drops.rs` (`115` L, `is_required() -> true`, 6-field `Drop` incl. `async_fut`), `rustc_const_eval/src/util/alignment.rs` (`78` L, `layout.align.abi <= pack`), `errors.rs:56-75`, `lib.rs` (`L408, 586, 634, 643, 695`), `library/core/src/ptr/mod.rs:804-831` (`L820`).
- **`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`** (`2026-11-17T20:49:56Z`):
  - `src/type-layout.md:140-154, 632-671` (`r[layout.repr.alignment.*]`), `src/behavior-considered-undefined.md:78-100` (`r[undefined.misaligned.*]`), `src/destructors.md:1-60` (`r[destructors.operation]`, `r[destructors.drop_in_place]`).
- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`** (`2026-11-19T21:39:21Z`):
  - `trusted/lean/Trusted/MirAst.lean:75-92, 308-321, 608-628, 782-795`; `trusted/lean/Trusted/MirSemantics.lean:949-976, 1240-1313, 1356-1375`.
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`** (`2026-09-24T17:27:27Z`, `v4.34.1`).

### 2. Preserved Package Support Artifacts (`support/`)

| Artifact | Purpose & Measured Status |
| :--- | :--- |
| `support/probe_packed_drops_and_elaborate_drops.py` | Self-contained live `rustc` + `Miri` differential probe script (5 test suites, 12 acceptance assertions, zero hardcoded metrics, automatic path sanitization). |
| `support/probe_results.json` | Complete machine-readable JSON output from running the probe on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0`: **`all_checks_passed: true`** (`12/12` checks green, `PACKED_DROP_LOG=1637` across native/`-Z ub-checks=yes`/`Miri` SB/`Miri` TB, `10/10` `CheckPackedRef` matrix matches, `4/4` packed-drop type-rule matches, `drop_in_place` `-O0`/`-O2` `-Z ub-checks=yes` bypass vs. `direct_mut_deref_control` `rc = -6` vs. `Miri` `rc = 1`, `RemoveUninitDrops` `5 -> 0` vs. `[]` on plain crate). |
| `support/mir_excerpts/` (10 `.mir` files) | Sanitized verbatim before/after MIR dumps for `core::ptr::drop_glue::<PackedNoImplDrop>`, `core::ptr::drop_glue::<PackedWithImplDrop>`, `partial_move_and_dynamic_drop_flag` (`ElaborateDrops` and `AddMovesForPackedDrops`), and `const_extract_both` (`RemoveUninitDrops`). |
| `support/PackedDropsCheckPackedRefAndElaborateDropsSoundness.lean` | Standalone pure Lean `v4.34.1` formalization (`1,742` lines, `59` user `theorem`s, `52` `noncomputable def`s, `19` inductive/structure types). |
| `support/AuditPackedDropsLean.lean` | Lean 4 metaprogram walking every constant in the compiled module environment to verify `0` `_unsafe_rec`, `0` non-`.safe` defs, `0` axioms/opaque/quot, and `[propext, Quot.sound]` axiom confinement, plus `#print axioms` on all 7 flagship theorems. |
| `support/check_lean.py` & `support/lean_check_receipt.json` | Automated token scanner, synchronous kernel compiler driver, and audit runner; receipt records **`passed: true`**, `0` errors, `0` warnings, `0` forbidden tokens, `0` audit violations, `axioms_used: ["propext"]`. |
| `support/verify_pins.py` & `support/pin_receipt.json` | Live GitHub API commit-SHA and raw-file HTTP status verifier; receipt records **`passed: true`** across `6/6` commits and `30/30` file status checks. |

## Revalidation

The cheapest reliable checks to test whether these findings still hold on a newer `rustc`, `Miri`, `rust-lang/reference`, or `joshlf/anneal` revision are four narrow, automated commands runnable directly from this package directory:

1. **Rerun the live `rustc` + `Miri` differential probe** (takes ~5–15 s with a warm Miri sysroot; tests all 12 runtime, MIR-dump, `E0793`/`E0509`/`E0277`/`E0588`, `RemoveUninitDrops`, and `drop_in_place` `-Z ub-checks=yes` vs. `Miri` checks in one invocation):
   ```console
   python3 support/probe_packed_drops_and_elaborate_drops.py --out /tmp/probe_reval.json
   ```
   - **What a failure signals:**
     - If `raw_drop_ub_checks_bypassed` turns `false` (and `raw_drop_in_place.ub_checks_rc != 0`), upstream `rustc` has closed the `core::ptr::drop_in_place` `-Z ub-checks=yes` blind spot (for example, by adding `assert_unsafe_precondition!(check_language_ub, ...)` in `library/core/src/ptr/mod.rs`, lifting the `is_sized` guard in `check_pointers.rs`, or running `CheckAlignment` after `Inline`).
     - If `remove_uninit_drops_const_runs_only_with_feature` fails because `plain_non_const_remove_uninit_drops_dumps` becomes non-empty or the feature stabilizes, `const_precise_live_drops` gating in `post_drop_elaboration.rs` / `lib.rs` has changed.
     - If MIR dump numbering shifts (`2-2-004` / `2-2-007`), inspect `compiler/rustc_mir_transform/src/lib.rs` to verify whether `AddMovesForPackedDrops` still runs strictly after `ElaborateDrops`.

2. **Re-verify the Lean `v4.34.1` kernel proof and purity audit** (takes ~8 s total):
   ```console
   python3 support/check_lean.py --lean lean --out /tmp/lean_reval.json
   ```
   Confirm `"passed": true`, `0` errors/warnings, `0` forbidden tokens, `0` audit violations (in particular `0` `_unsafe_rec` constants), and `"axioms_used"` confined to `["propext"]` (or `["propext", "Quot.sound"]`).

3. **Diff the five determining upstream `rust-lang/rust` source regions** against `ce66487ebbd7541212d22d01c39a808057d69f1f` before generalizing to a newer compiler:
   - `compiler/rustc_mir_transform/src/lib.rs` (`run_analysis_to_runtime_passes`, `run_runtime_lowering_passes`, `run_optimization_passes`)
   - `compiler/rustc_mir_transform/src/check_packed_ref.rs` and `compiler/rustc_const_eval/src/util/alignment.rs`
   - `compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs` and `compiler/rustc_mir_transform/src/shim.rs` (`make_shim`, `build_drop_shim`)
   - `compiler/rustc_mir_transform/src/check_pointers.rs` and `library/core/src/ptr/mod.rs` (`drop_in_place`)
   - `compiler/rustc_mir_transform/src/remove_uninit_drops.rs`, `compiler/rustc_mir_transform/src/elaborate_drops.rs`, and `compiler/rustc_const_eval/src/check_consts/post_drop_elaboration.rs`

4. **Re-check upstream GitHub pins and Anneal `Trusted.*` admission status:**
   ```console
   python3 support/verify_pins.py --out /tmp/pins_reval.json
   ```
   And inspect `trusted/lean/Trusted/MirAst.lean` (`TerminatorKind`, `MirTy`) and `trusted/lean/Trusted/MirSemantics.lean` (`evalRvalue`, `evalStatement`) in `joshlf/anneal` to check whether `TerminatorKind::Drop`, packed structs, or `.ref`/`.addressOf` have moved out of `.unsupported`.
