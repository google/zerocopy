# Rustc Analysis-to-Runtime MIR Lowering: CleanupPostBorrowck, False Edges, PlaceMention, and AbortUnwindingCalls

## Summary

Between `MirPhase::Analysis(AnalysisPhase::Initial)` and `MirPhase::Runtime(RuntimePhase::PostCleanup)`, `rustc` executes `run_analysis_to_runtime_passes` (`compiler/rustc_mir_transform/src/lib.rs:572-602`) to erase borrow-checker scaffolding, elaborate drops, enforce unwinding boundaries, and prune unreachable cleanup blocks:

1. **False-edge lowering lives in `CleanupPostBorrowck`, not a separate `remove_false_edges.rs` module.** Neither `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` nor `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973` contains `compiler/rustc_mir_transform/src/remove_false_edges.rs` (HTTP 404 in both revisions). `CleanupPostBorrowck` (`compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:24-91`) rewrites every `TerminatorKind::FalseEdge { real_target, .. }` and `TerminatorKind::FalseUnwind { real_target, .. }` to `Goto { target: real_target }` (calling `invalidate_cfg_cache()` if any terminator changed), while `SimplifyCfg::RemoveFalseEdges` (`compiler/rustc_mir_transform/src/simplify.rs:51,67`) is a `SimplifyCfg` pass variant invoked only when `const_precise_live_drops` triggers pre-drop checking (`lib.rs:581-593`).
2. **What `CleanupPostBorrowck` erases vs. preserves.** `CleanupPostBorrowck` replaces `AscribeUserType(..)`, `Assign((_, Rvalue::Ref(_, BorrowKind::Fake(_), _)))`, analysis-only `Coverage` markers (`CoverageKind::{BlockMarker, SpanMarker}` in `14210df0e2`; generalized via `kind.is_removed_after_analysis()` to `CoverageKind::{Point, BlockMarker}` in `c7d5ba59d8`), `FakeRead(..)`, and `BackwardIncompatibleDropHint { .. }` with `StatementKind::Nop`; lowers `PointerCoercion::{ArrayToPointer, MutToConstPointer}` to `CastKind::PtrToPtr`; and clears `body.user_type_annotations.raw` and every local's `decl.user_ty`. It does **not** erase `CoverageKind::VirtualCounter`, and it does **not** erase `StatementKind::PlaceMention(..)`.
3. **Validator enforcement lags doc comments across `Analysis(PostCleanup)` -> `Runtime(Initial)`.** Although the doc comment on `AnalysisPhase::PostCleanup` (`compiler/rustc_middle/src/mir/syntax.rs:102-116`) states that `FalseEdge`, `FalseUnwind`, `FakeRead`, `AscribeUserType`, fake borrows, analysis coverage markers, and array/mut-to-const pointer coercions are disallowed starting in `AnalysisPhase::PostCleanup`, `Validator` (`compiler/rustc_mir_transform/src/validate.rs:297-327,454-473,1139-1145,1296-1327`) enforces `CoverageKind` removal and pointer coercion lowering at `Analysis(PostCleanup)`, while deferring `AscribeUserType`, `FakeRead`, `BorrowKind::Fake`, `FalseEdge`, and `FalseUnwind` checks until `body.phase >= MirPhase::Runtime(RuntimePhase::Initial)`. `run_runtime_lowering_passes` runs `pm::run_passes_no_validate` (`lib.rs:649`), so full post-lowering validation runs only after `Runtime(Initial)` cleanup (`run_runtime_cleanup_passes`, `lib.rs:660-666`) or later passes.
4. **`FakeRead` erasure requires borrow-checker validity; `PlaceMention` is removed later by `RemovePlaceMention` unless `-Z mir-preserve-ub=yes`.** In Miri (`compiler/rustc_const_eval/src/interpret/step.rs:110-120`), `FakeRead` is an operational no-op only because borrow checking rejects uninitialized scrutinees (`E0381`) and match-guard mutations (`E0510`) statically; bypassing borrowck (e.g., via raw pointers or uninitialized unions) turns invalidated values into UB at actual value loads or unreachable arms rather than at `FakeRead`. Meanwhile, `PlaceMention(place)` evaluates place addressability/dereferences (`eval_place`) without loading the pointee value, and `RemovePlaceMention` (`compiler/rustc_mir_transform/src/remove_place_mention.rs:7-27`) deletes both `PlaceMention` and `Nop` only when `!mir_preserve_ub`.
5. **`AbortUnwindingCalls` enforces panic-strategy and FFI ABI unwinding boundaries inside `run_runtime_lowering_passes`.** Using `layout::fn_can_unwind(tcx, fn_def_id, abi)` (`compiler/rustc_middle/src/ty/layout.rs:1236-1280`), `AbortUnwindingCalls` (`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:26-144`) rewrites `UnwindResume` in every block (`Unreachable` if `!target_supports_unwinding`, else `UnwindTerminate(UnwindTerminateReason::Abi)` if `!body_can_unwind`), overwrites non-cleanup unwind edges of non-unwinding calls/drops/asserts/asm (`!call_can_unwind || !target_supports_unwinding`) with `UnwindAction::Unreachable`, rewrites `UnwindAction::Continue` to `UnwindAction::Terminate(UnwindTerminateReason::Abi)` on potentially unwinding calls inside `!body_can_unwind` functions (retaining `Cleanup(bb)` so local destructors still execute before aborting at the pad's `UnwindTerminate(Abi)`), and immediately runs `super::simplify::remove_dead_blocks(body)` (`L138`) to reclaim orphaned cleanup blocks.
6. **Mechanization and empirical confirmation.** Every invariant above is verified empirically (`21/21` checks passing on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` across native `-C panic={unwind,abort}`, `-C instrument-coverage`, `-Z mir-preserve-ub=yes`, `#[custom_mir]`, borrowck diagnostics, and Miri) and mechanized in pure axiom-minimal Lean `v4.34.1` (`support/CleanupPostBorrowckAndAbortCalls.lean`: `505` theorems, `371` axiom-free and remaining using only `propext`, `0` violations, `0` `._unsafe_rec`, `0` forbidden tokens, plus `5` `rfl` counterexamples).

## Applicability

These findings apply to the pinned compiler, specification, verification, and proof-assistant subjects recorded in `REPORT.json`:

- **Primary compiler & interpreter subject (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`):** All empirical MIR dumps, Miri executions, borrowck tests, and native `extern "C"` abort execution ran directly on this toolchain.
- **Upstream evolution delta (`rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`):** Directly diffed against `14210df0e2` across `cleanup_post_borrowck.rs`, `abort_unwinding_calls.rs`, `remove_place_mention.rs`, `remove_noop_landing_pads.rs`, `validate.rs`, `simplify.rs`, `coverage.rs`, and `lib.rs`. Behavioral rules below hold across both revisions, with exact source-level refactoring differences (`MirPass::is_required`/`is_enabled` -> `MirPass::policy(&PassCtx)`, `TerminatorKind::Goto { target }` -> `TerminatorKind::goto(target)`, `CoverageKind::{BlockMarker, SpanMarker}` -> `CoverageKind::is_removed_after_analysis()`, and `fn_sig().abi()` -> `fn_sig_abi()`) explicitly isolated in Findings.
- **Normative specification (`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`):** `src/panic.md` (`r[panic.strategy]`, `r[panic.unwind.ffi]`) and `src/items/external-blocks.md` specify source-level panic strategy (`-C panic=abort|unwind`) and FFI unwinding UB (`extern "C"` vs `extern "C-unwind"`).
- **Downstream MIR verifier (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** `Trusted.MirAst` and `Trusted.MirSemantics` model `Runtime(PostCleanup)` MIR (where `FakeRead`, `AscribeUserType`, `PlaceMention`, `FalseEdge`, and `FalseUnwind` are treated as absent or `.unsupported`, and `UnwindAction` governs unwinding behavior).
- **Proof assistant (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, Lean `v4.34.1`):** Standalone kernel-checked mechanization in `support/CleanupPostBorrowckAndAbortCalls.lean` using only Lean `Init` (`propext` only).

Scope conditions: results apply to function-like bodies (`tcx.def_kind(def_id).is_fn_like() == true`) lowered through `run_analysis_to_runtime_passes`. Non-function bodies (such as standalone constants stripped by trivial const handling or skipped by `AbortUnwindingCalls` at `abort_unwinding_calls.rs:33-35`), Wasm targets lacking `exception-handling`, and runtime optimizations in `run_optimization_passes` are distinguished explicitly below and under **Boundaries**.

## Findings

### 1. Pipeline Position and Exact `MirPhase` Transitions

```text
Basis: source (compiler/rustc_mir_transform/src/lib.rs, mod.rs, simplify.rs, deref_separator.rs) + execution
```

`rustc` transitions a `Body` from `Built` -> `Analysis(Initial)` (at the end of `mir_promoted`, `lib.rs:473`) -> `Analysis(PostCleanup)` -> `Runtime(Initial)` -> `Runtime(PostCleanup)` -> `Runtime(Optimized)` (`lib.rs:565-673,770`; `MirPhase::name()` in `compiler/rustc_middle/src/mir/mod.rs:92-112`):

1. **`run_analysis_cleanup_passes` (`lib.rs:607-623`) -> `MirPhase::Analysis(AnalysisPhase::PostCleanup)`:**
   Runs five passes sequentially under `pm::run_passes(..., Some(MirPhase::Analysis(AnalysisPhase::PostCleanup)), Allowed)`:
   - `ImpossiblePredicates`
   - `CleanupPostBorrowck` (`compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs`)
   - `RemoveNoopLandingPads` (`compiler/rustc_mir_transform/src/remove_noop_landing_pads.rs`, enabled only when `sess.panic_strategy().unwinds()`)
   - `SimplifyCfg::PostAnalysis` (`compiler/rustc_mir_transform/src/simplify.rs:53`)
   - `Derefer` (`compiler/rustc_mir_transform/src/deref_separator.rs`)
2. **Conditional `const_precise_live_drops` pre-pass (`lib.rs:581-593`):**
   If `check_consts::post_drop_elaboration::checking_enabled(...)`, runs `[RemoveUninitDrops, SimplifyCfg::RemoveFalseEdges, Lint(CheckLiveDrops)]` with `None` phase change. Notice there is **no** standalone `remove_false_edges.rs` file (`HTTP 404` on both `14210df0e2` and `c7d5ba59d8`).
3. **`run_runtime_lowering_passes` (`lib.rs:626-650`) -> `MirPhase::Runtime(RuntimePhase::Initial)`:**
   Executes via `pm::run_passes_no_validate` (`lib.rs:649`): `CriticalCallEdges`, `PostAnalysisNormalize`, `Subtyper`, `ElaborateDrops`, `Lint(CheckDropRecursion)`, **`AbortUnwindingCalls`**, `AddMovesForPackedDrops`, `EraseDerefTemps`, `ElaborateBoxDerefs`, `StateTransform`, `Lint(KnownPanicsLint)`.
4. **`run_runtime_cleanup_passes` (`lib.rs:653-673`) -> `MirPhase::Runtime(RuntimePhase::PostCleanup)`:**
   Executes `LowerIntrinsics`, **`RemovePlaceMention`**, `SimplifyCfg::PreOptimizations`, transitions to `Runtime(PostCleanup)`, and clears `decl.local_info = ClearCrossCrate::Clear`.
5. **Post-lowering validator gap between `syntax.rs` docs and `validate.rs`:**
   Per `compiler/rustc_mir_transform/src/validate.rs:297-327,454-473,1139-1145,1296-1327`:
   - Checked at `body.phase >= MirPhase::Analysis(AnalysisPhase::PostCleanup)`: `CoverageKind::{BlockMarker, SpanMarker}` (`is_removed_after_analysis()` in `c7d5ba59d8`) and `CastKind::PointerCoercion(PointerCoercion::{MutToConstPointer, ArrayToPointer}, _)`.
   - Deferred until `body.phase >= MirPhase::Runtime(RuntimePhase::Initial)`: `AscribeUserType`, `FakeRead`, `Rvalue::Ref(_, BorrowKind::Fake(_), _)`, `FalseEdge`, `FalseUnwind`, `SetDiscriminant` (`< Runtime(Initial)`), and `CoroutineDrop`.
   - Deferred until `body.phase > MirPhase::Runtime(RuntimePhase::Initial)` (`validate.rs:48`): `!self.can_unwind` checks on `UnwindAction::Continue` (`L261`) and `TerminatorKind::UnwindResume` (`L496`).
   - `run_runtime_lowering_passes` uses `pm::run_passes_no_validate` (`lib.rs:649`), so `Runtime(Initial)` itself is not validated on phase transition (`pm::run_passes` vs `pm::run_passes_no_validate`). Downstream MIR consumers such as `joshlf/anneal`'s `Trusted.MirAst` (`trusted/lean/Trusted/MirAst.lean:52-57,654-662`) ingest `Runtime(PostCleanup)` MIR after both `AbortUnwindingCalls` and `RemovePlaceMention` (or post-`SimplifyCfg`) have run.

### 2. What `CleanupPostBorrowck` Erases, Lowers, and Preserves

```text
Basis: source (cleanup_post_borrowck.rs, remove_place_mention.rs, coverage.rs) + execution (probe_results.json)
```

In `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:26-86` (`14210df0e2`):

| MIR construct | Action in `CleanupPostBorrowck` | Action in `RemovePlaceMention` | Empirical specimen measurement (`rustc 1.98.0-nightly`) |
| :--- | :--- | :--- | :--- |
| `StatementKind::FakeRead(..)` | `statement.make_nop(true)` | `Nop` removed | `specimen_match_guard`: `5 -> 0` (`nop: 0 -> 7` immediately after pass); `specimen_ascribe_and_ptr_coercions`: `8 -> 0` |
| `Rvalue::Ref(_, BorrowKind::Fake(_), _)` | `statement.make_nop(true)` | `Nop` removed | `specimen_match_guard`: `2 -> 0`; `specimen_nested_index_fake_borrow`: `ForIndex=2 -> 0` |
| `StatementKind::AscribeUserType(..)` | `statement.make_nop(true)` | `Nop` removed | `specimen_ascribe_and_ptr_coercions`: `8 -> 0` (`nop: 0 -> 16`) |
| `StatementKind::BackwardIncompatibleDropHint` | `statement.make_nop(true)` | `Nop` removed | Rewritten to `Nop` alongside above (`L41-42`) |
| `StatementKind::Coverage(BlockMarker / SpanMarker)` | `make_nop(true)` (`is_removed_after_analysis()` in `c7d5ba59d8`: `Point` and `BlockMarker`) | `Nop` removed | Coverage markers absent by `after_cleanup_post_borrowck` (`0 -> 0`) |
| `CoverageKind::VirtualCounter { .. }` | **Preserved** (`coverage.rs:126`: returns `false` under `c7d5ba59d8`) | **Preserved** | With `-C instrument-coverage`, `specimen_match_guard` retains `10 -> 10` virtual counters through `Runtime(PostCleanup)` |
| `PointerCoercion::{ArrayToPointer, MutToConstPointer}` | Rewritten in-place to `CastKind::PtrToPtr` (`L44-60`) | Preserved | `specimen_ascribe_and_ptr_coercions`: `(array_to_ptr=1, mut_to_const=1, ptr_to_ptr=0) -> (0, 0, 2)` |
| `TerminatorKind::FalseEdge { real_target, .. }` | Rewritten to `TerminatorKind::Goto { target: real_target }` | Preserved | `specimen_match_guard`: `3 -> 0` |
| `TerminatorKind::FalseUnwind { real_target, .. }` | Rewritten to `TerminatorKind::Goto { target: real_target }` | Preserved | `specimen_loop_false_unwind`: `1 -> 0` |
| `StatementKind::PlaceMention(..)` | **Preserved** | Stripped iff `!mir_preserve_ub` | `specimen_match_guard`: `3 -> 3` in `Analysis(PostCleanup)`, `3 -> 0` at default `Runtime(PostCleanup)`, `3 -> 3` with `-Z mir-preserve-ub=yes` |
| `body.user_type_annotations` & `local_decls[*].user_ty` | `.raw.clear()` and `= None` (`L81-85`) | Unchanged | Cleared unconditionally at pass exit |

Notice also that `SimplifyCfg::PostAnalysis` merges/strips the `Nop` instructions produced by `CleanupPostBorrowck` before leaving `run_analysis_cleanup_passes` (in `probe_results.json`, `specimen_match_guard` has `nop=7` at `after_cleanup_post_borrowck` and `nop=0` at `analysis_post_cleanup`). Under `-Z mir-preserve-ub=yes`, `RemovePlaceMention` is skipped (`remove_place_mention.rs:10-12`), keeping `place_mention=3` (`specimen_match_guard`) and `place_mention=1` (`specimen_place_mention_only`, `specimen_wildcard_match_place_mention`, `specimen_ascribe_and_ptr_coercions`) all the way through `Runtime(PostCleanup)`.

### 3. `FakeRead` vs. `PlaceMention` Operational Semantics and Miri Measurements

```text
Basis: source (step.rs, syntax.rs) + execution (borrowck + Miri in probe_results.json)
```

In `compiler/rustc_middle/src/mir/syntax.rs:513-620`, `FakeRead(FakeReadCause, Place)` exists so borrowck checks that variables/matched places are initialized (`ForMatchedPlace`, `ForLet`) and prevents match guards from mutating outer match places (`ForMatchGuard`, `ForGuardBinding`, backed by shallow `BorrowKind::Fake` references) or nested indexing prefixes (`ForIndex`). Because borrow checking precedes `CleanupPostBorrowck`, `rustc_const_eval/src/interpret/step.rs:110-112` makes `FakeRead(..) => {}` a literal no-op, whereas `PlaceMention(place)` (`step.rs:117-119`) calls `let _ = self.eval_place(**place)?;`:

- **Safe Rust is gated at borrowck (static rejection before MIR lowering):**
  - `borrowck_empty_match_uninit_void` (`match x {}` on uninitialized `x: Void`) fails borrowck with `error[E0381]: used binding 'x' isn't initialized`.
  - `borrowck_guard_mutates_scrutinee` (mutating `x` inside `match x` guard) fails borrowck with `error[E0510]: cannot assign 'x' in match guard`.
- **Unsafe Rust / raw-pointer bypasses reveal exact dynamic semantics in Miri (`miri 0.1.0 (14210df0e 2026-05-31)`):**
  - `let _named = *p;` (value load of invalid `bool` `0x02`, `let_named_invalid_bool`): **UB (`rc=1`)** — `"constructing invalid value of type bool: encountered 0x02, but expected a boolean"`.
  - `let _ = *p;` (`place_mention_invalid_bool`, lowered to `PlaceMention`) and `match *p { _ => () }` (`wildcard_match_invalid_bool`, lowered to `PlaceMention` + eliminated `FakeRead`): **no UB (`rc=0`)** because `PlaceMention` only calls `eval_place` on `p`, never loading the `bool` value.
  - `let _ = *dangling;` (`place_mention_dangling_thin_ptr`, dereferencing aligned non-null dangling `4usize as *const bool` once without loading memory): **no UB (`rc=0`)**, because creating an un-loaded `Place` only reads the pointer local `dangling`, which is initialized!
  - `let _ = **pp;` (`place_mention_uninit_double_ptr`, double deref through uninitialized pointer pointee): **UB (`rc=1`)** — `"reading memory at alloc19[0x0..0x8], but memory is uninitialized at [0x0..0x8]"`, because evaluating the outer projection `eval_place` *must* load the inner pointer `*pp`.
  - Raw-pointer match-guard mutation (`match_guard_raw_ptr_mutation`, mutating `*p = OptBool::None` via `*mut` in a guard) and `match *p {}` on invalid `Void` (`empty_match_raw_ptr_void`): because `FakeRead` / `BorrowKind::Fake` have no dynamic checks and are erased by `CleanupPostBorrowck`, Miri only traps downstream at the invalid `bool` discriminant load (`rc=1`) or `Unreachable` terminator (`rc=1`), never at the guard mutation or `FakeRead` itself.

Therefore, erasing `FakeRead` and `BorrowKind::Fake` is **unsound in isolation** (counterexample `ce1a`, `ce1b`, `ce1c`), and **sound iff** a certificate establishes that all reachable fake-read places are initialized/valid and no execution invalidates an active shallow fake borrow before its `FakeRead`. Meanwhile, `RemovePlaceMention` is only a **refinement** for UB-free prefixes (`execStmtList_removePlaceMention_refines`): removing `PlaceMention` drops dereference-validity checks like `**pp` in `place_mention_uninit_double_ptr` unless `-Z mir-preserve-ub=yes` is active.

### 4. `AbortUnwindingCalls` Mechanics and `-C panic=abort` vs. FFI ABI Lowering

```text
Basis: normative (rust-lang/reference panic.md) + source (abort_unwinding_calls.rs, layout.rs, remove_noop_landing_pads.rs) + execution (probe_results.json)
```

By `rust-lang/reference@ad35aca481` (`src/panic.md:92-129`), unwinding across a non-unwinding FFI ABI boundary (such as calling a foreign function declared `extern "C"` that throws, or unwinding out of a Rust `extern "C"` function) or into `-fno-exceptions` non-unwinding foreign frames is undefined behavior unless prevented; under `-C panic=abort`, optimizers assume Rust frames cannot unwind. Inside `run_runtime_lowering_passes`, `AbortUnwindingCalls` enforces both rules using `layout::fn_can_unwind(tcx, fn_def_id, abi)` (`layout.rs:1236-1280`):

1. **Exact `fn_can_unwind` truth table (`layout.rs:1236-1280`):**
   - If `fn_def_id == Some(did)`:
     * `CodegenFnAttrFlags::NEVER_UNWIND` -> `false`.
     * `!tcx.sess.panic_strategy().unwinds() && !tcx.is_foreign_item(did)` -> **`false` even if the Rust function has `extern "C-unwind"` ABI!** (`layout.rs:1247-1249` explicitly overrides non-FFI `extern "C-unwind"` definitions to non-unwinding under `-C panic=abort`.)
     * `-Z panic-in-drop=abort && is_lang_item(did, LangItem::DropGlue)` -> `false`.
   - Otherwise, `ExternAbi::{C, System, Cdecl, Stdcall, Fastcall, Vectorcall, Thiscall, Aapcs, Win64, SysV64} { unwind }` returns `unwind`; Rust ABIs (`ExternAbi::Rust` / `RustCall`) return `sess.panic_strategy().unwinds()`. Note that for `ty::FnPtr(..)`, `AbortUnwindingCalls` passes **`fn_def_id = None`** (`abort_unwinding_calls.rs:94-98`), so an `extern "C-unwind" fn` pointer still has `call_can_unwind = true` even under `-C panic=abort`!
2. **Pass actions (`abort_unwinding_calls.rs:46-139`):**
   - **Target unwind support:** `target_supports_unwinding = !(tcx.sess.target.is_like_wasm && panic_strategy == Abort && !asm_target_features.contains(exception_handling))`.
   - **`UnwindResume` terminators (all blocks, even cleanup blocks):** rewritten to `Unreachable` if `!target_supports_unwinding`, else to `UnwindTerminate(UnwindTerminateReason::Abi)` if `!body_can_unwind` (`L77-83`).
   - **Unwinding edges (non-cleanup blocks only, `L85-135`):**
     * If `!call_can_unwind || !target_supports_unwinding`: `*cleanup = UnwindAction::Unreachable`.
     * Else if `!body_can_unwind && matches!(unwind, Some(UnwindAction::Continue))`: `*cleanup = UnwindAction::Terminate(UnwindTerminateReason::Abi)`.
     * Else if `!body_can_unwind && UnwindAction::Cleanup(bb)`: keeps `Cleanup(bb)`; local destructors inside `bb` still run and terminate at `bb`'s rewritten `UnwindTerminate(Abi)` (confirmed empirically by `native_extern_c_unwind_aborts_after_drop`: `Marker::drop` increments and prints before `run_rc = -6` SIGABRT!).
   - **Immediate dead-block pruning:** `super::simplify::remove_dead_blocks(body)` (`L138`) compacts away cleanup blocks whose incoming `Cleanup(bb)` edge was overwritten to `Unreachable`. Notice also that `RemoveNoopLandingPads` is **disabled** under `-C panic=abort` (`remove_noop_landing_pads.rs:15`: `sess.panic_strategy().unwinds()`), so before `AbortUnwindingCalls` under `-C panic=abort` a no-drop `extern "C"` call to a foreign `C-unwind` function or `C-unwind` fn pointer still has a 1-block `Cleanup(bb) -> UnwindResume` pad, which `AbortUnwindingCalls` turns into `Cleanup(bb) -> UnwindTerminate(Abi)` instead of `UnwindAction::Terminate(Abi)` on the `Call` itself.

Empirical verification across the 13 caller patterns under `rustc 1.98.0-nightly`:

| Caller specimen | `-C panic=unwind` (Before -> After `AbortUnwindingCalls`) | `-C panic=abort` (Before -> After `AbortUnwindingCalls`) |
| :--- | :--- | :--- |
| `caller_rust_calls_rust_with_drop` | `bb:5->5, cb:2->2, res:1->1` | `bb:5->3, cb:2->0, unreach:0->2` |
| `caller_rust_calls_rust_no_drop` | `bb:2->2, cb:0->0, cont:1->1` | `bb:3->2, cb:1->0, res:1->0, unreach:0->1` |
| `caller_extern_c_calls_rust_with_drop` | `bb:5->5, cb:2->2, term_abi:0->1` (`res:1->0`) | `bb:5->3, cb:2->0, unreach:0->2` |
| `caller_extern_c_calls_rust_no_drop` | `bb:2->2, cont:1->0, edge_abi:0->1` | `bb:3->2, cb:1->0, res:1->0, unreach:0->1` |
| `caller_extern_c_calls_foreign_c_unwind_with_drop` | `bb:5->5, cb:2->2, term_abi:0->1` (`res:1->0`) | `bb:5->5, cb:2->2, term_abi:0->1, unreach:0->1` |
| `caller_extern_c_calls_foreign_c_unwind_no_drop` | `bb:2->2, cont:1->0, edge_abi:0->1` | `bb:3->3, cb:1->1, res:1->0, term_abi:0->1` |
| `caller_extern_c_unwind_calls_foreign_c_unwind_with_drop` | `bb:5->5, cb:2->2, res:1->1` | `bb:5->5, cb:2->2, term_abi:0->1, unreach:0->1` |
| `caller_extern_c_calls_foreign_c_nounwind_with_drop` | `bb:5->4, cb:2->1, term_abi:0->1, unreach:0->1` | `bb:5->3, cb:2->0, unreach:0->2` |
| `caller_rust_calls_fnptr_c_unwind_with_drop` | `bb:5->5, cb:2->2, res:1->1` | `bb:5->5, cb:2->2, term_abi:0->1, unreach:0->1` |
| `caller_rust_calls_fnptr_c_unwind_no_drop` | `bb:2->2, cb:0->0, cont:1->1` | `bb:3->3, cb:1->1, res:1->0, term_abi:0->1` |
| `caller_rust_calls_rust_defined_c_unwind_with_drop` | `bb:5->5, cb:2->2, res:1->1` | **`bb:5->3, cb:2->0, unreach:0->2`** (`FnDef` non-FFI!) |
| `caller_rust_inline_asm_may_unwind_with_drop` | `bb:5->5, cb:2->2, res:1->1` | `bb:5->5, cb:2->2, term_abi:0->1, unreach:0->1` (`asm!`, `drop` unreachable) |
| `caller_rust_assert_overflow_with_drop` | `bb:5->5, cb:2->2, res:1->1` | `bb:5->3, cb:2->0, unreach:0->2` |

In `custom_extern_c_unwind_continue` (`#[custom_mir(dialect = "analysis", phase = "post-cleanup")]` `extern "C"` body calling a local `extern "C-unwind"` fn with `UnwindContinue()` directly, skipping `RemoveNoopLandingPads`), `-C panic=unwind` lowers the `Continue` edge directly to `Terminate(Abi)` (`edge_abi: 0 -> 1`), whereas `-C panic=abort` sees a non-foreign `FnDef` (`fn_can_unwind == false`) and lowers it to `UnwindAction::Unreachable` (`unreach: 0 -> 1`).

### 5. Kernel-Checked Lean `v4.34.1` Mechanization and Sharpness Counterexamples

```text
Basis: source (support/CleanupPostBorrowckAndAbortCalls.lean) + execution (support/check_lean.py, lean_check_receipt.json)
```

`support/CleanupPostBorrowckAndAbortCalls.lean` (`4,589` lines, Lean `v4.34.1` `Init` only, `0` forbidden tokens, `505` theorems / `371` axiom-free / max axiom `{propext}`, `0` `._unsafe_rec`, `0` violations) formalizes four operational modes (`.analysisGuarded`, `.analysisUnguarded`, `.analysisPostCleanup`, `.runtime`) and proves:

- **`cleanupPostBorrowck_syntax_valid` & `cleanupPostBorrowck_unguarded_exact_equiv`:** `cleanupPostBorrowck` clears all forbidden analysis statements (`FakeRead`, `AssignFakeBorrow`, `AscribeUserType`, `BackwardIncompatibleDropHint`, removed coverage markers), lowers `FalseEdge`/`FalseUnwind` to `Goto`, coerces `ArrayToPointer`/`MutToConstPointer` to `PtrToPtr`, clears `hasUserTypeAnnots`, and is an exact step-by-step equality against `.analysisPostCleanup` when `FakeRead` checks are elided.
- **`cleanupPostBorrowck_certified_equiv` & `cleanupPostBorrowck_certified_iff`:** Assuming `bodyUsesFakeCleanly isFake b = true` and `CertifiedForFakeRead cfg fuel b stAn oracle 0`, runtime execution after `cleanupPostBorrowck` matches `.analysisGuarded` identically (`outcome`, `trace`, non-fake `store`), and `CertifiedForFakeRead` is **iff** equivalent to avoiding `ubFakeReadViolation` under `.analysisGuarded`.
- **`placeMention_ignores_invalid_pointee`, `assignCopy_rejects_invalid_pointee`, `placeMention_checks_pointer_local`, & `execStmtList_removePlaceMention_refines`:** Formalizes Miri's `PlaceMention` vs. value-load split and proves that `RemovePlaceMention` (`stmts.filter keepNonPlaceMention`) preserves exact `store`, `trace`, and `bb` whenever execution without removal does not fault.
- **`abortRewriteOnly_nonpanicking_equiv` & `abortRewriteOnly_exact_analysis_equiv`:** Under `OracleRespectsAbi cfg b st oracle 0 fuel` and `wfBodyForAbort`, `abortRewriteOnly` matches `.analysisPostCleanup` (where non-unwinding ABI violations deterministically abort rather than faulting as UB in runtime MIR) and matches non-panicking `.runtime` executions across any configuration pair `(cfg, cfg0)`.
- **`compactReachableBody_bisim`, `unreachable_blocks_dropped_by_compaction`, `abortUnwindingCalls_exact_analysis_equiv`, `abortUnwindingCalls_nonpanicking_equiv`, & `full_analysis_to_runtime_lowering_sound`:** Proves exact bounded-BFS reachability closure (`iterReach blocks.length`), dead-block index-remapping bisimulation from block `0`, dropping of all unreachable cleanup blocks, and full end-to-end soundness of `abortUnwindingCalls cfg (cleanupPostBorrowck b)` (`validRuntimeSyntax`, `outcome`, `trace`, non-fake `store`) against `.analysisGuarded`.
- **Five concrete sharpness counterexamples (`rfl`):**
  1. **`ce1a_uncertified_fakeread_uninit_scrutinee`:** On an uninitialized slot `0` with `FakeRead(ForMatchedPlace, slot 0)`, `cleanupPostBorrowck` returns `.returned 42` instead of trapping `.fault .ubFakeReadViolation`.
  2. **`ce1b_uncertified_fakeread_invalid_discriminant`:** On an out-of-range discriminant `enumVal 2 2` with `FakeRead(ForMatchedPlace, slot 0)`, `cleanupPostBorrowck` returns `.returned 7` while `.analysisGuarded` traps `.fault .ubFakeReadViolation`.
  3. **`ce1c_guard_mutation_bypasses_erased_fake_borrow`:** Mutating the outer place between `AssignFakeBorrow` and `FakeRead(ForMatchGuard)` returns `.returned 1` after `cleanupPostBorrowck` instead of `.fault .ubFakeReadViolation`.
  4. **`ce2_mutant_cleanup_to_continue_causes_abi_ub`:** A buggy mutant pass (`mutantCleanupToContinue`) rewriting `Cleanup` / `UnwindResume` inside a `!bodyCanUnwind` function to `Continue` (instead of `Terminate(Abi)`) causes `.fault .ubUnwindPastNounwindAbi` under `.runtime`, whereas `abortUnwindingCalls` deterministically yields `.aborted .abi`.
  5. **`ce3_nounwind_violation_hits_unreachable_ub`:** Violating `OracleRespectsAbi` on a non-FFI `extern "C-unwind"` call under `-C panic=abort` executes `UnwindAction::Unreachable` and yields `.fault .ubUnreachableUnwind`, whereas foreign `extern "C-unwind"` remains unwindable and routes to cleanup/`Terminate(Abi)`.

## Boundaries

- **WebAssembly `!target_supports_unwinding` execution is *not examined* empirically:** `abort_unwinding_calls.rs:46-48` was audited by direct source inspection and mechanized cleanly in Lean (`targetSupportsUnwinding = false`), showing `UnwindResume -> Unreachable` and all unwind edges -> `UnwindAction::Unreachable`, but no `wasm32` binary was compiled or executed in the local probe.
- **Inline assembly in Miri is *unsupported*:** `compiler/rustc_const_eval/src/interpret/step.rs:658-660` rejects `TerminatorKind::InlineAsm` via `throw_unsup_format!`. Behavior of `InlineAsmOptions::MAY_UNWIND` inside `AbortUnwindingCalls` was therefore verified by source inspection and `-Z dump-mir=AbortUnwindingCalls` counts (`caller_rust_inline_asm_may_unwind_with_drop`), not Miri execution.
- **Coroutine `Yield` / `CoroutineDrop` and async drop expansion (`StateTransform`) are *not examined*:** Both live in `run_runtime_lowering_passes` (`lib.rs:646`) alongside `ElaborateDrops` and `AbortUnwindingCalls`; our probe and Lean AST model synchronous `Call`, `Drop`, `Assert`, `InlineAsm`, `FalseEdge`, and `FalseUnwind` bodies only.
- **Generalizability to non-function MIR bodies (`!kind.is_fn_like()`) is *known not to apply*:** `AbortUnwindingCalls` exits immediately on `!kind.is_fn_like()` (`abort_unwinding_calls.rs:33-35`) to avoid query cycles with `tcx.type_of`, and `Validate` skips `!kind.is_fn_like()` unwind checks (`validate.rs:51-52`); const items never get unwind actions rewritten by `AbortUnwindingCalls`.
- **Generalizability to `Runtime(Optimized)` MIR is *known not to apply* without considering later passes:** `run_optimization_passes` (`lib.rs:690-772`) runs `CheckAlignment`/`CheckNull`/`CheckEnums`, `RemoveStorageMarkers`, inlining, `SimplifyCfg::Final`, and `o1(RemoveNoopLandingPads)`, which further transform CFG topology and `UnwindAction` edges after `Runtime(PostCleanup)`.
- **Lean formalization model scope (*unknown* for arbitrary Rust type layout bugs):** `support/CleanupPostBorrowckAndAbortCalls.lean` faithfully mechanizes intra-procedural MIR statement/terminator semantics, `fn_can_unwind`, fake borrows, dead-block compaction, and `PlaceMention`, rather than full Stacked Borrows / Tree Borrows aliasing or linker-level cross-crate panic-strategy incompatibility checks.

## Evidence

| Artifact / Pin | Details |
| :--- | :--- |
| **`rust-lang/rust` (`rustc 1.98.0-nightly`)** | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (verified via GitHub API in `support/pin_receipt.json`). Inspected: `cleanup_post_borrowck.rs:1-91`, `abort_unwinding_calls.rs:1-144`, `remove_place_mention.rs:1-27`, `remove_noop_landing_pads.rs:1-143`, `lib.rs:564-800`, `simplify.rs:1-95`, `deref_separator.rs:1-100`, `pass_manager.rs:310-375`, `validate.rs:1-95,245-345,345-425,450-565,1135-1165,1292-1335`, `compiler/rustc_middle/src/mir/mod.rs:75-120`, `syntax.rs:75-140,513-620`, `layout.rs:1236-1280`, `step.rs:105-160,560-660`. Confirmed absent (`HTTP 404`): `compiler/rustc_mir_transform/src/remove_false_edges.rs`. |
| **`rust-lang/rust` (HEAD snapshot at audit)** | `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (verified via GitHub API). Diffed against `14210df0e2`: `PassPolicy`/`PassCtx`, `TerminatorKind::goto`, `CoverageKind::is_removed_after_analysis()` (`compiler/rustc_middle/src/mir/coverage.rs:119-129`), `fn_sig_abi`; `remove_false_edges.rs` also absent (`HTTP 404`). |
| **`rust-lang/reference`** | `ad35aca481751a06afeb23820a672b0f3b11a476` (verified via GitHub API): `src/panic.md:1-150`, `src/items/external-blocks.md:1-100`. |
| **`joshlf/anneal`** | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (verified via GitHub API): `trusted/lean/Trusted/MirAst.lean:1-95,625-720,740-835`, `trusted/lean/Trusted/MirSemantics.lean:1515-1600`. |
| **`leanprover/lean4`** | `5045d0056413266e57c625dcd7c365b10e377c52` (`Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`). |
| **Empirical probe & specimens (observed 2026-11-21)** | Runner: `support/probe_cleanup_post_borrowck_and_abort.py`. Specimens: `support/specimens/mir_pipeline_specimens.rs`, `support/specimens/custom_mir_specimens.rs`, `support/specimens/miri_place_and_guard_ub.rs`, `support/specimens/borrowck_and_native_abort.rs`. Recorded outputs: `support/probe_output/probe_results.json`, `support/probe_output/probe_summary.md`, and curated MIR dumps under `support/probe_output/mir/` (`21/21` checks passed). |
| **Lean `v4.34.1` formalization & receipts (observed 2026-11-21)** | Formalization: `support/CleanupPostBorrowckAndAbortCalls.lean` (SHA-256 `06fffdfdcd655c461548e725e4b534ada81f7863b7196f9bd612d76f18a021eb`, `202,947` bytes, `4,589` lines, `20` public theorems, `505` audited theorems, `371` axiom-free, max axiom `{propext}`, `0` `._unsafe_rec`, `0` violations, `0` forbidden tokens; compile `21.601s` / `767,304 kB`; audit `5.347s` / `1,584,692 kB`). Checker & audit: `support/CleanupPostBorrowckAudit.lean`, `support/check_lean.py`, `support/lean_check_receipt.json`. |
| **Pin verification receipt** | `support/verify_pins.py`, `support/pin_receipt.json` (all 5 commit pins and all 25 cited file statuses including two `HTTP 404` checks verified). |

## Revalidation

To test whether a newer `rustc` toolchain, upstream `rust-lang/rust` commit, or local Lean toolchain preserves every claim above:

1. **Re-run the empirical `rustc` + Miri probe against the target toolchain:**
   ```bash
   python3 support/probe_cleanup_post_borrowck_and_abort.py --out support/probe_output
   ```
   Confirm `21/21` checks pass, including `-Z mir-preserve-ub=yes`, `CoverageKind::VirtualCounter` retention, `FnDef` vs. `FnPtr` unwindability under `-C panic=abort`, `#[custom_mir]` lowering, Miri's `PlaceMention` vs. value-load distinction, and native `extern "C"` destructor cleanup before SIGABRT.
2. **Re-run strict Lean kernel compilation, token scan, and constant audit:**
   ```bash
   python3 support/check_lean.py --lean lean --out support/lean_check_receipt.json
   ```
   Verify `passed: true`, zero compiler errors/warnings, zero forbidden tokens, `violations: 0`, and axioms restricted to `[propext]` / `[]`.
3. **Inspect upstream diffs on the four pass-defining files:**
   Diff `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs`, `abort_unwinding_calls.rs`, `remove_place_mention.rs`, `validate.rs`, and `lib.rs` (`run_analysis_to_runtime_passes`) plus `compiler/rustc_middle/src/ty/layout.rs` (`fn_can_unwind`) between `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` and the new target commit, and re-run:
   ```bash
   python3 support/verify_pins.py --out support/pin_receipt.json
   ```
