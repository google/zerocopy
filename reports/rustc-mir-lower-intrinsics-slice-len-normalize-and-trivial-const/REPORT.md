# `rustc` MIR Intrinsic Lowering, Slice-Length Desugaring, Post-Analysis Normalization, and Trivial-Const Fast-Path Semantics

## Summary

Four `rustc_mir_transform` components govern how high-level intrinsic calls, `<[T]>::len` calls, opaque/associated types, and constant items cross the `MirPhase::Built` $\to$ `MirPhase::Analysis(PostCleanup)` $\to$ `MirPhase::Runtime(PostCleanup)` $\to$ `MirPhase::Runtime(Optimized)` boundaries in `rust-lang/rust` (audited across `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` [`1.98.0-nightly`], `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` [`1.102.0-nightly`], and `137d1d49458b73b7b85d2c1599d8730886d65e47` [HEAD]):

1. **`LowerIntrinsics` (`compiler/rustc_mir_transform/src/lower_intrinsics.rs`, `PassPolicy::Required` in `run_runtime_cleanup_passes`, `lib.rs:686`):** Dispatches across **14 explicit match arms covering 29 distinct `sym::*` intrinsics** (plus a wildcard `_ => {}` pass-through leaving all other intrinsics such as `ctpop`, `volatile_load`, and `const_eval_select` as `TerminatorKind::Call` through `Runtime(PostCleanup)`). Between `14210df0e27c` (`1.98.0-nightly`) and `137d1d49458b` (HEAD), both `sym::copy_nonoverlapping` (`lines 76-88`) and `sym::assume` (`lines 102-114`) gained an explicit `*destination = Rvalue::Use(Operand::zero_sized_constant(unit), WithRetag::Yes)` assignment after `StatementKind::Intrinsic(...)`; in `14210df0e27c`, both arms omitted the destination unit store entirely.
2. **Uninhabited `read_via_copy` and `transmute`/`transmute_unchecked` preserve pre-`Unreachable` UB ordering:** When a lowered call targets an uninhabited return type (`target == None`), both `read_via_copy` (`lower_intrinsics.rs:191-205`) and `transmute`/`transmute_unchecked` (`lines 299-313`) append the `Assign` statement (`_0 = copy (*_2)` or `_0 = move _2 as Void (Transmute)`) **before** setting `terminator.kind = TerminatorKind::Unreachable`. Live Miri (`0.1.0` on `14210df0e27c`) confirms a strict three-tier UB precedence: on an 8-byte uninhabited struct `UninhabitedSized(u64, Void)` behind a null pointer, memory-access UB (`"memory access failed: attempting to access 8 bytes, but got null pointer"`) fires first; on a valid 8-byte pointer or 0-byte `Void` (where 0-byte access short-circuits), validity UB (`"constructing invalid value of type ..."`) fires next; neither ever collapses prematurely to `"entering unreachable code"`. Dropping the pre-`Unreachable` statement misclassifies both fault kinds as `unreachableUb`.
3. **Four distinct `LowerIntrinsics` place/operand ICE and broken-MIR failure modes (including a formally discovered upstream invariant gap in `slice_get_unchecked`):**
   - Passing an indirect place (`*pp`) via `#[custom_mir(dialect = "runtime", phase = "initial")]` (bypassing `Derefer`) to `slice_get_unchecked` triggers `assert!(!place.is_indirect())` (`lower_intrinsics.rs:254` at `137d1d49458b`, `line 230` at `14210df0e27c`, `rc = 101`).
   - Passing a constant literal index in **ordinary nightly Rust** (`core::intrinsics::slice_get_unchecked(sp, 2)`, without `#[custom_mir]`) triggers an immediate `Option::unwrap()` ICE at `lower_intrinsics.rs:259` (`line 235:56` at `14210df0e27c`, `rc = 101`) because `index.node.place()` is `None` for `Operand::Constant`.
   - **Upstream precondition gap discovered during Lean formalization and confirmed live on `rustc 1.98.0-nightly`:** `assert!(!place.is_indirect())` in `slice_get_unchecked` is strictly weaker than the post-`Derefer` MIR invariant (`Deref` allowed only as projection index `0`). Passing a non-indirect field projection `pair.0` (`[Field(0)]`, where `is_indirect() == false`) in `#[custom_mir(dialect = "runtime", phase = "initial")]` **bypasses `assert!(!place.is_indirect())`**, emits `_0 = &raw const (*(_1.0: *const [u32]))[_2]` (`[Field(0), Deref, Index(_2)]`), and crashes MIR validation (`validate.rs:82:25`, `rc = 101`: `"place (*(_1.0: *const [u32]))[_2] has deref as a later projection"`). The exact necessary and sufficient precondition is `place.as_local().is_some()` (`place.projection.is_empty()`), which `read_via_copy` (`lines 179-188`) already enforces (`span_bug!("Only passing a local is supported")`).
   - `discriminant_value` (`lines 216-217`) performs `tcx.mk_place_deref(arg)` with **no** `as_local()` or `!is_indirect()` guard at all, silently emitting invalid double-deref `_0 = discriminant((*(*_1)))` that fails downstream in `validate.rs:82:25` (`rc = 101`).
4. **Wide-pointer `aggregate_raw_ptr` $\leftrightarrow$ `UnOp::PtrMetadata` bijection is conditioned on `InterpCx::deref_pointer`:** `aggregate_raw_ptr` lowers to `Rvalue::Aggregate(AggregateKind::RawPtr(pointee, mutability), [data, meta])` (`lower_intrinsics.rs:315-341`), and `ptr_metadata` lowers to `Rvalue::UnaryOp(UnOp::PtrMetadata, ptr)` (`lines 342-358`). Crucially, `InterpCx::unary_op` (`compiler/rustc_const_eval/src/interpret/operator.rs:499-512`) invokes `self.deref_pointer(val)?` **before** extracting `MemPlaceMeta`. Consequently, `PtrMetadata` is an exact round-trip inverse of `aggregate_raw_ptr` for all sized and slice raw pointers (`*const [T]` / `*mut [T]`, even with null or dangling data addresses, per `place.rs:527-529`), but faults with validity UB on dangling/null/misaligned `&[T]`/`&mut [T]` references (confirmed live in Miri: `rc = 1`) and on `*const dyn Trait` pointers carrying invalid vtables (`place.rs:523-526`).
5. **`LowerSliceLenCalls` (`compiler/rustc_mir_transform/src/lower_slice_len.rs`) runs *after* `Runtime(PostCleanup)` and drops cleanup unwind edges without invalidating the CFG cache:** Scheduled at the front of `run_optimization_passes` (`lib.rs:718`, after `CheckAlignment`/`CheckNull`/`CheckEnums` and before `Inline`) with `PassPolicy::optional(ctx.mir_opt_level() >= 1)`, `LowerSliceLenCalls` rewrites normal 1-argument non-diverging calls whose `func.const_fn_def()` equals `#[lang = "slice_len_fn"]` (`core::slice::<impl [T]>::len`) into `Assign(dst, UnaryOp(UnOp::PtrMetadata, arg)); Goto(bb)`. It is disabled at `-Zmir-opt-level=0`, skips indirect `FnPtr` calls (`let f: fn(&[u32]) -> usize = <[u32]>::len; f(s)`), and still fires on `&mut [u32]` after mutation (via the shared reborrow temporary). Because `<[T]>::len` is not marked `#[rustc_nounwind]`, calls with live `Drop` guards carry `unwind: bb_cleanup` entering `LowerSliceLenCalls`; rewriting `Call -> [return: bb1, unwind: bb3]` to `Goto(bb1)` via `body.basic_blocks.as_mut_preserves_cfg()` (`lower_slice_len.rs:24-25`, commented `"The one successor remains unchanged, so no need to invalidate"`) **orphans `bb3 (cleanup)` and mutates CFG successors without invalidating cached predecessors/dominators**.
6. **`PostAnalysisNormalize` (`post_analysis_normalize.rs`) reveals opaques and strips `OpaqueCast`, while `CleanupPostBorrowck` clears `user_type_annotations`:** Neither `14210df0e27c` nor `137d1d49458b` asserts `user_type_annotations.is_empty()` inside `post_analysis_normalize.rs`; instead, `CleanupPostBorrowck` (`cleanup_post_borrowck.rs:79-83`, `lib.rs:645`) clears `body.user_type_annotations` and every `decl.user_ty` *prior* to `PostAnalysisNormalize` (`lib.rs:655`). `PostAnalysisNormalize` (`PassPolicy::Required`) runs immediately after entering `MirPhase::Analysis(AnalysisPhase::PostCleanup)` (`body.typing_env(tcx)` $\to$ `TypingEnv::post_analysis`), normalizes `ConstOperand`, `Ty`, and (added at `137d1d49458b`) `GenericArgs` via `try_normalize_erasing_regions` with `ty::set_aliases_to_non_rigid` (silently preserving unnormalizable impossible where-clauses), and strips `ProjectionElem::OpaqueCast` when `!tcx.next_trait_solver_globally()` (verified live: `copy ((_1 as Pair).1: u64)` $\to$ `copy (_1.1: u64)`).
7. **`trivial_const` (`trivial_const.rs` + `lib.rs:403-408`) skips 48 MIR passes and requires `has_impossible_clauses` and opaque-type guards for CTFE soundness:** Constants (`DefKind::Const`, `DefKind::AssocConst`, and at `137d1d49458b` `DefKind::AnonConst` excluding `AnonConstKind::NonTypeSystemInline`) whose raw `mir_built` body has exactly 1 basic block, 1 statement `_0 = Operand::Constant(Const::Val | recursive empty-args Const::Unevaluated)`, and a `Return` terminator bypass all `mir_built` lints, `mir_promoted`, `mir_drops_elaborated_and_const_checked`, and `mir_for_ctfe` (confirmed live: `1` MIR dump file for `TRIV_A`, `TRIV_B`, and `TRIV_C_CHAIN2` vs. `49` dump files for `NON_TRIV_ARITH = 40 + 2`, `NON_TRIV_GENERIC_REF = GenHolder::<u8>::ASSOC_TRIV`, and `NON_TRIV_OPAQUE_DEF`). Live execution on `1.98.0-nightly` (`14210df0e27c`, which pre-dates `has_impossible_clauses`) directly reproduces the soundness bug fixed in `137d1d49458b` (`trivial_const.rs:65-67`): `IMPOSSIBLE_CLAUSE_TRIV: usize = 7 where String: Copy` compiles cleanly (`rc = 0`, `1` dump, evaluating to `7`), whereas `IMPOSSIBLE_CLAUSE_NON_TRIV: usize = 3 + 4 where String: Copy` runs all `49` passes, is rewritten to `bb0: { unreachable; }` by `ImpossiblePredicates`, and aborts CTFE with `error[E0080]: entering unreachable code` (`rc = 1`).
8. **Anneal TCB capture seam (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Every unmodeled construct emitted by these four passes fails closed in `Trusted.MirAst` and `Trusted.MirSemantics`: `Operand::RuntimeChecks`, `BinOp::Cmp`, `StatementKind::Intrinsic`, `Rvalue::Cast(Transmute)`, `AggregateKind::RawPtr`, `ProjectionElem::Index`, and `Rvalue::Use(_, WithRetag::Yes)` over reference/pointer types all reject or lower to `.unsupported`, `UnOp::PtrMetadata` is present in `MirAst.UnOp` (`line 446`) but returns `.error .unsupported` in `evalUnOp` (`MirSemantics.lean:1193`), `TerminatorKind::Unreachable` steps to `.fault .undefined` (`MirSemantics.lean:1551-1552`), and `trivial_const` items have no `mir_drops_elaborated_and_const_checked` body because `mir_promoted` and `mir_for_ctfe` both `debug_assert!(!tcx.is_trivial_const(def))`.

All formal claims are kernel-checked in standalone Lean `v4.34.1` ([`support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean`](support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean): `2,310` lines, `45` user-declared theorems / `411` namespace theorems, `0` warnings under `-DwarningAsError=true`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`), and all empirical compiler and Miri claims are reproduced by [`support/probe_lower_intrinsics_slice_len_and_trivial_const.py`](support/probe_lower_intrinsics_slice_len_and_trivial_const.py) with captured outputs in [`support/probe_results.json`](support/probe_results.json).

## Applicability

This report governs the exact pinned upstream revisions and toolchains recorded in `REPORT.json`, with their cross-subject relationships defined as follows:

| Subject | Repository / Artifact | Immutable Revision | Date / Version | Role in Investigation |
| :--- | :--- | :--- | :--- | :--- |
| **`rust-lang/rust` HEAD** | `rust-lang/rust` | `137d1d49458b73b7b85d2c1599d8730886d65e47` | `2026-11-22T20:28:26Z` | Primary source authority for `lower_intrinsics.rs`, `lower_slice_len.rs`, `post_analysis_normalize.rs`, `trivial_const.rs`, `impossible_clauses.rs`, `cleanup_post_borrowck.rs`, `deref_separator.rs`, `validate.rs`, `lib.rs`, `rustc_middle/src/mir/{mod,syntax,statement}.rs`, `rustc_const_eval/src/{const_eval/eval_queries,interpret/{step,place,operator,cast,intrinsics}}.rs`, and `library/core/src/{intrinsics/mod,slice/mod}.rs`. |
| **`rust-lang/rust` intermediate pin** | `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `1.102.0-nightly` (`2026-11-11`) | Intermediate source pin diffed against `137d1d49458b` to isolate recent changes (`Intrinsic::Rustc(name)` wrapper in `lower_intrinsics.rs`; `body.typing_env(tcx)` refactor in `post_analysis_normalize.rs`; identical `lower_slice_len.rs`, `trivial_const.rs`, and `impossible_clauses.rs`). |
| **`rust-lang/rust` & Miri live toolchain** | `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `1.98.0-nightly` (`2026-05-31`), `miri 0.1.0`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu` | Executed live `rustc` and `cargo miri` toolchain **and** source-audited baseline exposing four concrete cross-version changes relative to `137d1d49458b`. |
| **The Rust Reference** | `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | `2026-11-17T20:49:56Z` | Normative specification for UB (`r[undefined.pointer-access]`, `r[undefined.place-projection]`, `r[undefined.invalid]`, `r[undefined.dangling]`, `r[undefined.validity.const-provenance]`), pointer bit validity, and slice/constant rules. |
| **Anneal TCB** | `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `2026-11-19T21:39:21Z` | Target MIR capture and verification seam (`trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`), whose capture driver pins `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` and whose MIR semantics cites `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`. |
| **Lean 4 kernel** | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | `v4.34.1` (`2026-09-24`) | Standalone proof assistant kernel checking `support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean` (`x86_64-unknown-linux-gnu`, `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`). |

### Shared vs. Version-Specific Behavior

- **Shared across `14210df0e27c`, `3ef0c22cdb86`, and `137d1d49458b`:**
  - All 14 explicit `LowerIntrinsics` match arms and all 29 lowered `sym::*` intrinsic names, plus the wildcard `_ => {}` pass-through.
  - Statement-before-`Unreachable` lowering on uninhabited `read_via_copy` and `transmute`/`transmute_unchecked`.
  - All four `LowerIntrinsics` precondition failure modes (`!place.is_indirect()` ICE on `*pp`, `index.node.place().unwrap()` ICE on constant literal index, non-indirect `pair.0` field-projection bypass leading to `validate.rs` broken MIR, `read_via_copy` non-local `span_bug!`, and `discriminant_value` unguarded `mk_place_deref`).
  - `LowerSliceLenCalls` gating (`mir_opt_level >= 1`, `CallSource::Normal`, `target: Some(bb)`, `func.const_fn_def() == slice_len_fn`), placement in `run_optimization_passes` before `Inline`, and the `as_mut_preserves_cfg()` unwind-edge cache bug.
  - `CleanupPostBorrowck` clearing `user_type_annotations` and `decl.user_ty` prior to `PostAnalysisNormalize`, and `PostAnalysisNormalize` stripping `ProjectionElem::OpaqueCast` when `!next_trait_solver_globally()`.
  - `trivial_const` syntactic shape (1 BB, 1 statement `_0 = Const::Val | empty-args recursive UnevaluatedConst`, `Return`) and `!opaque_types_defined_by.is_empty()` / `body.has_opaque_types()` guards.
- **Specific to `14210df0e27c` (`1.98.0-nightly`) vs. `3ef0c22cdb86` and `137d1d49458b`:**
  - **`copy_nonoverlapping` & `assume` unit destination store:** Absent in `14210df0e27c` (emits only `StatementKind::Intrinsic` + `Goto`); present in both `3ef0c22cdb86` and `137d1d49458b` (appends `*destination = Rvalue::Use(Operand::zero_sized_constant(unit), WithRetag::Yes)` before `Goto`).
  - **`trivial_const` `has_impossible_clauses` and `AnonConstKind::NonTypeSystemInline` guards:** Absent in `14210df0e27c` (allowing `IMPOSSIBLE_CLAUSE_TRIV` to bypass `ImpossiblePredicates` and succeed while `IMPOSSIBLE_CLAUSE_NON_TRIV` fails with `E0080`); present in both `3ef0c22cdb86` and `137d1d49458b` (`trivial_const.rs:57, 65-67`, with the pass renamed from `ImpossiblePredicates` to `ImpossibleClauses`).
  - **`PostAnalysisNormalize` `visit_args` & `set_aliases_to_non_rigid`:** `14210df0e27c` uses `Unnormalized::new_wip(...)` and does not override `visit_args`; `3ef0c22cdb86` and `137d1d49458b` use `ty::set_aliases_to_non_rigid` and override `visit_args` (`post_analysis_normalize.rs:90-97`).
  - **Pass policy API:** `14210df0e27c` uses `is_enabled` / `is_required`; `3ef0c22cdb86` and `137d1d49458b` use `PassPolicy::Required` / `PassPolicy::optional(...)`.
- **Specific to `137d1d49458b` vs. `3ef0c22cdb86`:**
  - `lower_intrinsics.rs:20` matches `Intrinsic::Rustc(name) = intrinsic.name` (replacing direct `match intrinsic.name`).
  - `post_analysis_normalize.rs:15` calls `body.typing_env(tcx)` instead of manually calling `ty::TypingEnv::post_analysis(tcx, body.source.def_id())`, enabled because `run_analysis_cleanup_passes` (`lib.rs:651`) has already transitioned `body.phase` to `MirPhase::Analysis(AnalysisPhase::PostCleanup)` (`mir/mod.rs:429-431`).

Live compiler and Miri probes executed on `1.98.0-nightly` (`14210df0e27c`, Edition 2024, `x86_64-unknown-linux-gnu`) directly establish execution behavior at `14210df0e27c`; statements about behavior added between `14210df0e27c` and `137d1d49458b` rest on direct source inspection of `137d1d49458b` and `3ef0c22cdb86` plus mechanized Lean proof, not live execution of a `137d1d49458b` binary.

## Findings

### Finding 1: Exact Pipeline Placement Across `rustc_mir_transform` and Companion Corpus Erratum

`Basis: source, execution`

Direct inspection of `compiler/rustc_mir_transform/src/lib.rs` (`lines 394-857` at `137d1d49458b`) establishes the exact `MirPhase` placement of all four audited components:

```text
mir_built (lib.rs:395-433)  [MirPhase::Built]
  ├─ build_mir_inner_impl(def)
  ├─ FAST EXIT: if trivial_const::trivial_const(tcx, def, || &body).is_some()
  │     └─► alloc_steal_mir(body); dump_mir_for_phase_change; return body
  │         (SKIPS all built lints, SimplifyCfg::Initial, mir_promoted,
  │          mir_borrowck, mir_drops_elaborated_and_const_checked, mir_for_ctfe!)
  └─ else: LintAndRemoveUninhabited, MIR lints, SimplifyCfg::Initial, SanityCheck
        │
        ▼
mir_promoted (lib.rs:436-498)  [debug_assert!(!tcx.is_trivial_const(def))]
  └─ PromoteTemps, SimplifyCfg::PromoteConsts, InstrumentCoverage
     └─► MirPhase::Analysis(AnalysisPhase::Initial)
        │
        ▼
mir_drops_elaborated_and_const_checked (lib.rs:546-604)
  ├─ mir_borrowck, check_liveness, steal mir_promoted, check_transmutes, check_well_formed
  └─ run_analysis_to_runtime_passes (lib.rs:608-637):
       ├─ 1. run_analysis_cleanup_passes (lib.rs:642-656)
       │      ├─ ImpossibleClauses          (lib.rs:644; PassPolicy::optional(true))
       │      ├─ CleanupPostBorrowck        (lib.rs:645; PassPolicy::Required — clears user_type_annotations)
       │      ├─ RemoveNoopLandingPads      (lib.rs:646)
       │      ├─ SimplifyCfg::PostAnalysis  (lib.rs:647)
       │      ├─ Derefer                    (lib.rs:648; PassPolicy::Required — splits nested Derefs)
       │      ├─ PHASE CHANGE ──► MirPhase::Analysis(AnalysisPhase::PostCleanup) (lib.rs:651)
       │      └─ PostAnalysisNormalize      (lib.rs:655; PassPolicy::Required — reveals opaques, strips OpaqueCast)
       ├─ 2. run_runtime_lowering_passes (lib.rs:659-681)
       │      └─ CriticalCallEdges, Subtyper, ElaborateDrops, CheckDropRecursion,
       │         AbortUnwindingCalls, AddMovesForPackedDrops, EraseDerefTemps,
       │         ElaborateBoxDerefs, StateTransform, KnownPanicsLint
       │         ──► MirPhase::Runtime(RuntimePhase::Initial)
       └─ 3. run_runtime_cleanup_passes (lib.rs:684-698)
              ├─ LowerIntrinsics            (lib.rs:686; PassPolicy::Required — 14 arms / 29 syms)
              ├─ RemovePlaceMention         (lib.rs:687; optional(!mir_preserve_ub))
              ├─ SimplifyCfg::PreOptimizations (lib.rs:688)
              ├─ PHASE CHANGE ──► MirPhase::Runtime(RuntimePhase::PostCleanup) (lib.rs:691)  ◄── CAPTURE SEAM
              └─ clear decl.local_info      (lib.rs:695-697)
        │
        ├──► mir_for_ctfe (lib.rs:501-541) [debug_assert!(!tcx.is_trivial_const(def_id))]
        │      └─ remap_mir_for_const_eval_select(Const), CtfeLimit
        │
        └──► optimized_mir / inner_optimized_mir (lib.rs:792-838)
               ├─ MentionedItems (lib.rs:824)
               ├─ Early exit if single empty bb0 ending in Unreachable (lib.rs:829-833)
               └─ run_optimization_passes (lib.rs:700-789):
                    ├─ CheckAlignment, CheckNull, CheckEnums (lib.rs:711-713)
                    ├─ LowerSliceLenCalls (lib.rs:718; PassPolicy::optional(mir_opt_level >= 1))
                    ├─ InstSimplify::BeforeInline (lib.rs:721)
                    ├─ ForceInline, Inline (lib.rs:723-725)
                    └─ ... ──► MirPhase::Runtime(RuntimePhase::Optimized)
```

#### Cross-Revision Evolution of the Four Pass Files

| File (`compiler/rustc_mir_transform/src/`) | `14210df0e27c` (`1.98.0-nightly`) | `3ef0c22cdb86` (`1.102.0-nightly`) | `137d1d49458b` (HEAD) | Material Semantic / Structural Changes |
| :--- | :---: | :---: | :---: | :--- |
| `lower_intrinsics.rs` | `344` LOC (`is_required()`) | `368` LOC (`PassPolicy::Required`) | `369` LOC (`PassPolicy::Required`) | `14210df0` $\to$ `3ef0c22c`: adds unit `*destination` store to `copy_nonoverlapping` & `assume`, `generic_args.no_bound_vars().unwrap()`, `Operand::zero_sized_constant`. `3ef0c22c` $\to$ `137d1d49`: wraps name in `Intrinsic::Rustc(name)`. |
| `lower_slice_len.rs` | `67` LOC (`is_enabled`, `is_required`) | `65` LOC (`PassPolicy::optional`) | `65` LOC (identical to `3ef0c22c`) | Refactor to `PassPolicy::optional(ctx.mir_opt_level() >= 1)` and `TerminatorKind::goto(*bb)`; logic and `as_mut_preserves_cfg()` unchanged. |
| `post_analysis_normalize.rs` | `86` LOC | `100` LOC | `98` LOC | `14210df0` $\to$ `3ef0c22c`: replaces `Unnormalized::new_wip` with `ty::set_aliases_to_non_rigid`, adds `visit_args`. `3ef0c22c` $\to$ `137d1d49`: replaces `TypingEnv::post_analysis(...)` with `body.typing_env(tcx)`. |
| `trivial_const.rs` | `117` LOC | `124` LOC | `124` LOC (identical to `3ef0c22c`) | `14210df0` $\to$ `3ef0c22c`: adds `has_impossible_clauses` soundness guard (`lines 65-67`) and excludes `AnonConstKind::NonTypeSystemInline` (`line 57`). |
| `impossible_clauses.rs` | `impossible_predicates.rs` | `121` LOC (`ImpossibleClauses`) | `121` LOC (identical to `3ef0c22c`) | Renamed pass and exported `has_impossible_clauses` for reuse by `trivial_const.rs`; also detects structurally unsized `Sized` clauses (`dyn Trait<T>: Sized`, `lines 38-84`). |

#### Erratum to Companion Corpus Report `rustc-mir-phases-reachability-and-postcleanup-lowering`

In the companion corpus report `rustc-mir-phases-reachability-and-postcleanup-lowering`, Stage 4 of the summary pipeline table inaccurately listed `LowerSliceLenCalls`, `CheckNull`, `CheckAlignment`, `CheckEnums`, `Derefer`, and `LowerIntrinsics` inside `run_runtime_lowering_passes` (and stated `Derefer` ran conditionally when `!mir_preserve_ub`). Primary source across `14210df0e27c`, `3ef0c22cdb86`, and `137d1d49458b` establishes:
1. `Derefer` (`lib.rs:648`) and `PostAnalysisNormalize` (`lib.rs:655`) are required passes in `run_analysis_cleanup_passes` (not `run_runtime_lowering_passes`, and `Derefer` is unconditional).
2. `LowerIntrinsics` (`lib.rs:686`) is the first required pass in `run_runtime_cleanup_passes`, immediately preceding `RemovePlaceMention` and `SimplifyCfg::PreOptimizations` before `MirPhase::Runtime(RuntimePhase::PostCleanup)`.
3. `CheckAlignment`, `CheckNull`, `CheckEnums` (`lib.rs:711-713`), and `LowerSliceLenCalls` (`lib.rs:718`) execute inside `run_optimization_passes` **after** `MirPhase::Runtime(RuntimePhase::PostCleanup)`. Consequently, any consumer capturing at `Runtime(PostCleanup)` sees `LowerIntrinsics` already applied, but still sees `<[T]>::len` as an unlowered `TerminatorKind::Call`.

---

### Finding 2: Complete 14-Arm (29-Intrinsic) `LowerIntrinsics` Architecture and Destination-Store Evolution

`Basis: source, execution, derived`

In `compiler/rustc_mir_transform/src/lower_intrinsics.rs` (`lines 11-369` at `137d1d49458b`; `lines 11-344` at `14210df0e27c`), `LowerIntrinsics::run_pass` scans every basic block's terminator for:

```rust
// compiler/rustc_mir_transform/src/lower_intrinsics.rs:16-22 (137d1d49458b)
if let TerminatorKind::Call { func, args, destination, target, .. } = &mut terminator.kind
    && let ty::FnDef(def_id, generic_args) = *func.ty(local_decls, tcx).kind()
    && let Some(intrinsic) = tcx.intrinsic(def_id)
    && let Intrinsic::Rustc(name) = intrinsic.name
{
    let generic_args = generic_args.no_bound_vars().unwrap();
    match name { ... }
}
```

Crucially, `LowerIntrinsics` fires **only** on direct `ty::FnDef` intrinsic calls (`Intrinsic::Rustc(name)`), never on function pointers (and Rust forbids reifying intrinsic `FnDef`s into function pointers) and never on `Intrinsic::Llvm(...)` or non-intrinsic callees. Its `match name` statement contains **14 explicit lowered arms covering 29 distinct `sym::*` intrinsics**, plus a trailing `_ => {}` wildcard arm (these 14 arms collapse into 12 semantic lowering families only if one merges the two `NonDivergingIntrinsic` arms `copy_nonoverlapping`+`assume` and the two wide-pointer arms `aggregate_raw_ptr`+`ptr_metadata`).

| Arm # | `137d1d49` Lines | `14210df0` Lines | Matched `sym::*` Intrinsics (Count) | Argument / Target Preconditions | Emitted MIR Statements | Emitted Terminator |
| :---: | :---: | :---: | :--- | :--- | :--- | :--- |
| **1** | `24-26` | `22-24` | `unreachable` (1) | Any `target` (ignored) | None | `TerminatorKind::Unreachable` |
| **2** | `27-43` | `25-41` | `ub_checks`, `overflow_checks`, `contract_checks` (3) | `target.unwrap()` | `*dst = Use(Operand::RuntimeChecks(op), WithRetag::Yes)` | `Goto(target)` |
| **3** | `44-60` | `42-62` | `forget` (1) | `target.unwrap()` (note: `args` ignored!) | `*dst = Use(Operand::zero_sized_constant(unit), WithRetag::Yes)` | `Goto(target)` |
| **4** | `61-90` | `63-88` | `copy_nonoverlapping` (1) | `target.unwrap()`, `take_array::<3>(args)` | `Intrinsic(CopyNonOverlapping { src, dst, count })`; **at `137d1d49` ALSO `*dst = Use(unit, WithRetag::Yes)`** | `Goto(target)` |
| **5** | `91-116` | `89-105` | `assume` (1) | `target.unwrap()`, `take_array::<1>(args)` | `Intrinsic(Assume(arg))`; **at `137d1d49` ALSO `*dst = Use(unit, WithRetag::Yes)`** | `Goto(target)` |
| **6** | `117-154` | `106-143` | `wrapping_{add,sub,mul}`, `three_way_compare`, `unchecked_{add,sub,mul,div,rem,shl,shr}` (11) | `target.unwrap()`, `take_array::<2>(args)` | `*dst = BinaryOp(Add\|Sub\|Mul\|Cmp\|AddUnchecked\|SubUnchecked\|MulUnchecked\|Div\|Rem\|ShlUnchecked\|ShrUnchecked, (lhs, rhs))` | `Goto(target)` |
| **7** | `155-174` | `144-163` | `add_with_overflow`, `sub_with_overflow`, `mul_with_overflow` (3) | `target.unwrap()`, `take_array::<2>(args)` | `*dst = BinaryOp({Add,Sub,Mul}WithOverflow, (lhs, rhs))` | `Goto(target)` |
| **8** | `175-206` | `164-195` | `read_via_copy` (1) | `take_array::<1>(args)`, `arg.place().as_local()` (`span_bug!` otherwise); `target` may be `None`! | `*dst = Use(Copy(*local), WithRetag::Yes)` | `None => Unreachable`, `Some(t) => Goto(t)` |
| **9** | `208-226` | `197-215` | `discriminant_value` (1) | `target.unwrap()`, `take_array::<1>(args)`, `arg.place().unwrap()` (**NO `!is_indirect()` or `as_local()` guard!**) | `*dst = Rvalue::Discriminant(mk_place_deref(arg))` | `Goto(target)` |
| **10** | `227-243` | `216-232` | `offset` (1) | `target.unwrap()`, `take_array::<2>(args)` | `*dst = BinaryOp(BinOp::Offset, (ptr, delta))` | `Goto(target)` |
| **11** | `244-289` | `233-278` | `slice_get_unchecked` (1) | `target.unwrap()`, `take_array::<2>(args)`, `ptrish.place().unwrap()`, **`assert!(!place.is_indirect())`**, **`index.place().unwrap().as_local().unwrap()`** | `*dst = RawPtr(Const\|Mut, (*ptr)[idx])` or `Ref(r, Shared\|Mut{Default}, (*ptr)[idx])` by `generic_args.type_at(0)` | `Goto(target)` |
| **12** | `290-314` | `279-303` | `transmute`, `transmute_unchecked` (2) | `take_array::<1>(args)`; `target` may be `None`! | `*dst = Cast(CastKind::Transmute, arg, dst_ty)` | `Some(t) => Goto(t)`, `None => Unreachable` |
| **13** | `315-341` | `304-330` | `aggregate_raw_ptr` (1) | `target.unwrap()`, `take_array::<2>(args)`, `generic_args.type_at(0)` is `ty::RawPtr` | `*dst = Aggregate(AggregateKind::RawPtr(pointee_ty, mutability), [data, meta])` | `Goto(target)` |
| **14** | `342-358` | `331-347` | `ptr_metadata` (1) | `target.unwrap()`, `take_array::<1>(args)` | `*dst = UnaryOp(UnOp::PtrMetadata, ptr)` | `Goto(target)` |
| **Wildcard** | `359` | `348` | All other intrinsics (`ctpop`, `volatile_load`, `copy`, `size_of`, `const_eval_select`, `atomic_*`, etc.) | Unchanged | None | Remains `TerminatorKind::Call` |

#### Three Subtle Implementation Details Verified in Source and Execution

1. **`copy_nonoverlapping` and `assume` Destination Unit-Write Fix (`14210df0e2` $\to$ `137d1d4945`):**
   Live `1.98.0-nightly` (`14210df0e27c`) MIR dumps from `support/probe_results.json` confirm the pre-fix behavior verbatim:
   ```text
   // probe_assume after LowerIntrinsics (rustc 1.98.0-nightly, 14210df0e27c)
   bb0: {
       StorageLive(_2);
       _2 = copy _1;
       assume(move _2);
       goto -> bb1;
   }
   bb1: {
       StorageDead(_2);
       return;
   }
   ```
   Notice `_0` (of type `()`) is **never assigned** in `14210df0e27c` (and the exact same omission appears in `probe_copy_nonoverlapping`). While reading an uninitialized `()` local is a no-op under zero-sized copy semantics in Miri, any MIR consumer enforcing strict initialization tracking on `_0` — or any `#[custom_mir]` / raw-pointer destination `*ptr = assume(b)` where writing to `*destination` carries a place-validity side effect — diverges from `TerminatorKind::Call` semantics. In `3ef0c22cdb86` and `137d1d49458b` (`lower_intrinsics.rs:76-88, 102-114`), both arms now append `*destination = Rvalue::Use(Operand::zero_sized_constant(tcx.types.unit, span), WithRetag::Yes)` immediately after `StatementKind::Intrinsic(...)`. Lean theorem `assume_unit_dest_fix_head_vs_legacy198` formalizes this exact divergence (`stSrc.locals 0 = .unit`, `stHead.locals 0 = .unit`, `stLeg.locals 0 = .uninit`).
2. **`forget` Discards Its Argument Operand Without Moving or Dropping:**
   In `lower_intrinsics.rs:44-60`, `sym::forget` ignores `args` completely and emits only `_0 = const (); goto -> bb1;`. In ordinary Rust (`probe_forget(x: u64)`), MIR building has already copied/moved `x` into a staging temporary `_2 = copy _1` prior to the call terminator, and `ElaborateDrops` did not schedule a drop on `_2` because the call took ownership of `_2` by value; `LowerIntrinsics` then replaces the call with `_0 = const ()`, leaving `_2` to end at `StorageDead(_2)` without invoking `Drop::drop`.
3. **`write_via_move` and Unlowered Intrinsics:**
   As documented in `lower_intrinsics.rs:207` (`// write_via_move is already lowered during MIR building`), `core::intrinsics::write_via_move` never reaches `LowerIntrinsics`. Conversely, `probe_unlowered_ctpop` confirms that intrinsics falling through to line `359` (`_ => {}`) survive `LowerIntrinsics` intact as `_0 = std::intrinsics::ctpop::<u32>(move _2) -> [return: bb1, unwind unreachable];`. Note also that `probe_binops` confirms `unchecked_div` and `unchecked_rem` map to ordinary `BinOp::Div` and `BinOp::Rem` (`lines 140-141`), because MIR `BinOp::Div`/`BinOp::Rem` already carry UB-on-zero and UB-on-`MIN/-1` semantics (safe Rust `/` and `%` emit explicit `TerminatorKind::Assert` guards during MIR building prior to executing `BinOp::Div`/`BinOp::Rem`).

---

### Finding 3: Uninhabited `read_via_copy` and `transmute`/`transmute_unchecked` Statement-Before-`Unreachable` UB Ordering

`Basis: normative, source, execution, derived`

The Rust Reference (`rust-lang/reference@c9cc32825b03`, `src/behavior-considered-undefined.md`, `r[undefined.pointer-access]` and `r[undefined.invalid]`) specifies two independent sources of UB when reading or transmuting an uninhabited type:
- `r[undefined.pointer-access]`: *"Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer."*
- `r[undefined.invalid]`: *"Producing an invalid value. 'Producing' a value happens any time a value is assigned to or read from a place, passed to a function/primitive operation or returned from a function/primitive operation."*

In `lower_intrinsics.rs`, both `sym::read_via_copy` (`lines 191-205`) and `sym::transmute | sym::transmute_unchecked` (`lines 299-313`) explicitly accommodate `target == None` (which MIR building emits whenever a function call returns an uninhabited type such as `enum Void {}` or `struct UninhabitedSized(u64, Void)`):

```rust
// compiler/rustc_mir_transform/src/lower_intrinsics.rs:191-205 (137d1d49458b)
block.statements.push(Statement::new(
    terminator.source_info,
    StatementKind::Assign(Box::new((
        *destination,
        Rvalue::Use(Operand::Copy(derefed_place), WithRetag::Yes),
    ))),
));
terminator.kind = match *target {
    None => {
        // No target means this read something uninhabited,
        // so it must be unreachable.
        TerminatorKind::Unreachable
    }
    Some(target) => TerminatorKind::goto(target),
}
```

And symmetrically for `transmute | transmute_unchecked` (`lines 299-313`):

```rust
// Always emit the cast, even if we transmute to an uninhabited type,
// because that lets CTFE and codegen generate better error messages
// when such a transmute actually ends up reachable.
block.statements.push(Statement::new(
    terminator.source_info,
    StatementKind::Assign(Box::new((
        *destination,
        Rvalue::Cast(CastKind::Transmute, arg.node, dst_ty),
    ))),
));
if let Some(target) = *target {
    terminator.kind = TerminatorKind::goto(target);
} else {
    terminator.kind = TerminatorKind::Unreachable;
}
```

#### Empirical `rustc` MIR Dumps and Live Miri Fault-Precedence Matrix

Running `probe_lower_intrinsics_slice_len_and_trivial_const.py` on `rustc 1.98.0-nightly` + `miri 0.1.0` (`14210df0e27c`) produces exact statement-before-`unreachable` MIR for all four uninhabited specimens and distinguishes three UB layers at runtime:

| Specimen (`support/probe_results.json`) | Emitted MIR After `LowerIntrinsics` | Miri Exit Code | Exact Miri Diagnostic (`error: Undefined Behavior:`) | Firing Stage |
| :--- | :--- | :---: | :--- | :--- |
| `read_via_copy_sized_uninhabited_null` (`*const UninhabitedSized`, 8 B, `null`) | `_0 = copy (*_2);` then `unreachable;` | `1` | `memory access failed: attempting to access 8 bytes, but got null pointer` | **Stage 1: Memory access** (`check_ptr_access`, size `8 > 0`) |
| `read_via_copy_sized_uninhabited_valid` (`*const UninhabitedSized`, 8 B, valid stack `u64`) | `_0 = copy (*_2);` then `unreachable;` | `1` | `constructing invalid value of type UninhabitedSized: at .1, encountered a value of zero-variant enum Void` | **Stage 2: Type validity** (`copy_op` validation on field `.1`) |
| `read_via_copy_void_null` (`*const Void`, 0 B, `null`) | `_0 = copy (*_2);` then `unreachable;` | `1` | `constructing invalid value of type Void: encountered a value of zero-variant enum Void` | **Stage 2: Type validity** (0-byte `check_ptr_access` short-circuits, then `Void` validity fails) |
| `transmute_unit_to_void` (`transmute::<(), Void>(())`) | `_0 = move _2 as Void (Transmute);` then `unreachable;` | `1` | `constructing invalid value of type Void: encountered a value of zero-variant enum Void` | **Stage 2: Cast validity** (`cast.rs:196-216`: size check `0 == 0` passes, then `copy_op_allow_transmute` fails validity) |

Notice the crucial nuance between 0-byte `Void` and non-zero-sized uninhabited types (`UninhabitedSized(u64, Void)`):
- For 0-byte `Void`, `check_ptr_access` short-circuits zero-byte raw-pointer accesses even on `null`, so Miri proceeds directly from Stage 1 to Stage 2 (`invalidValueUb`) inside `_0 = copy (*_2)` — **still before** `TerminatorKind::Unreachable`!
- For 8-byte `UninhabitedSized`, Stage 1 (`memAccessUb`) fires immediately on `null` inside `_0 = copy (*_2)`, whereas on a valid 8-byte stack slot Stage 1 succeeds and Stage 2 (`invalidValueUb` at field `.1`) fires — **still before** `TerminatorKind::Unreachable`!
- For `transmute` / `transmute_unchecked`, `compiler/rustc_const_eval/src/interpret/cast.rs:192-218` first verifies `src.layout.size == dest.layout.size` (`sizeMismatchUb` if unequal, reachable via `transmute_unchecked`), then executes `self.copy_op_allow_transmute(src, dest)?`, which validates both source and destination types before `TerminatorKind::Unreachable` is ever reached.

In [`support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean`](support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean), Theorem `lowerIntrinsics_uninhabited_preserves_pre_ub` proves universal exact fault-kind preservation for `read_via_copy`, `transmute`, and `transmute_unchecked` when `target = none`; Theorems `lowerIntrinsics_readViaCopy_sizedUninhabited_null_is_memAccessUb` and `lowerIntrinsics_readViaCopy_void_null_is_invalidValueUb` mirror the exact Miri witnesses; and Theorem `naive_uninhabited_drop_stmt_misclassifies_ub` refutes any lowering pass that drops the assignment statement before `Unreachable` (`unreachableUb ≠ memAccessUb`).

---

### Finding 4: `slice_get_unchecked`, `read_via_copy`, and `discriminant_value` Preconditions, Live ICEs, and the `!place.is_indirect()` Invariant Gap

`Basis: source, execution, derived`

In `compiler/rustc_mir_transform/src/lower_intrinsics.rs:244-289` (`lines 220-265` at `14210df0e27c`), `sym::slice_get_unchecked` lowers calls into a place projection followed by a 4-way pointer/reference constructor selected from `ret_ty = generic_args.type_at(0)`:

```rust
// compiler/rustc_mir_transform/src/lower_intrinsics.rs:253-282 (137d1d49458b)
let place = ptrish.node.place().unwrap();
assert!(!place.is_indirect());
let updated_place = place.project_deeper(
    &[
        ProjectionElem::Deref,
        ProjectionElem::Index(
            index.node.place().unwrap().as_local().unwrap(),
        ),
    ],
    tcx,
);

let ret_ty = generic_args.type_at(0);
let rvalue = match *ret_ty.kind() {
    ty::RawPtr(_, Mutability::Not) => Rvalue::RawPtr(RawPtrKind::Const, updated_place),
    ty::RawPtr(_, Mutability::Mut) => Rvalue::RawPtr(RawPtrKind::Mut, updated_place),
    ty::Ref(region, _, Mutability::Not) => Rvalue::Ref(region, BorrowKind::Shared, updated_place),
    ty::Ref(region, _, Mutability::Mut) => Rvalue::Ref(
        region,
        BorrowKind::Mut { kind: MutBorrowKind::Default },
        updated_place,
    ),
    _ => bug!("Unknown return type {ret_ty:?}"),
};
```

Live execution of `probe_slice_get_unchecked_all4` confirms all four lowered MIR forms in a single function:
- `*const [u32]` $\to$ `_6 = &raw const (*_7)[_8];`
- `*mut [u32]` $\to$ `_9 = &raw mut (*_10)[_11];`
- `&[u32]` $\to$ `_12 = &(*_13)[_14];`
- `&mut [u32]` $\to$ `_15 = &mut (*_16)[_17];`

#### Complete Taxonomy of Precondition Violations and Live `rustc` ICEs

Why does `slice_get_unchecked` assert `!place.is_indirect()`? By `compiler/rustc_middle/src/mir/syntax.rs:117-118`, beginning in `MirPhase::Analysis(AnalysisPhase::PostCleanup)` (enforced by `Derefer` at `lib.rs:648` and checked by `validate.rs`), **`ProjectionElem::Deref` is permitted ONLY as the first projection (`index 0`) of any `Place`**. `Place::is_indirect(&self)` (`compiler/rustc_middle/src/mir/statement.rs:377-379`) delegates to `ProjectionElem::is_indirect` (`lines 263-275`), returning `true` iff `self.projection` contains `Deref` or `PhantomDeref`.

However, formalizing `sliceGetUnchecked_preserves_derefOnlyFirst_iff` in Lean 4 proved a sharper algebraic equivalence:
$$\texttt{derefOnlyFirst}(\texttt{place.project\_deeper}([\texttt{Deref}, \texttt{Index}(\text{idx})])) = \texttt{true} \iff \texttt{place.projection} = []$$
In other words, **`!place.is_indirect()` is necessary but NOT sufficient!** Any non-empty non-indirect projection prefix — such as a tuple/struct field projection `pair.0` (`[Field(0)]`, for which `is_indirect() == false`) — passes `assert!(!place.is_indirect())` yet appends `Deref` at index `1`, producing the illegal place `(*(_1.0))[_2]`.

Testing all six custom-MIR and ordinary-Rust cases live on `rustc 1.98.0-nightly` (`14210df0e27c`) confirms every failure mode:

| Probe Case (`support/probe_results.json`) | Entry Dialect / Rust Form | Argument Passed | `rc` | Exact Failure Mechanism & Location (`14210df0` / `137d1d49`) |
| :--- | :--- | :--- | :---: | :--- |
| `direct_slice_get_unchecked_control` | `#[custom_mir(dialect = "runtime", phase = "initial")]` | `slice_get_unchecked(p, idx)` (`p: *const [u32]`, plain local) | **`0`** | Cleanly lowers to `_0 = &raw const (*_1)[_2]; goto -> bb1;`. |
| `indirect_slice_get_unchecked` | `#[custom_mir(dialect = "runtime", phase = "initial")]` | `slice_get_unchecked(*pp, idx)` (`proj = [Deref]`) | **`101`** | ICE: `assertion failed: !place.is_indirect()` at `lower_intrinsics.rs:230:25` (`line 254` at `137d1d49`). |
| `const_index_slice_get_unchecked` | **Ordinary nightly Rust** (no `#[custom_mir]`!) | `slice_get_unchecked(sp, 2)` (literal `2` $\to$ `Operand::Constant`) | **`101`** | ICE: `called Option::unwrap() on a None value` at `lower_intrinsics.rs:235:56` (`line 259` at `137d1d49`: `index.node.place().unwrap().as_local().unwrap()`). |
| `field_proj_slice_get_unchecked_validate_mir` | `#[custom_mir(dialect = "runtime", phase = "initial")]` + `-Zvalidate-mir` | `slice_get_unchecked(pair.0, idx)` (`proj = [Field(0)]`, `is_indirect() == false`) | **`101`** | **Bypasses `assert!(!place.is_indirect())`!** Emits `_0 = &raw const (*(_1.0: *const [u32]))[_2];`, then ICEs in `validate.rs:82:25`: `broken MIR ... (after pass LowerIntrinsics) at bb0[0]: place (*(_1.0: *const [u32]))[_2] has deref as a later projection`. |
| `indirect_read_via_copy` | `#[custom_mir(dialect = "runtime", phase = "initial")]` | `read_via_copy(*pp)` (`proj = [Deref]`) | **`101`** | Explicit `span_bug!("Only passing a local is supported")` at `lower_intrinsics.rs:160:29` (`line 184` at `137d1d49`, guarding `place.as_local()`). |
| `indirect_discriminant_no_validate` & `_validate_mir` | `#[custom_mir(dialect = "runtime", phase = "initial")]` (with & without `-Zvalidate-mir`) | `discriminant_value(*pp)` (`proj = [Deref]`) | **`101`** | **No guard in `lower_intrinsics.rs:216-217`!** Silently emits `_0 = discriminant((*(*_1)));`, triggering `validate.rs:82:25` `broken MIR` immediately after `LowerIntrinsics` (with `-Zvalidate-mir`) or at phase change to `runtime-optimized` (without `-Zvalidate-mir`). |

**Engineering takeaway for `rustc` and custom-MIR producers:** Calling `core::intrinsics::slice_get_unchecked` with a literal constant index (`2`) crashes `rustc` even in standard Rust without `#[custom_mir]` (because `rustc_mir_build` optimizes literal operands to `Operand::Constant` rather than staging them in a local; `core::slice` avoids this only because `get_unchecked(self, index: usize)` passes a local parameter `index`). Inside `lower_intrinsics.rs`, both `slice_get_unchecked` (`line 254`) and `discriminant_value` (`line 216`) would require `place.as_local()` (matching `read_via_copy` at `line 180`) to uphold the post-`Derefer` invariant unconditionally rather than relying on `rustc_mir_build` staging or downstream MIR validation.

---

### Finding 5: Wide-Pointer Duality (`aggregate_raw_ptr` $\leftrightarrow$ `UnOp::PtrMetadata`) and `deref_pointer` Validity Boundaries

`Basis: normative, source, execution, derived`

`LowerIntrinsics` lowers `core::intrinsics::aggregate_raw_ptr` (`lower_intrinsics.rs:315-341`) and `core::intrinsics::ptr_metadata` (`lines 342-358`) into dual MIR rvalues:

```text
// probe_raw_ptr_roundtrip after LowerIntrinsics (live rustc 1.98.0-nightly)
_3 = *const [u32] from (move _4, move _5);   // Rvalue::Aggregate(AggregateKind::RawPtr([u32], Not), [_4, _5])
...
_0 = PtrMetadata(move _6);                   // Rvalue::UnaryOp(UnOp::PtrMetadata, move _6)
```

Direct inspection of `rustc_const_eval` exposes an asymmetric validity contract that naive syntactic models miss:

1. **Assembly (`AggregateKind::RawPtr`, `compiler/rustc_const_eval/src/interpret/step.rs:317-338`):** Reads the thin pointer `data` (`read_pointer`) and metadata scalar `meta` (`MemPlaceMeta::None` if `meta.layout.is_zst()`, else `MemPlaceMeta::Meta(read_scalar)`), packs `Immediate::new_pointer_with_meta(data, meta, self)`, and writes the result via `copy_op(&ptr, dest)?` (validating that the resulting raw pointer satisfies raw-pointer bit validity: initialized scalar bits, and for `dyn Trait`, valid vtable metadata). Note also `validate.rs:1120-1129`: `AggregateKind::RawPtr` is legal only in `MirPhase::Runtime(_)`, and input `data_ptr` mutability must match output raw pointer mutability.
2. **Projection (`UnOp::PtrMetadata`, `compiler/rustc_const_eval/src/interpret/operator.rs:499-513`):**
   ```rust
   ty::RawPtr(..) | ty::Ref(..) => {
       assert_eq!(un_op, PtrMetadata);
       self.deref_pointer(val)?; // validity check
       let (_, meta) = val.to_scalar_and_meta();
       interp_ok(match meta {
           MemPlaceMeta::Meta(scalar) => {
               let ty = un_op.ty(*self.tcx, val.layout.ty);
               let layout = self.layout_of(ty)?;
               ImmTy::from_scalar(scalar, layout)
           }
           MemPlaceMeta::None => {
               let unit_layout = self.layout_of(self.tcx.types.unit)?;
               ImmTy::uninit(unit_layout)
           }
       })
   }
   ```
   **Line 501 (`self.deref_pointer(val)?`) is load-bearing:** Inside `InterpCx::deref_pointer` (`compiler/rustc_const_eval/src/interpret/place.rs:468-538`):
   - **If `val` is a reference (`&T`, `&mut T`) or `Box<T>` (`lines 490-516`):** Enforces non-null (`scalar_may_be_null`), full pointee dereferenceability (`check_ptr_access` over `size_and_align_of_val`), alignment (`check_ptr_align`), and metadata validity (slice total size $\le \text{isize::MAX}$ or valid `dyn` vtable).
   - **If `val` is a raw pointer (`*const T`, `*mut T`, `lines 517-534`):**
     - For `ty::Slice(..) | ty::Str | ty::Foreign(..)` or sized pointees (`lines 527-529`): performs **zero** data-address or allocation checks (`// Nothing to check (read_immediate already ensured initialization)`).
     - For `ty::Dynamic(data, _)` (`lines 523-526`): calls `self.get_ptr_vtable_ty(vtable, Some(data))?`, faulting with UB if the vtable pointer is invalid or has the wrong principal trait!

Live Miri probes verify both sides of this boundary:
- `aggregate_raw_ptr_metadata_roundtrip` (`arr = [10u32, 20, 30, 40]`, `aggregate_raw_ptr(p, 4)` $\to$ `ptr_metadata` $\to$ `s.len()` $\to$ `slice_get_unchecked(sp, idx)`): exits **`rc = 0`** cleanly.
- `slice_len_dangling_ref` (`let raw = slice_from_raw_parts(dangling, 5); let s: &[u32] = unsafe { &*raw }; s.len()`): exits **`rc = 1`** (`error: Undefined Behavior: constructing invalid value of type &[u32]: encountered a dangling reference (0x4[noalloc] has no provenance)`).

Lean theorems `aggregateRawPtr_ptrMetadata_bijection` and `ptrMetadata_derefPointer_validity_boundaries` formalize all four round-trip cases (thin, slice, valid `dyn Trait`, and slice reconstruction identity) alongside both failure boundaries (dangling `&[T]` and invalid `dyn Trait` vtable).

---

### Finding 6: `LowerSliceLenCalls` (`lower_slice_len.rs`) Refinement, Gating Matrix, and Latent CFG-Cache Defect

`Basis: source, execution, derived`

In `library/core/src/slice/mod.rs:112-120` (`137d1d49458b`), `<[T]>::len` is wired as the `slice_len_fn` lang item:

```rust
#[lang = "slice_len_fn"]
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_const_stable(feature = "const_slice_len", since = "1.39.0")]
#[rustc_no_implicit_autorefs]
#[inline]
#[must_use]
pub const fn len(&self) -> usize {
    ptr::metadata(self)
}
```

`LowerSliceLenCalls` (`compiler/rustc_mir_transform/src/lower_slice_len.rs:10-65`) runs as an optional optimization pass at the start of `run_optimization_passes` (`lib.rs:718`, immediately after `CheckAlignment`/`CheckNull`/`CheckEnums` and **before `Inline`** so the call is simplified prior to inlining work):

```rust
// compiler/rustc_mir_transform/src/lower_slice_len.rs:13-64 (137d1d49458b)
fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
    PassPolicy::optional(ctx.mir_opt_level() >= 1)
}
...
// The one successor remains unchanged, so no need to invalidate
let basic_blocks = body.basic_blocks.as_mut_preserves_cfg();
...
if let TerminatorKind::Call {
    func, args, destination, target: Some(bb), call_source: CallSource::Normal, ..
} = &terminator.kind
    && let [arg] = &args[..]
    && let Some((fn_def_id, _)) = func.const_fn_def()
    && fn_def_id == slice_len_fn_item_def_id
{
    let r_value = Rvalue::UnaryOp(UnOp::PtrMetadata, arg.node.clone());
    block.statements.push(Statement::new(terminator.source_info, StatementKind::Assign(Box::new((*destination, r_value)))));
    block.terminator_mut().kind = TerminatorKind::goto(*bb);
}
```

#### Exact Activation Conditions and Live Differential Evidence (`-Zmir-opt-level=0` vs. `1`)

| Specimen (`support/probe_results.json`) | `-Zmir-opt-level=0` (`runtime-optimized.after.mir`) | `-Zmir-opt-level=1` (`LowerSliceLenCalls.before` $\to$ `after`) | Explanation |
| :--- | :--- | :--- | :--- |
| `probe_slice_len(s: &[u32])` | `LowerSliceLenCalls` does NOT run; retains `_0 = core::slice::<impl [u32]>::len(move _2) -> [return: bb1, unwind continue]` | `Call(slice::len, move _2)` $\to$ **`_0 = PtrMetadata(move _2); goto -> bb1;`** | All five syntactic gates satisfied (`opt >= 1`, `target: Some`, `Normal`, 1 arg, `const_fn_def == slice_len_fn`). |
| `probe_slice_len_mut_reborrow(s: &mut [u32])` (`s[0] = 1; s.len()`) | `LowerSliceLenCalls` does NOT run; retains `Call(slice::len, move _6)` after `(*_1)[_2] = const 1_u32` | `_6 = &(*_1); Call(slice::len, move _6)` $\to$ **`_0 = PtrMetadata(move _6); goto -> bb2;`** | Mutation/aliasing on `s` prior to `.len()` does **not** inhibit lowering because Rust creates an explicit shared reborrow `_6 = &(*_1)` whose lifetime spans only the call, and `PtrMetadata` reads the fat-pointer metadata of `_6` after `deref_pointer` validation. |
| `probe_slice_len_fn_ptr(s: &[u32])` (`let f: fn(&[u32]) -> usize = <[u32]>::len; f(s)`) | Retains `_0 = move _3(move _4) -> [return: bb1, unwind continue]` | **Unchanged** (`_0 = move _3(move _4) -> [return: bb1, unwind continue]`) | Indirect call through `FnPtr` local `_3`; `func.const_fn_def()` returns `None`. |
| `probe_slice_len_sole_unwind_cleanup(s: &[u32], _g: DropGuard)` | Retains `_0 = core::slice::<impl [u32]>::len(move _3) -> [return: bb1, unwind: bb3]` | `Call(slice::len, move _3) -> [return: bb1, unwind: bb3]` $\to$ **`_0 = PtrMetadata(move _3); goto -> bb1;`** (`bb3 (cleanup)` orphaned!) | **Fires even when `unwind: UnwindAction::Cleanup(bb3)` is present**, deleting the `bb0 -> bb3` CFG edge while calling `as_mut_preserves_cfg()`! |

#### Latent Upstream CFG-Cache Defect in `lower_slice_len.rs:24-25`

Because `core::slice::<impl [T]>::len` (`library/core/src/slice/mod.rs:118`) is **not** annotated with `#[rustc_nounwind]`, `AbortUnwindingCalls` and `RemoveNoopLandingPads` preserve `unwind: bb3` whenever a local with a non-trivial `Drop` impl (`DropGuard`) is live across `s.len()`. When `LowerSliceLenCalls` rewrites `bb0`'s terminator from `Call { target: Some(bb1), unwind: Cleanup(bb3) }` to `Goto { target: bb1 }`, the successor set of `bb0` strictly shrinks from `[bb1, bb3]` to `[bb1]` — leaving `bb3 (cleanup)` with **zero** incoming edges in `probe_slice_len_sole_unwind_cleanup`.

Calling `body.basic_blocks.as_mut_preserves_cfg()` (`lower_slice_len.rs:25`) relies on the comment `// The one successor remains unchanged, so no need to invalidate`, which holds **only** when `unwind` is `Continue`/`Unreachable`/`Terminate` and is **false** whenever `unwind` is `Cleanup(bb)`. In `rustc`'s default pipeline this does not currently trigger an ICE only because the preceding passes (`CheckAlignment`, `CheckNull`, `CheckEnums`) do not populate `basic_blocks.cache` before `LowerSliceLenCalls`, and later `SimplifyCfg` invalidates the cache. However, any pass added between `Runtime(PostCleanup)` and `LowerSliceLenCalls` that queries `body.basic_blocks.predecessors()` or `dominators()` would inherit stale CFG caches (listing `bb0` as a predecessor of orphaned `bb3`). Lean theorems `lowerSliceLenCalls_refines_call` and `lowerSliceLenCalls_drops_cleanup_edge_invalidates_cfg` mechanize both the semantic soundness of the rewrite and this exact CFG-edge discrepancy.

---

### Finding 7: `PostAnalysisNormalize` (`post_analysis_normalize.rs`) and `CleanupPostBorrowck` (`cleanup_post_borrowck.rs`)

`Basis: source, execution, derived`

Direct source inspection clarifies a common misconception about where `user_type_annotations` are eliminated and how opaque types transition into the runtime MIR dialect:

1. **`user_type_annotations` are cleared by `CleanupPostBorrowck`, NOT asserted by `PostAnalysisNormalize`:**
   - Inside `run_analysis_cleanup_passes` (`lib.rs:642-656`), `CleanupPostBorrowck` (`lib.rs:645`, `PassPolicy::Required`) runs **before** `Derefer` (`line 648`) and **before** `PostAnalysisNormalize` (`line 655`).
   - `CleanupPostBorrowck::run_pass` (`compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:27-84`) converts `StatementKind::AscribeUserType`, `FakeRead`, fake borrows, and `BackwardIncompatibleDropHint` into `Nop`, replaces `FalseEdge`/`FalseUnwind` with `Goto`, downgrades `ArrayToPointer`/`MutToConstPointer` coercions to `CastKind::PtrToPtr`, and explicitly clears both annotation stores:
     ```rust
     // compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:79-83 (137d1d49458b)
     body.user_type_annotations.raw.clear();
     for decl in &mut body.local_decls {
         decl.user_ty = None;
     }
     ```
   - `post_analysis_normalize.rs` (`lines 1-98` at `137d1d49458b`; `lines 1-86` at `14210df0e27c`) contains **no** assertion on `user_type_annotations`; MIR validation (`validate.rs:296-303`) enforces that `AscribeUserType` and `FakeRead` are absent beginning at `MirPhase::Runtime(RuntimePhase::Initial)`.
   - Live MIR dumps of `probe_assoc_norm` confirm this exact sequencing: `CleanupPostBorrowck.before.mir` contains two `User Type Annotations` entries (`Canonical { value: Ty(<u32 as Assoc>::Out), ... }`), `let _2: u64 as UserTypeProjection { base: UserType(0), projs: [] }`, and `AscribeUserType(_2, o, ...)`; immediately in `CleanupPostBorrowck.after.mir`, the entire `User Type Annotations` table is empty, `_2` is plain `let _2: u64;`, and `AscribeUserType` is `nop;`.
2. **Exact `TypingMode::PostAnalysis` Transition (`lib.rs:651-655` + `mir/mod.rs:414-439`):**
   - `run_analysis_cleanup_passes` executes `[ImpossibleClauses, CleanupPostBorrowck, RemoveNoopLandingPads, SimplifyCfg::PostAnalysis, Derefer]` with phase transition `Some(MirPhase::Analysis(AnalysisPhase::PostCleanup))` (`lib.rs:651`), and **then** executes `PostAnalysisNormalize` (`lib.rs:655`) in a separate `pm::run_passes(..., None)` call.
   - Because `body.phase` is now `MirPhase::Analysis(AnalysisPhase::PostCleanup)`, `Body::typing_env` (`compiler/rustc_middle/src/mir/mod.rs:414-439`) returns `TypingEnv::post_analysis(tcx, body.source.def_id())`, switching trait/opaque resolution from borrowck mode (where opaque types remain hidden) into `TypingMode::PostAnalysis` (where all opaques defined in the crate reveal their concrete hidden types and specializable associated items normalize).
   - As `lib.rs:652-654` warns: moving `PostAnalysisNormalize` earlier or later causes `-Zvalidate-mir` to fail due to mismatched `TypingEnv`s (`Subtyper` at `lib.rs:664` also relies on opaque types already being revealed).
3. **`OpaqueCast` Projection Removal and `try_normalize` Fallback:**
   - Under the classic trait solver (`if !self.tcx.next_trait_solver_globally()`, `post_analysis_normalize.rs:43-58`), `visit_place` filters out every `ProjectionElem::OpaqueCast(_)` element (re-interning only when at least one `OpaqueCast` is present), because once opaque types are replaced with their hidden types, `OpaqueCast` projections are redundant — and `validate.rs:882-889` rejects any surviving `ProjectionElem::OpaqueCast` starting at `MirPhase::Runtime(RuntimePhase::Initial)`.
   - Live MIR dumps of `project_opaque_pair` (`type OpaquePair = impl Copy; #[define_opaque(OpaquePair)] pub fn project_opaque_pair(p: OpaquePair) -> u64 { let Pair(_, y) = p; y }`) verify this directly:
     - `PostAnalysisNormalize.before.mir`: `fn project_opaque_pair(_1: OpaquePair) -> u64` with `_2 = copy ((_1 as Pair).1: u64);` (`ProjectionElem::OpaqueCast(Pair)`).
     - `PostAnalysisNormalize.after.mir`: `fn project_opaque_pair(_1: Pair) -> u64` with `_2 = copy (_1.1: u64);` (opaque revealed to `Pair` and `OpaqueCast` stripped).
   - In `visit_const_operand` (`lines 63-74`), `visit_ty` (`lines 77-87`), and `visit_args` (`lines 90-97`, newly added between `14210df0e27c` and `3ef0c22cdb86`), `PostAnalysisNormalizeVisitor` deliberately uses **`if let Ok(...) = self.tcx.try_normalize_erasing_regions(self.typing_env, ty::set_aliases_to_non_rigid(self.tcx, ...))`** rather than panicking `normalize_erasing_regions`. As noted in the source comment (`#91745`), bodies with impossible-to-satisfy `where` clauses (when `ImpossibleClauses` is disabled or does not simplify a local-generic clause) can contain unnormalizable projections; `try_normalize_erasing_regions` falls back cleanly without ICEing.

Lean theorems `cleanupPostBorrowck_clears_user_type_annotations`, `postAnalysisNormalize_eliminates_opaque_cast`, `postAnalysisNormalize_preserves_place_eval`, and `postAnalysisNormalize_reveals_or_preserves_on_impossible` mechanize these exact invariants.

---

### Finding 8: `trivial_const` (`trivial_const.rs` + `lib.rs` + `eval_queries.rs`) Chained Fast Path and Soundness Guard Necessity

`Basis: source, execution, derived`

`trivial_const` (`compiler/rustc_mir_transform/src/trivial_const.rs:46-124` at `137d1d49458b`) implements a zero-pipeline fast path for constant items whose `mir_built` body trivially evaluates without control flow, panics, drops, or runtime operations.

#### Exact Syntactic and Semantic Admissibility Predicate (`trivial_const.rs:55-113`)

A `LocalDefId` qualifies as a trivial const returning `Some((ConstValue, Ty<'tcx>))` **if and only if ALL nine conditions hold**:

1. **Admitted `DefKind` (`lines 55-59`):** `DefKind::Const`, `DefKind::AssocConst`, or `DefKind::AnonConst` with `tcx.anon_const_kind(def) != AnonConstKind::NonTypeSystemInline` (the `NonTypeSystemInline` exclusion was added between `14210df0e27c` and `3ef0c22cdb86` so inline `const { ... }` blocks do not bypass MIR analysis/const-checking; `DefKind::Static` and `DefKind::Fn` are always rejected).
2. **No impossible clauses (`lines 65-67`, added in `3ef0c22cdb86` / `137d1d49458b`):** `!crate::impossible_clauses::has_impossible_clauses(tcx, def.into())`.
3. **Defines no opaque types (`lines 69-71`):** `tcx.opaque_types_defined_by(def).is_empty()`.
4. **Body contains no opaque types (`lines 75-77`):** `!body.has_opaque_types()`.
5. **Single basic block (`lines 79-81`):** `body.basic_blocks.len() == 1`.
6. **Single statement (`lines 83-86`):** `body.basic_blocks[START_BLOCK].statements.len() == 1`.
7. **`Return` terminator (`lines 88-90`):** `block.terminator().kind == TerminatorKind::Return`.
8. **Direct return-place constant assignment (`lines 92-102`):** Statement 0 is `StatementKind::Assign((place, Rvalue::Use(Operand::Constant(c), _)))` with `*place == Place::from(RETURN_PLACE)` (`_0`).
9. **Literal or chained empty-args trivial const (`lines 103-112`):**
   - `Const::Val(v, ty)` $\to$ `Some((v, ty))` (base case);
   - `Const::Unevaluated(UnevaluatedConst { def, args, .. }, _)` with **`args.is_empty()`** $\to$ recursive `tcx.trivial_const(def)` (chained case);
   - `Const::Ty(..)` or non-empty `args` $\to$ `None`.

#### Complete Bypass Hook Points in `rustc_mir_transform` and `rustc_const_eval`

- **`mir_built` (`lib.rs:403-408`):** Invokes `trivial_const::trivial_const(tcx, def, || &body)` immediately after `build_mir_inner_impl(def)`. On `Some(_)`, it allocates `&Steal<Body>`, dumps `1-1-000.built.after.mir`, and **returns immediately** — skipping `LintAndRemoveUninhabited`, all six MIR lints (`CheckForceInline`, `CheckCallRecursion`, `CheckPackedRef`, `CheckConstItemMutation`, `CheckMutRestriction`, `FunctionItemReferences`), `SimplifyCfg::Initial`, and `SanityCheck`.
- **`mir_promoted` (`lib.rs:440`) and `mir_for_ctfe` (`lib.rs:502`):** Both enforce `debug_assert!(!tcx.is_trivial_const(def))` (in debug builds, requesting promoted or CTFE MIR for a trivial const panics!).
- **`eval_to_const_value_raw_provider` (`compiler/rustc_const_eval/src/const_eval/eval_queries.rs:377-379`):** Short-circuits directly to `return Ok(value)` when `tcx.trivial_const(def_id)` returns `Some((value, _ty))` — never even constructing an `InterpCx`!
- **`eval_to_allocation_raw_provider` (`eval_queries.rs:468-473`):** Routes `Some((value, ty))` into `eval_trivial_const_using_ecx` (`lines 146-160`), which copies `value` directly into the return allocation and runs `intern_and_validate` without ever calling `ecx.load_mir` or `mir_for_ctfe`.

#### Live Empirical Pipeline Census and `has_impossible_clauses` Soundness Bug Reproduction (`1.98.0-nightly`)

Running `probe_lower_intrinsics_slice_len_and_trivial_const.py` with `-Zdump-mir=all` on `rustc 1.98.0-nightly` (`14210df0e27c`) produces a stark binary split (`1` MIR file vs. `49` MIR files) and **directly reproduces live the pre-fix `has_impossible_clauses` soundness discrepancy**:

| Constant Item (`support/probe_results.json`) | Rust Definition | MIR Dump Count | Compile `rc` | Pipeline Executed |
| :--- | :--- | :---: | :---: | :--- |
| `TRIV_A` | `pub const TRIV_A: usize = 42;` | **`1`** | `0` | `built.after.mir` only (`_0 = const 42_usize; return;`) |
| `TRIV_B` | `pub const TRIV_B: usize = TRIV_A;` | **`1`** | `0` | `built.after.mir` only (`_0 = const TRIV_A; return;`) — 1-hop chained trivial const |
| `TRIV_C_CHAIN2` | `pub const TRIV_C_CHAIN2: usize = TRIV_B;` | **`1`** | `0` | `built.after.mir` only (`_0 = const TRIV_B; return;`) — 2-hop chained trivial const |
| `NON_TRIV_ARITH` | `pub const NON_TRIV_ARITH: usize = 40 + 2;` | **`49`** | `0` | Full pipeline (`nll`, `renumber`, `SimplifyCfg-initial`, `PromoteTemps`, `ImpossiblePredicates`, `CleanupPostBorrowck`, `Derefer`, `PostAnalysisNormalize`, `ElaborateDrops`, `LowerIntrinsics`, `RemovePlaceMention`, `CtfeLimit`) |
| `NON_TRIV_GENERIC_REF` | `pub const NON_TRIV_GENERIC_REF: usize = GenHolder::<u8>::ASSOC_TRIV;` | **`49`** | `0` | Rejected by `if !args.is_empty() { return None; }` (`trivial_const.rs:106-108`) -> full 49-pass pipeline |
| `NON_TRIV_OPAQUE_DEF` | `#[define_opaque(HiddenCopy)] pub const NON_TRIV_OPAQUE_DEF: HiddenCopy = 99usize;` | **`49`** | `0` | Rejected by `!tcx.opaque_types_defined_by(def).is_empty()` (`lines 69-71`) -> full 49-pass pipeline |
| `IMPOSSIBLE_CLAUSE_TRIV` | `pub const IMPOSSIBLE_CLAUSE_TRIV: usize = 7 where String: Copy;` | **`1`** | **`0`** | **Pre-guard bug on `14210df0e27c`:** bypassed `ImpossiblePredicates` completely and evaluated cleanly to `7`! |
| `IMPOSSIBLE_CLAUSE_NON_TRIV` | `pub const IMPOSSIBLE_CLAUSE_NON_TRIV: usize = 3 + 4 where String: Copy;` | **`49`** | **`1`** | Entered full pipeline; `ImpossiblePredicates` replaced body with `bb0: { unreachable; }`; CTFE aborted with `error[E0080]: entering unreachable code`! |

Look at why the two guards in `trivial_const.rs:65-77` are mathematically load-bearing:
1. **Why `has_impossible_clauses` (`lines 65-67`) is load-bearing:** `ImpossibleClauses` (`compiler/rustc_mir_transform/src/impossible_clauses.rs:68-115`) detects unsatisfiable global `where` clauses (such as `where String: Copy` under `#![feature(trivial_bounds, generic_const_items)]`) and structurally unsized `Sized` clauses (`dyn Trait<T>: Sized`), truncating the MIR body to a lone `bb0: { unreachable; }` so CTFE rejects evaluation with `E0080`. Without `has_impossible_clauses` in `trivial_const`, `const A: usize = 7 where String: Copy` succeeds (`7`) while semantically identical `const B: usize = 3 + 4 where String: Copy` fails (`E0080`). Adding `has_impossible_clauses` at `3ef0c22cdb86`/`137d1d49458b` forces `IMPOSSIBLE_CLAUSE_TRIV` onto the full pipeline so both evaluate identically.
2. **Why `!tcx.opaque_types_defined_by(def).is_empty()` (`lines 69-71`) and `body.has_opaque_types()` (`lines 75-77`) are load-bearing:** Opaque type hidden types (`type HiddenCopy = impl Copy`) are inferred and checked during `mir_borrowck` and revealed during `PostAnalysisNormalize`. If a constant defining or mentioning an opaque type took the `trivial_const` shortcut, `mir_borrowck` would be bypassed (leaving hidden types unchecked or undefined) and `Const::Val` would carry an unnormalized opaque type into `eval_to_const_value_raw`.
3. **Why `args.is_empty()` (`lines 106-108`) is load-bearing:** A generic associated const reference like `GenHolder::<u8>::ASSOC_TRIV` carries substitution arguments `[u8]` (which may violate trait bounds, carry lifetimes, or select specialized/overridden associated items); checking `tcx.trivial_const(def)` on the uninstantiated `DefId` without instantiating `args` would ignore those substitutions.

Lean theorems `trivialConst_eval_equiv_ctfe` (general structural induction over arbitrary chain depth `fuel`), `trivialConst_without_impossibleClauses_unsound_counterexample`, `trivialConst_without_opaqueGuard_counterexample`, `trivialConst_rejects_nonempty_generic_args`, and `trivialConst_rejects_non_type_system_inline_anon_const` mechanically prove both sufficiency of the guarded fast path and necessity of each guard.

---

### Finding 9: Anneal TCB Capture Seam (`joshlf/anneal@c131b320eeeb`) Coverage Matrix

`Basis: source, derived`

Auditing `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`) against the exact MIR artifacts produced or bypassed by these four passes yields a complete fail-closed TCB seam audit:

| Emitted / Affected MIR Construct | Producing Pass | `Trusted/MirAst.lean` Representation (`c131b320e`) | `Trusted/MirSemantics.lean` Behavior (`c131b320e`) | Verification Seam Implication |
| :--- | :--- | :--- | :--- | :--- |
| `TerminatorKind::Unreachable` | `LowerIntrinsics` (`unreachable`, uninhabited `read_via_copy`/`transmute`) & `ImpossibleClauses` | `TerminatorKind.unreachable` (`line 776`) | `.fault .undefined` (`lines 1551-1552`) | **Exact match.** Pre-`Unreachable` statements execute before `.unreachable`, so Anneal preserves statement-before-`Unreachable` ordering whenever the statement itself is in the modeled fragment. |
| `Operand::RuntimeChecks` | `LowerIntrinsics` (`ub_checks`, `overflow_checks`, `contract_checks`) | Explicitly **omitted** from `MirAst.Operand` (`lines 36, 548-556`) | Fail-closed: capture must reject rather than folding to `.constant` | **Sound fail-closed.** Crate-dependent runtime checks cannot be constant-folded during capture. |
| `BinOp::{Add,Sub,Mul,Div,Rem,AddUnchecked,SubUnchecked,MulUnchecked,ShlUnchecked,ShrUnchecked,AddWithOverflow,SubWithOverflow,MulWithOverflow,Offset}` | `LowerIntrinsics` (arms 6, 7, 10) | 1-to-1 constructors in `MirAst.BinOp` (`lines 400-408`) | Arithmetic/shift/overflow modeled in `evalBinOp`; `.offset` returns `.error .unsupported` | **Sound.** Lowered integer/wrapping/unchecked/with-overflow ops land directly in Anneal's modeled fragment; pointer `.offset` fails closed. |
| `BinOp::Cmp` | `LowerIntrinsics` (`three_way_compare`) | Omitted from `BinOp`; lowers at `Rvalue` level to `.unsupported` (`lines 397-399`) | `.error .unsupported` (`line 1313`) | **Sound fail-closed.** |
| `StatementKind::Intrinsic(CopyNonOverlapping \| Assume)` | `LowerIntrinsics` (arms 4, 5) | `StatementKind.unsupported` (`lines 655-662`) | `.fault .unsupported` | **Sound fail-closed.** Note: once `Assume`/`CopyNonOverlapping` are added to Anneal, capture pinned to `f8a08b688` (`1.98.0-nightly`) must note that `14210df0e2` omits the trailing `*dst = ()` assignment whereas `137d1d4945` emits it. |
| `Rvalue::Use(Operand::Copy(*local), WithRetag::Yes)` | `LowerIntrinsics` (`read_via_copy`) | `Rvalue.use` only for no-retag / reference-free types; otherwise `.unsupported` (`lines 583-597`); `ProjectionElem.deref` (`line 473`) | `evalOperandToSlot` / deref on raw pointers fails closed until heap memory model lands | **Sound fail-closed.** Note `WithRetag::Yes` gate on `MirAst.lean:596-597` explicitly catches reference/box copies. |
| `Rvalue::Discriminant(*arg)` | `LowerIntrinsics` (`discriminant_value`) | `Rvalue.discriminant place` (`line 624`) | Supported only for unprojected locals (`place.projection.isEmpty`, `lines 1269-1271`); `(*arg)` (`[.deref]`) returns `.error .unsupported` | **Sound fail-closed.** Lowered `discriminant((*_2))` has `[.deref]` projection so it cleanly fails closed rather than mis-evaluating as an unprojected local. |
| `Rvalue::RawPtr` / `Rvalue::Ref` on `(*ptr)[idx]` | `LowerIntrinsics` (`slice_get_unchecked`) | `ProjectionElem.index` maps to `.unsupported` (`lines 469-475`); `Rvalue.addressOf`/`ref` return `.error .unsupported` (`line 1313`) | `.error .unsupported` | **Sound fail-closed.** |
| `Rvalue::Cast(CastKind::Transmute, ...)` | `LowerIntrinsics` (`transmute`, `transmute_unchecked`) | `Rvalue.unsupported` (`lines 612-618`) | `.error .unsupported` (`line 1313`) | **Sound fail-closed.** |
| `Rvalue::Aggregate(AggregateKind::RawPtr, ...)` | `LowerIntrinsics` (`aggregate_raw_ptr`) | `Rvalue.unsupported` (`lines 612-618`) | `.error .unsupported` (`line 1313`) | **Sound fail-closed.** |
| `Rvalue::UnaryOp(UnOp::PtrMetadata, ...)` | `LowerIntrinsics` (`ptr_metadata`) & `LowerSliceLenCalls` | `UnOp.ptrMetadata` (`lines 445-446`) | `evalUnOp` returns `.error .unsupported` (`lines 1177-1193`) | **Sound fail-closed.** When Anneal later models `UnOp.ptrMetadata`, it **must** enforce `deref_pointer` validity (`operator.rs:501`: null/align/deref on `&[T]`, vtable validity on `dyn Trait`) rather than treating `PtrMetadata` as a pure tuple projection! |
| `<[T]>::len` calls at `Runtime(PostCleanup)` | *Not yet lowered* (runs later in `run_optimization_passes`) | `TerminatorKind.call` (`line 752`) | `.fault .unsupported` (`line 1568`) | **Architectural implication:** At `Runtime(PostCleanup)`, `<[T]>::len` is STILL a `Call` to `core::slice::<impl [T]>::len`, NOT `UnOp::PtrMetadata`. Verifying slice-length code at `Runtime(PostCleanup)` therefore requires either inlining/modeling `core::slice::len` (whose body calls `ptr_metadata`) or selectively running `LowerSliceLenCalls` (fixing its `as_mut_preserves_cfg()` unwind-edge bug!). |
| `ProjectionElem::OpaqueCast` & `user_type_annotations` | Removed before `Runtime(PostCleanup)` by `PostAnalysisNormalize` & `CleanupPostBorrowck` | `OpaqueCast` -> `ProjectionElem.unsupported` (`line 470`); `AscribeUserType` -> `StatementKind.unsupported` (`line 655`) | Absent in well-formed `Runtime(PostCleanup)` bodies | **Guaranteed absent** for classic-solver `Runtime(PostCleanup)` bodies (note `-Znext-solver=globally` interaction in Boundaries). |
| `trivial_const` items | `mir_built` early exit (`lib.rs:403-408`) | `ConstLit.{scalar, zeroSized}` (`lines 504-506`) | Consumed as pre-evaluated `Operand.constant` inside callers | **Capture hazard:** A capture driver iterating `tcx.hir_body_owners()` **must NOT** call `tcx.mir_promoted(def)`, `tcx.mir_drops_elaborated_and_const_checked(def)`, or `tcx.mir_for_ctfe(def)` on `tcx.is_trivial_const(def)` items (doing so trips `debug_assert!(!tcx.is_trivial_const(def))` in debug builds and bypasses the fast path); instead, resolve them via `tcx.trivial_const(def)`. |

Note also that at `joshlf/anneal@c131b320eeeb`, `trusted/rustc-capture/src/driver.rs:25` pins `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"` — one day prior to `14210df0e27c` (`2026-05-31`). Consequently, any capture driver upgraded to extract constants on that `1.98.0-nightly` toolchain inherits the pre-`has_impossible_clauses` `trivial_const` behavior (and the pre-unit-destination-store `copy_nonoverlapping`/`assume` lowering) until the toolchain pin advances past `3ef0c22cdb86`.

---

### Finding 10: Kernel-Checked Lean 4 (`v4.34.1`) Mechanization Architecture and Theorem Inventory

`Basis: source, execution, derived`

[`support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean`](support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean) (`2,310` lines, `95,047` bytes, `45` user-declared theorems, `411` total namespace environment theorems) mechanizes all four passes in standalone Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with **zero external imports** beyond `Init`, **zero `sorry`**, **zero `Classical.choice`**, **zero `omega`**, **zero `bv_decide`**, **zero `native_decide`**, **zero `partial def`**, **zero `unsafe`**, **zero `deriving`**, and **zero `._unsafe_rec` constants** (achieved by expressing all list and fuel iterations via `List.foldr` and `Nat.rec` rather than equation-compiled self-recursion).

| Group | Mechanized Theorems (`RustcMirLowerIntrinsicsSoundness.*`) | Axioms Used | What Is Formally Established |
| :--- | :--- | :--- | :--- |
| **1. Place & Post-`Derefer` Invariants** (`7` thms) | `checkValueValidity_uninhabited_always_faults`, `projList_anyIndirect_append`, `sliceGetUnchecked_preserves_derefOnlyFirst_iff`, `sliceGetUnchecked_plainLocal_preserves_derefOnlyFirst`, `sliceGetUnchecked_indirect_violates_derefOnlyFirst`, `sliceGetUnchecked_fieldProj_bypasses_isIndirect_yet_violates_derefOnlyFirst`, `discriminantValue_nonlocal_violates_derefOnlyFirst` | `[]` / `[propext]` | Exact iff characterization (`p.proj = []`) for post-`Derefer` safety of `slice_get_unchecked`; formal refutation showing `pair.0` (`[Field(0)]`) bypasses `assert!(!place.is_indirect())` while breaking `derefOnlyFirst`; refutation of unguarded `discriminant_value`. |
| **2. Intrinsic Census & Composition** (`6` thms) | `all_29_explicit_syms_are_lowered`, `evalStmts_nil`, `evalStmts_cons`, `evalStmts_append`, `execBlock_append_assign`, `execBlock_append_nonDiv_unit` | `[]` / `[propext]` | Exhaustive 29-intrinsic coverage witness (`syms.length = 29`, wildcard unlowered) and block-statement composition laws. |
| **3. `LowerIntrinsics` Soundness & Counterexamples** (`9` thms) | **`lowerIntrinsics_uninhabited_preserves_pre_ub`**, `lowerIntrinsics_readViaCopy_sizedUninhabited_null_is_memAccessUb`, `lowerIntrinsics_readViaCopy_void_null_is_invalidValueUb`, `naive_uninhabited_drop_stmt_misclassifies_ub`, **`aggregateRawPtr_ptrMetadata_bijection`**, `ptrMetadata_derefPointer_validity_boundaries`, `assume_unit_dest_fix_head_vs_legacy198`, `sliceGetUnchecked_const_index_triggers_ice`, `lowerIntrinsics_sound_all_arms` | `[propext]` / `[propext, Quot.sound]` | Universal fault-kind preservation for uninhabited `read_via_copy`/`transmute`/`transmute_unchecked`; refutation of statement omission; complete wide-pointer bijection and `deref_pointer` failure boundaries; `14210df0` vs `137d1d49` `assume` destination-write divergence; constant-index ICE; and total semantic equivalence across all 14 arms. |
| **4. `LowerSliceLenCalls` Refinement & CFG Defect** (`6` thms) | **`lowerSliceLenCalls_refines_call`**, `lowerSliceLenCalls_disabled_at_opt0`, `lowerSliceLenCalls_skips_fn_ptr`, `lowerSliceLenCalls_skips_non_normal_call_source`, `lowerSliceLenCalls_skips_diverging_call`, `lowerSliceLenCalls_drops_cleanup_edge_invalidates_cfg` | `[]` / `[propext]` | Full semantic equivalence (including `&[T]` validity checks on dangling slices); all four gating boundaries; and formal refutation of `as_mut_preserves_cfg()` when `unwind = some cleanupBb`. |
| **5. `PostAnalysisNormalize` & `CleanupPostBorrowck`** (`6` thms) | `cleanupPostBorrowck_clears_user_type_annotations`, `stripOpaqueCasts_hasOpaqueCast_false`, `postAnalysisNormalize_eliminates_opaque_cast`, `evalProjVal_cons`, `postAnalysisNormalize_preserves_place_eval`, `postAnalysisNormalize_reveals_or_preserves_on_impossible` | `[]` / `[propext]` | `user_type_annotations` clearing prior to normalization; total elimination of `ProjectionElem::OpaqueCast`; projection-evaluation preservation under `OpaqueCast` erasure; and `try_normalize` fallback preservation under impossible clauses. |
| **6. `trivial_const` Equivalence & Guard Necessity** (`11` thms) | `trivialConst_zero`, `trivialConst_succ`, `evalFullCtfe_succ`, **`trivialConst_eval_equiv_ctfe`**, `trivialConst_chain2_resolves_concrete`, **`trivialConst_without_impossibleClauses_unsound_counterexample`**, `trivialConst_without_opaqueGuard_counterexample`, `trivialConst_rejects_nonempty_generic_args`, `trivialConst_rejects_non_type_system_inline_anon_const`, `trivialConst_rejects_arithmetic_body`, `trivialConst_rejects_static_and_fn` | `[]` / `[propext]` | Arbitrary-depth induction proving guarded `trivial_const` agrees identically with full CTFE; concrete 3-const chain witness; and formal refutations proving necessity of `has_impossible_clauses`, opaque-type guards, `args.is_empty()`, and `AnonConstKind::NonTypeSystemInline`. |

## Boundaries

To prevent over-generalization, the following negative-space boundaries apply strictly:

1. **Live execution pinned to `1.98.0-nightly` (`14210df0e27c`), not a compiled `137d1d49458b` binary (`not examined` for live `137d1d49458b` execution):**
   - All live `rustc` MIR dumps, ICE reproductions (`rc = 101`), and Miri runs (`0.1.0`) were executed on `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65, 2026-05-31)`.
   - Claims about changes introduced between `14210df0e27c` and `137d1d49458b` (`copy_nonoverlapping`/`assume` destination unit write, `has_impossible_clauses` and `AnonConstKind::NonTypeSystemInline` in `trivial_const.rs`, `visit_args` and `body.typing_env(tcx)` in `post_analysis_normalize.rs`, and `Intrinsic::Rustc(name)` in `lower_intrinsics.rs`) are established by direct primary-source inspection of `137d1d49458b` and `3ef0c22cdb86` plus mechanized Lean proof (`source` + `derived`), **not** by executing a `137d1d49458b` binary.
2. **Next-generation trait solver (`-Znext-solver=globally`) `OpaqueCast` behavior (`not examined` empirically):**
   - `post_analysis_normalize.rs:43` skips stripping `ProjectionElem::OpaqueCast` when `self.tcx.next_trait_solver_globally()` is `true`, because the new solver avoids emitting `OpaqueCast` projections during MIR construction in the first place. We did not execute live `-Znext-solver=globally` probes to confirm whether any residual `OpaqueCast` can survive under `-Znext-solver=globally`.
3. **Contract-check intrinsic (`sym::contract_checks`) invocation surface (`known not to apply` on `1.98.0-nightly` public `core::intrinsics`):**
   - Although `lower_intrinsics.rs:27-43` (and `lines 25-41` at `14210df0e27c`) lowers `sym::contract_checks` to `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)`, `core::intrinsics` at `1.98.0-nightly` does not export a standalone `core::intrinsics::contract_checks` function (`E0425`, and manually declaring `#[rustc_intrinsic] fn contract_checks() -> bool;` triggers `E0093: unrecognized intrinsic` during intrinsic type-checking after `LowerIntrinsics` has already lowered the call). Our `rc = 0` live probe therefore executes `ub_checks()` and `overflow_checks()`, while `contract_checks` lowering is verified from primary source (`lower_intrinsics.rs:27-43`).
4. **`LowerSliceLenCalls` CFG-cache bug triggerability in stock `-Zmir-opt-level=1..2` pipelines (`unknown` whether any current flag combination triggers an ICE without a custom pass):**
   - While live `probe_slice_len_sole_unwind_cleanup` proves `LowerSliceLenCalls` removes `bb0 -> bb3 (cleanup)` under `as_mut_preserves_cfg()`, we did not exhaustively search all `-Zmir-enable-passes` permutations to determine whether an upstream pass between `Runtime(PostCleanup)` and `LowerSliceLenCalls` can be enabled via CLI flags alone to populate `basic_blocks.cache` and trigger a live stale-predecessor ICE.
5. **Stack-borrows / Tree-borrows retagging differences between `<[T]>::len(&self)` `FnEntry` retag and `UnOp::PtrMetadata` (`not examined`):**
   - `LowerSliceLenCalls` runs in `run_optimization_passes` (which Miri disables via `-Zmir-opt-level=0`), so Miri executes the `core::slice::len` call with normal `FnEntry` protector/retag semantics rather than lowered `PtrMetadata`. Whether replacing `Call(slice::len, &s)` with `PtrMetadata(&s)` (eliminating the `FnEntry` protector on `&self`) is strictly refining under Stacked Borrows / Tree Borrows in the presence of concurrent/reentrant raw-pointer aliasing is **not examined** in our Lean model (which models `deref_pointer` validity without aliasing stacks/trees).
6. **Lean formalization abstraction boundary (`known not to apply` as a direct proof over `rustc` Rust source or `joshlf/anneal` imports):**
   - `support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean` is a standalone Lean `v4.34.1` formalization modeling the exact algorithms and side conditions audited in `rust-lang/rust`; it does **not** import `joshlf/anneal`'s `Trusted.MirSemantics` module directly and does **not** mechanically extract Rust source into Lean. Single-block `ExecState` abstracts away multi-threaded weak memory, Stacked/Tree Borrows provenance trees, unwind stack unwinding execution, and full `TyCtxt` trait-solver normalization algorithms.
7. **Other MIR optimization passes and MIR-build-time intrinsic lowerings (`not examined`):**
   - `write_via_move` (lowered in `rustc_mir_build`), `const_eval_select` (`remap_mir_for_const_eval_select`), LLVM-named intrinsics (`Intrinsic::Llvm`), and downstream `InstSimplify` / `GVN` / `Inline` passes are outside the scope of this report.
8. **Attractive stronger conclusions NOT established:**
   - Passing `LowerIntrinsics` does **not** eliminate all `TerminatorKind::Call` terminators to `#[rustc_intrinsic]` items: only the 29 explicit `sym::*` names are lowered; all other intrinsics remain `Call`s in `Runtime(PostCleanup)`.
   - `assert!(!place.is_indirect())` in `lower_intrinsics.rs:254` does **not** guarantee post-`Derefer` MIR well-formedness on arbitrary `#[custom_mir]` inputs (refuted by `field_proj_slice_get_unchecked_validate_mir`).
   - `trivial_const` does **not** guarantee that `tcx.mir_drops_elaborated_and_const_checked(def)` can be called safely on constant items — in fact, `mir_promoted` and `mir_for_ctfe` explicitly assert `!tcx.is_trivial_const(def)`.

## Evidence

All primary-source, execution, and mechanized-proof evidence was acquired and verified on **`2026-11-23`**.

### 1. Primary Source Citations (`rust-lang/rust`, `rust-lang/reference`, `joshlf/anneal`)

- **`rust-lang/rust` HEAD (`137d1d49458b73b7b85d2c1599d8730886d65e47`, `2026-11-22T20:28:26Z`):**
  - `compiler/rustc_mir_transform/src/lower_intrinsics.rs`: `lines 1-369` (`Intrinsic::Rustc(name)` at `20`; 14 explicit arms at `24-358`; `copy_nonoverlapping` unit store at `76-88`; `assume` unit store at `102-114`; `read_via_copy` `as_local()` & `target: None => Unreachable` at `175-206`; `write_via_move` comment at `207`; `discriminant_value` unguarded `mk_place_deref` at `208-226`; `slice_get_unchecked` `assert!(!place.is_indirect())` & `index.node.place().unwrap().as_local().unwrap()` at `244-289`; `transmute`/`transmute_unchecked` cast-before-`Unreachable` at `290-314`; `aggregate_raw_ptr` & `ptr_metadata` at `315-358`; wildcard `_ => {}` at `359`; `PassPolicy::Required` at `365-368`).
  - `compiler/rustc_mir_transform/src/lower_slice_len.rs`: `lines 1-65` (`PassPolicy::optional(ctx.mir_opt_level() >= 1)` at `13-15`; `as_mut_preserves_cfg()` comment and call at `24-25`; `lower_slice_len_call` guard and rewrite at `33-65`).
  - `compiler/rustc_mir_transform/src/post_analysis_normalize.rs`: `lines 1-98` (`body.typing_env(tcx)` at `15`; `PassPolicy::Required` at `19-22`; `!next_trait_solver_globally()` `OpaqueCast` filter at `43-58`; `visit_const_operand`, `visit_ty`, `visit_args` using `try_normalize_erasing_regions` + `ty::set_aliases_to_non_rigid` at `63-97`).
  - `compiler/rustc_mir_transform/src/trivial_const.rs`: `lines 1-124` (`DefKind` & `AnonConstKind::NonTypeSystemInline` check at `55-59`; `has_impossible_clauses` guard at `65-67`; `!opaque_types_defined_by.is_empty()` at `69-71`; `body.has_opaque_types()` at `75-77`; syntactic 1-BB/1-stmt/`Return` check at `79-102`; recursive empty-args `UnevaluatedConst` & `Const::Val` at `103-112`; `trivial_const_provider` at `119-124`).
  - `compiler/rustc_mir_transform/src/impossible_clauses.rs`: `lines 1-121` (`is_structurally_unsized` at `38-49`; `has_impossible_clauses` at `68-97`; `ImpossibleClauses::run_pass` truncating to `bb0: { unreachable; }` at `101-115`).
  - `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs`: `lines 1-90` (`body.user_type_annotations.raw.clear()` and `decl.user_ty = None` at `79-83`).
  - `compiler/rustc_mir_transform/src/deref_separator.rs`: `lines 1-109` (`Derefer`, `PassPolicy::Required` at `100-108`).
  - `compiler/rustc_mir_transform/src/lib.rs`: `mir_built` trivial-const early exit (`395-408`), `mir_promoted` `debug_assert!(!tcx.is_trivial_const(def))` (`440`), `mir_for_ctfe` `debug_assert!(!tcx.is_trivial_const(def_id))` (`502`), `run_analysis_to_runtime_passes` (`608-637`), `run_analysis_cleanup_passes` (`642-656`), `run_runtime_lowering_passes` (`659-681`), `run_runtime_cleanup_passes` (`684-698`), `run_optimization_passes` (`700-789`, `LowerSliceLenCalls` at `718`).
  - `compiler/rustc_mir_transform/src/validate.rs`: `AscribeUserType`/`FakeRead` check (`296-311`), `ProjectionElem::OpaqueCast` rejection after `PostAnalysisNormalize` (`882-889`), `AggregateKind::RawPtr` runtime-only & mutability check (`1120-1129`), `UnOp::PtrMetadata` pointer/ref check (`1261-1267`).
  - `compiler/rustc_middle/src/mir/mod.rs`: `Body::typing_env` (`414-439`).
  - `compiler/rustc_middle/src/mir/syntax.rs`: `AnalysisPhase::PostCleanup` `Deref`-first invariant (`102-120`), `RuntimePhase::Initial` (`125-141`).
  - `compiler/rustc_middle/src/mir/statement.rs`: `ProjectionElem::is_indirect` (`263-275`), `Place::is_indirect` (`377-379`), `Place::is_indirect_first_projection` (`392-394`).
  - `compiler/rustc_const_eval/src/const_eval/eval_queries.rs`: `eval_trivial_const_using_ecx` (`146-160`), `eval_to_const_value_raw_provider` fast path (`377-379`), `eval_to_allocation_raw_provider` fast path (`468-473`).
  - `compiler/rustc_const_eval/src/interpret/step.rs`: `StatementKind::Intrinsic` (`116`), `write_aggregate` `AggregateKind::RawPtr` (`317-338`).
  - `compiler/rustc_const_eval/src/interpret/operator.rs`: `UnOp::PtrMetadata` calling `self.deref_pointer(val)?` (`499-513`).
  - `compiler/rustc_const_eval/src/interpret/place.rs`: `InterpCx::deref_pointer` (`468-538`).
  - `compiler/rustc_const_eval/src/interpret/cast.rs`: `CastKind::Transmute` size check and `copy_op_allow_transmute` (`192-218`).
  - `compiler/rustc_const_eval/src/interpret/intrinsics.rs`: `eval_nondiverging_intrinsic` (`869-890`).
  - `library/core/src/slice/mod.rs`: `#[lang = "slice_len_fn"] pub const fn len(&self) -> usize { ptr::metadata(self) }` (`112-120`).
  - `library/core/src/intrinsics/mod.rs`: signatures for `forget` (`815`), `offset` (`1163`), `slice_get_unchecked` (`1201-1208`), `read_via_copy` (`2291`), `write_via_move` (`2302`), `discriminant_value` (`2316`), `aggregate_raw_ptr` (`2998-3000`), `ptr_metadata` (`3008`).
- **`rust-lang/rust` comparison pins (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):**
  - Diffed directly across `lower_intrinsics.rs`, `lower_slice_len.rs`, `post_analysis_normalize.rs`, `trivial_const.rs`, `deref_separator.rs`, and `impossible_clauses.rs` (establishing all version deltas in Applicability and Finding 1).
- **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `2026-11-17`):**
  - `src/behavior-considered-undefined.md`: `r[undefined.pointer-access]` (`line 19`), `r[undefined.place-projection]` (`line 22`), `r[undefined.invalid]` (`line 59`), `r[undefined.dangling.def]` (`line 104`), `r[undefined.validity.const-provenance]` (`lines 171-173`).
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `2026-11-19`):**
  - `trusted/rustc-capture/src/driver.rs`: `COMPILER_VERSION` (`line 25`), `after_analysis` (`lines 75-84`).
  - `trusted/lean/Trusted/MirAst.lean`: `Operand::RuntimeChecks` rejection note (`36, 548-556`), `BinOp` (`381-409`), `UnOp` (`441-446`), `ProjectionElem` (`466-475`), `ConstLit` (`492-506`), `Rvalue` (`582-628`), `StatementKind` (`649-662`), `TerminatorKind.unreachable` (`752, 776`).
  - `trusted/lean/Trusted/MirSemantics.lean`: `evalUnOp` (`1177-1193`), `evalRvalue` (`1240-1313`), `evalTerminator` (`1537-1569`).

### 2. Preserved Package Support Material and Integrity Hashes

| Artifact | SHA-256 | Role & Verification Command |
| :--- | :--- | :--- |
| [`support/probe_lower_intrinsics_slice_len_and_trivial_const.py`](support/probe_lower_intrinsics_slice_len_and_trivial_const.py) | `381e55b58cb4ff275ada9b4a603992f36580ae663ce8e1d3eee16de6982c8086` | Self-contained differential probe running live `rustc` and `cargo miri` across all 6 experiment suites (trivial consts, 14-arm `LowerIntrinsics`, `LowerSliceLenCalls` at `-Zmir-opt-level=0` vs `1`, `PostAnalysisNormalize`/`CleanupPostBorrowck`, 7 `custom_mir`/const-index ICE & control cases, and 6 Miri runtime UB/round-trip cases). |
| [`support/probe_results.json`](support/probe_results.json) | `bedb3119889aa8aaadb8bd3ac324b5bc7ee3d50e6f4ce255de2eddb438566c45` | Complete captured output from `python3 support/probe_lower_intrinsics_slice_len_and_trivial_const.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` + `miri 0.1.0` (`x86_64-unknown-linux-gnu`), sanitized of ephemeral temp/host paths. |
| [`support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean`](support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean) | `c5893603cc43c3984f945896c3eda9aaaacbc5f39c4801bf86bccfbbf158cde7` | Standalone `2,310`-line (`95,047`-byte) Lean `v4.34.1` formalization with `45` user-declared theorems (`411` namespace environment theorems). Verified with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0` in `10.33s`), `0` warnings, `0` `._unsafe_rec` constants, `0` forbidden tokens, and `0` axioms outside `[propext, Quot.sound]`. |

### 3. Recorded Verification Commands and Observed Receipts

- **Live `rustc` & Miri differential probe:**
  ```console
  python3 support/probe_lower_intrinsics_slice_len_and_trivial_const.py
  ```
  Observed receipt: `exit 0`; `trivial_const` `compile_rc = 0` (`TRIV_A`/`TRIV_B`/`TRIV_C_CHAIN2`/`IMPOSSIBLE_CLAUSE_TRIV` = `1` dump each; `NON_TRIV_ARITH`/`NON_TRIV_GENERIC_REF`/`NON_TRIV_OPAQUE_DEF` = `49` dumps each); `impossible_clause_non_triv` `compile_rc = 1` (`E0080: entering unreachable code`, `49` dumps); `lower_intrinsics` `compile_rc = 0`; `lower_slice_len` `o0`/`o1` `compile_rc = 0`/`0`; `post_analysis_normalize` `compile_rc = 0`; `custom_mir_probes` `rc = 101` on all five negative cases (`indirect_slice_get_unchecked`, `const_index_slice_get_unchecked`, `field_proj_slice_get_unchecked_validate_mir`, `indirect_read_via_copy`, `indirect_discriminant_{no_validate,validate_mir}`) and `rc = 0` on `direct_slice_get_unchecked_control`; Miri `rc = 0` on `aggregate_raw_ptr_metadata_roundtrip` and `rc = 1` with expected UB diagnostics on all five negative Miri probes.
- **Lean `v4.34.1` kernel check & purity audit:**
  ```console
  LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
    "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
    -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean
  ```
  Observed receipt: `exit 0` (`real 10.334s`, `0` errors, `0` warnings); exhaustive Lean `Environment` audit reported `AUDIT_THEOREM_COUNT=411`, `AUDIT_UNSAFE_REC_COUNT=0`, `AUDIT_BAD_AXIOMS=0` (only `[]`, `[propext]`, `[propext, Quot.sound]`); source scan confirmed `0` occurrences of `sorry`, `admit`, `axiom`, `Classical`, `omega`, `bv_decide`, `native_decide`, `partial`, `unsafe`, `deriving`, and `_unsafe_rec`.

## Revalidation

Use the following narrow discriminating checks to revalidate this report against a newer `rust-lang/rust`, `joshlf/anneal`, or `leanprover/lean4` revision without repeating the full investigation:

1. **Diff the five governing `rustc_mir_transform` source files against `137d1d49458b73b7b85d2c1599d8730886d65e47`:**
   ```console
   git diff 137d1d49458b73b7b85d2c1599d8730886d65e47..<NEW_SHA> -- \
     compiler/rustc_mir_transform/src/lower_intrinsics.rs \
     compiler/rustc_mir_transform/src/lower_slice_len.rs \
     compiler/rustc_mir_transform/src/post_analysis_normalize.rs \
     compiler/rustc_mir_transform/src/trivial_const.rs \
     compiler/rustc_mir_transform/src/lib.rs
   ```
   Check specifically:
   - Whether new `sym::*` arms were added to `LowerIntrinsics::run_pass`, or whether `slice_get_unchecked` (`line 254`) and `discriminant_value` (`line 216`) were tightened from `!place.is_indirect()` / unguarded to `place.as_local()`, or whether `slice_get_unchecked` (`line 259`) learned to handle `Operand::Constant` indices.
   - Whether `LowerSliceLenCalls` (`lower_slice_len.rs:25`) replaced `as_mut_preserves_cfg()` with `as_mut()` (or invalidated CFG cache when dropping an `UnwindAction::Cleanup` edge), or whether `core::slice::<impl [T]>::len` gained `#[rustc_nounwind]`.
   - Whether `PostAnalysisNormalize` still strips `ProjectionElem::OpaqueCast` or whether `-Znext-solver=globally` became the default.
   - Whether `trivial_const` gained/dropped any guards (`has_impossible_clauses`, `opaque_types_defined_by`, `body.has_opaque_types()`, `AnonConstKind::NonTypeSystemInline`, `args.is_empty()`).
2. **Rerun the live `rustc` and Miri differential probe against any target nightly toolchain:**
   ```console
   python3 support/probe_lower_intrinsics_slice_len_and_trivial_const.py --out /tmp/reval_probe.json
   ```
   On any `rustc` revision $\ge$ `3ef0c22cdb86` (including `137d1d49458b`), expect **two deliberate improvements** relative to the `1.98.0-nightly` baseline in `support/probe_results.json`:
   - `probe_copy_nonoverlapping` and `probe_assume` after `LowerIntrinsics` will now emit `_0 = const ();` immediately after `copy_nonoverlapping(...)` / `assume(...)`.
   - `IMPOSSIBLE_CLAUSE_TRIV` will no longer exit `rc = 0` with `1` dump file; instead, `has_impossible_clauses` will reject the fast path, emitting `~49` dump files, rewriting its body to `bb0: { unreachable; }`, and failing CTFE with `error[E0080]: entering unreachable code` identically to `IMPOSSIBLE_CLAUSE_NON_TRIV`.
3. **Re-verify the standalone Lean proof artifact under a newer Lean 4 toolchain:**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/LowerIntrinsicsSliceLenAndTrivialConstSoundness.lean
   ```
   A clean `exit 0` confirms all `45` user-declared theorems continue to elaborate and kernel-check with zero warnings and zero `sorry`s; rerun the `#eval` environment check (confirming `AUDIT_UNSAFE_REC_COUNT=0` and `AUDIT_BAD_AXIOMS=0`) whenever upgrading Lean minor versions.
4. **Re-audit the Anneal TCB seam when `joshlf/anneal` updates `COMPILER_VERSION` or extends `Trusted/MirAst.lean` / `Trusted/MirSemantics.lean`:**
   Inspect `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, and `trusted/lean/Trusted/MirSemantics.lean` specifically when adding support for `UnOp.ptrMetadata` (confirming `deref_pointer` validity is enforced), `StatementKind::Intrinsic`, `Rvalue::Cast(Transmute)`, `AggregateKind::RawPtr`, or constant-item capture (confirming `tcx.is_trivial_const(def)` items route through `tcx.trivial_const(def)` rather than `mir_promoted`/`mir_for_ctfe`).
