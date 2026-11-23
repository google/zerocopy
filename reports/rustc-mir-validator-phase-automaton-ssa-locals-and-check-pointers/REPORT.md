# Phase-Indexed MIR Validation, SSA Local Discovery, and Raw-Pointer UB Instrumentation in `rustc`

## Summary

This report establishes primary-source, empirically tested, and constructively mechanized ground truth for three tightly coupled `rustc_mir_transform` subsystems—**`Validator`** (`validate.rs`), **`SsaLocals`** (`ssa.rs`), and **`check_pointers`** (`check_pointers.rs`, together with `CheckAlignment` and `CheckNull`)—across `rust-lang/rust` HEAD (`137d1d49458b73b7b85d2c1599d8730886d65e47`) and the executed `rustc 1.98.0-nightly` / Miri `0.1.0` toolchain (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), cross-referenced against the Rust Reference (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`) and Anneal's trusted MIR boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`).

Core conclusions to retain:

1. **`MirPhase` validation is monotonically strengthening on analysis-artifact bans and across the entire `Runtime` dialect, but NOT monotonically strengthening across the `Analysis -> Runtime` boundary—and `rustc`'s own doc comments disagree with `validate.rs` and `pass_manager.rs`:**
   - The 6-point total order `Built < Analysis(Initial) < Analysis(PostCleanup) < Runtime(Initial) < Runtime(PostCleanup) < Runtime(Optimized)` monotonically tightens all analysis-artifact bans, while `StatementKind::SetDiscriminant` and `AggregateKind::RawPtr` are forbidden before `Runtime(Initial)` and permitted at `>= Runtime(Initial)` (and pre-runtime `Subslice` ordering is lifted at `Runtime(Initial)`).
   - Contrary to `compiler/rustc_middle/src/mir/syntax.rs:104-143`, `validate.rs` enforces bans on `FakeRead`, `AscribeUserType`, `FalseEdge`, `FalseUnwind`, `Rvalue::Ref(_, Fake(_), _)`, non-first `ProjectionElem::Deref`, and `Box` derefs at `>= MirPhase::Runtime(RuntimePhase::Initial)` rather than `Analysis(PostCleanup)` or `Runtime(PostCleanup)`. Moreover, `pass_manager.rs:408` explicitly **skips** validation at the `Analysis(PostCleanup)` transition even under `-Zvalidate-mir=yes`, whereas `pass_manager.rs:409` runs `Validator` **unconditionally** (even without `-Zvalidate-mir=yes`) at the `Runtime(Optimized)` phase transition.
   - `StatementKind::Retag` no longer exists in either `14210df0e` or `137d1d49458b`; retagging is attached to `Rvalue::Use(Operand, WithRetag)`. `StatementKind::BackwardIncompatibleDropHint` is permitted in all phases by `validate.rs`.
   - `TerminatorKind::TailCall` ABI, return-type, and closure compatibility are **not** checked in `validate.rs` (`validate.rs:379, 1636-1639` hold empty `FIXME(explicit_tail_calls)` blocks); `validate.rs` enforces only the shared `Call | TailCall` checks (`Move` argument alignment/place shape, `#[rustc_force_inline]`, and `FnDef | FnPtr` callability).

2. **The `(src.is_cleanup, dst.is_cleanup, EdgeKind)` bipartite automaton enforces strict two-phase unwind path separation plus contracted cleanup-forest acyclicity:**
   - Only 3 of 8 `(src.is_cleanup, dst.is_cleanup, EdgeKind)` triples are valid: `(false, false, Normal)`, `(true, true, Normal)`, and `(false, true, Unwind)`. Combined with `START_BLOCK` (`bb0`) having `is_cleanup == false` and zero predecessors (`validate.rs:140-142`), every valid path from `bb0` stays in `is_cleanup == false` via `Normal` edges (Phase A), crosses at most one `Unwind` edge into `is_cleanup == true`, and stays permanently in `is_cleanup == true` via `Normal` edges (Phase B). Normal `Return` is restricted to Phase A; `UnwindResume` (additionally gated by `can_unwind`) and `UnwindTerminate` are restricted to Phase B.
   - When `unwind_edge_count > 1`, `CfgChecker::check_cleanup_control_flow` (`validate.rs:168-244`) contracts each reachable cleanup block to its highest cleanup dominator and enforces that the contracted graph is an out-degree-`<= 1` DAG (required for Windows MSVC SEH funclet lowering).
   - `#[custom_mir]` structurally enforces the `START_BLOCK` zero-predecessor rule at HIR name resolution because `rustc_mir_build/src/builder/custom/mod.rs:82-86` allocates `bb0` implicitly without binding it in `block_map`; the `validate.rs:140-142` check therefore guards against buggy MIR transformation passes rather than `custom_mir` inputs.

3. **`SsaLocals` soundness over shared borrows depends critically on `Ty::is_freeze`, reachable-only RPO traversal, `Move`-to-`Copy` neutralization, and union-find idempotence:**
   - `SsaLocals::new` (`ssa.rs:37-101`) must traverse `traversal::reverse_postorder(body)` (skipping unreachable blocks) because `Dominators::dominates` asserts `b.start != 0` (`dominators/mod.rs:384`) and panics on unreachable nodes.
   - `Rvalue::Ref(_, Shared, place)` records `local` in `borrowed_locals` via `PlaceContext::may_observe_address()`, preserving `Set1::One` iff `local_ty.is_freeze(tcx, typing_env)` (`ssa.rs:77-81`). Live differential execution and Miri (`-Zmiri-tree-borrows`) confirm `GVN` folds `x + 1` to `const 43_u32` across `touch_u32(&x)` for `u32: Freeze`, while demoting `Cell<u32>: !Freeze` to `Set1::Many` so `mutate_cell(&c)` produces `100`.
   - `SsaLocals` treats `Operand::Move` as a non-mutating read (`ssa.rs:247-250`). Because Miri and Anneal's `Trusted.MirSemantics` (`deinitMovedPlace = true`) deinitialize moved non-ZST storage, consumers such as `CopyProp` (`copy_prop.rs:128-135`) and `ReferencePropagation` (`ref_prop.rs:88-118`) must rewrite `Operand::Move` to `Operand::Copy` whenever unifying or reusing SSA locals.
   - In `compute_copy_classes` (`ssa.rs:296-361`), `RETURN_PLACE` (`_0`) cannot be renamed to a temporary, so `_0 = copy _t` re-roots `_t`'s entire equivalence class to `_0` iff `local_kind(head) == LocalKind::Temp` (refusing `LocalKind::Arg`). Crucially, this re-rooting sweep CAN move a single borrowed `Temp` into `_0`'s class when `_0` is unborrowed—explaining `copy_prop.rs:65-69` (`if local != head && borrowed_locals.contains(local)`). The true class invariant preserved across all iterations is **at most one borrowed local per copy class**, plus union-find idempotence (`copies[copies[x]] = copies[x]`), which is both sufficient and strictly necessary for the two-pass in-place `meet_copy_equivalence` loop (`ssa.rs:174-198`) to enforce exact class-wide conjunction.

4. **`check_pointers` (`CheckAlignment` and `CheckNull`) implements asymmetric field-projection and ZST policies via `BorrowedFieldProjectionMode`, preserves CFG validity via `UnwindAction::Unreachable`, and omits terminators:**
   - The upstream projection-mode enum in `check_pointers.rs:19-22` is `BorrowedFieldProjectionMode::{FollowProjections, NoFollowProjections}`. `CheckAlignment` uses `FollowProjections` with `excluded_pointees = [bool, i8, u8]` (notably excluding `u8` but *not* `()`), checking base-pointer alignment against field alignment on borrows (`&(*p).b` skips alignment checks for `u8` fields, while `(*p).b` checks `Pair::ALIGN`), justified by modular alignment equivalence on non-packed structs (`offset % align == 0 -> (addr % align == 0 <-> (addr + offset) % align == 0)`). `CheckNull` uses `NoFollowProjections`, gating non-borrow uses on `size_of::<T>() != 0` while unconditionally asserting non-null on `SharedBorrow | Borrow` (even for ZST `()`), emitting `AssertKind::NullReferenceConstructed` in `137d1d49458b` vs `AssertKind::NullPointerDereference` in `14210df0e`.
   - `check_pointers` splits blocks backwards with `UnwindAction::Unreachable` (`#[rustc_nounwind]` abort, observed as `SIGABRT` / exit `-6` at runtime) so failed UB checks never initiate unwinding into unsafe code.
   - Although `PointerFinder::should_visit_place` (`check_pointers.rs:182-198`) returns `true` for `MutatingUseContext::{Call, Yield, Drop}`, `check_pointers` (`check_pointers.rs:75-87`) only invokes `finder.visit_statement(statement, location)` and **never visits terminators**. Live `#[custom_mir]` testing confirms `Call(RET = sink(copy (*_1)))` passes `-Zvalidate-mir=yes` and receives zero instrumentation from both `CheckAlignment` and `CheckNull`.

5. **Constructive Lean 4 (`v4.34.1`) mechanization:**
   - `support/MirValidatorPhaseAutomatonAndSsaLocalsSoundness.lean` (2,253 lines, 842 module constants, 20 exported theorems) kernel-checks cleanly under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with `0` `sorryAx`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide` (`Lean.ofReduceBool`), `0` `partial def`, and `0` `._unsafe_rec` constants (axioms restricted strictly to `[propext, Quot.sound]`, with `[]` on pure constructive corollaries).

## Applicability

This report examines five durable upstream subjects and characterizes their exact technical relationships:

1. **Primary-source implementation authority (`rust-lang/rust` HEAD `137d1d49458b73b7b85d2c1599d8730886d65e47`, 2026-11-22):** All line numbers, function signatures, pass policies, and source audits in `## Findings` refer to this commit unless explicitly annotated as `14210df0e`.
2. **Executed compiler and Miri differential target (`rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`, `miri 0.1.0`, host `x86_64-unknown-linux-gnu`):** All live `rustc` ICE reproductions, `-Zdump-mir` outputs, native runtime executions, and `cargo miri run` (`MIRIFLAGS=-Zmiri-tree-borrows`) runs in `support/probe_results.json` were executed on this toolchain on `2026-11-23`. Section `### 6` explicitly records every source-level diff between `14210df0e` and `137d1d49458b` across `validate.rs`, `ssa.rs`, `check_pointers.rs`, `check_alignment.rs`, and `check_null.rs` so shared vs. version-specific behaviors remain strictly separated:
   - **Shared across `14210df0e` and `137d1d49458b`:** `ssa.rs` logic is 100% semantically identical (differing by a single `use rustc_middle::bug` -> `use rustc_span::bug` import); the 6-phase `MirPhase` lattice, `(is_cleanup, EdgeKind)` 3-of-8 transition matrix, `START_BLOCK` zero-predecessor rule, `check_cleanup_control_flow` dominator contraction, `TailCall` empty `FIXME` stub, `Rvalue::Use(_, WithRetag)` (absence of `StatementKind::Retag`), `validate_debuginfos`, `BorrowedFieldProjectionMode` semantics, `check_pointers` statement-only loop, and `UnwindAction::Unreachable` abort semantics are identical across both revisions.
   - **Specific to `137d1d49458b` (absent in `14210df0e`):** `PassPolicy::optional(...)` replacing `is_required() -> true` on `Validator`, `CheckAlignment`, and `CheckNull`; `CheckNull` emitting `AssertKind::NullReferenceConstructed` for borrows vs. `AssertKind::NullPointerDereference` for other uses; `check_pointers` replacing `split_block` with `basic_blocks.push_with`; and new `validate.rs` checks for `async drop` at `>= Runtime(Initial)`, `-Zvalidate-mir` pre-runtime `Call` `Move` non-local/non-box checks, `CastKind::BoxDerefTransmute`, `CoverageKind::is_removed_after_analysis()`, and `next_trait_solver_globally()` / `.ignoring_regions()` in `predicate_must_hold_modulo_regions`.
3. **Normative Rust language semantics (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, 2026-11-17):** Supplies the normative undefined-behavior and interior-mutability rules (`r[undefined.alias]`, `r[undefined.immutable]`, `r[undefined.misaligned.*]`, `r[undefined.dangling.*]`, `r[undefined.validity.reference-box]`, `r[interior-mut.unsafe-cell]`) that license `SsaLocals`'s `Freeze` assumption and `CheckAlignment`/`CheckNull`'s field-projection and ZST distinctions.
4. **Anneal trusted MIR verification boundary (`joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`, 2026-11-19):** Interpreted through `rustc`'s MIR invariants to map which `Validator` and `SsaLocals` assumptions are currently checked statically (`BodyStaticAdmitted`), enforced dynamically fail-closed (`Trusted.MirSemantics.evalStep`), or delegated to the capture driver (`trusted/rustc-capture/src/driver.rs`, pinned to `1.98.0-nightly (f8a08b688 2026-05-30)`).
5. **Mechanized soundness verification (`leanprover/lean4` `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`):** All theorems in `support/MirValidatorPhaseAutomatonAndSsaLocalsSoundness.lean` are standalone `Init`-only constructive proofs verifying formalized abstractions of `validate.rs`, `ssa.rs`, and `check_pointers.rs`; they do not import `joshlf/anneal`'s `Trusted.MirSemantics` or extract executable Rust compiler code.

Invocation modes relevant to empirical behavior:
- `Validator` checks gated by `tcx.sess.opts.unstable_opts.validate_mir` (`-Zvalidate-mir=yes`): per-pass validation in `pass_manager.rs:331, 382-384`, non-`Optimized` phase-change validation in `pass_manager.rs:403-408`, pre-runtime `Call` `Move` non-local/non-box check (`validate.rs:436-452`), and pre-runtime `Operand::Copy` `Copy`-trait check (`validate.rs:652-663`).
- `CheckAlignment` and `CheckNull` run when `ctx.ub_checks()` is true (enabled by default with `-C debug-assertions=on` or explicitly via `-Zub-checks=yes`) and `LangItem::PanicImpl` is present (`check_pointers.rs:62-64`).
- `GVN` and `CopyProp` (primary consumers of `SsaLocals`) are enabled at `mir_opt_level >= 2` (`GVN`) and `>= 1` (`CopyProp`, `copy_prop.rs:26`), with `ReferencePropagation` at `>= 2` (`ref_prop.rs:77`).

## Findings

### 1. `MirPhase` Linear Lattice, Pipeline Placement, and Documentation-vs-Code Discrepancies

Basis: source (`rust-lang/rust@137d1d49458b`, `14210df0e`) + documentation (`syntax.rs`) + execution (`V9`, `V10`, `V11`) + derived (Lean theorem `mirPhase_invariant_monotonicity`)

#### 1.1 Exact 6-Point `MirPhase` Total Order and Pipeline Transitions

In `compiler/rustc_middle/src/mir/syntax.rs:42-144`, `MirPhase` derives `PartialOrd, Ord` in variant-declaration order, yielding a 6-element total order:

```rust
pub enum MirPhase {
    Built,                  // rank 0
    Analysis(AnalysisPhase),// Initial = 0 (rank 1), PostCleanup = 1 (rank 2)
    Runtime(RuntimePhase),  // Initial = 0 (rank 3), PostCleanup = 1 (rank 4), Optimized = 2 (rank 5)
}
```

`compiler/rustc_mir_transform/src/pass_manager.rs:393-399` strictly enforces forward-only transitions:

```rust
if let Some(new_phase) = phase_change {
    if body.phase >= new_phase {
        panic!("Invalid MIR phase transition from {:?} to {:?}", body.phase, new_phase);
    }
    body.phase = new_phase;
    body.pass_count = 0;
```

The exact pass-manager pipeline in `compiler/rustc_mir_transform/src/lib.rs:395-789` drives a body through all six phases across four queries:

| Query / Stage | Source (`lib.rs`) | Entry Phase | Exit Phase | Validation Mode (`pass_manager.rs`) | Key Lowering / Cleanup Passes |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `mir_built` | `L395-433` | `Built` | `Built` | `run_passes` (`validate_each = true`; gated by `-Zvalidate-mir`) | `LintAndRemoveUninhabited`, MIR lints, `SimplifyCfg::Initial`, `SanityCheck` |
| `mir_promoted` | `L436-498` | `Built` | `Analysis(Initial)` | `run_passes` + phase-change validate if `-Zvalidate-mir` | `PromoteTemps`, `SimplifyCfg::PromoteConsts`, `InstrumentCoverage` |
| `run_analysis_cleanup_passes` | `L642-656` | `Analysis(Initial)` | `Analysis(PostCleanup)` | `run_passes` (`L651`) — **phase-change validate explicitly SKIPPED at `Analysis(PostCleanup)`** (`pass_manager.rs:408`); followed by `PostAnalysisNormalize` (`L655`) | `ImpossibleClauses`, `CleanupPostBorrowck`, `RemoveNoopLandingPads`, `SimplifyCfg::PostAnalysis`, `Derefer`, then `PostAnalysisNormalize` |
| `run_runtime_lowering_passes` | `L659-681` | `Analysis(PostCleanup)` | `Runtime(Initial)` | **`run_passes_no_validate`** (`validate_each = false` — skips per-pass AND phase-change validate!) | `CriticalCallEdges`, `Subtyper`, `ElaborateDrops`, `CheckDropRecursion`, `AbortUnwindingCalls`, `AddMovesForPackedDrops`, `EraseDerefTemps`, `ElaborateBoxDerefs`, `StateTransform`, `KnownPanicsLint` |
| `run_runtime_cleanup_passes` | `L684-698` | `Runtime(Initial)` | `Runtime(PostCleanup)` | `run_passes` (validates after `LowerIntrinsics`, `RemovePlaceMention`, `SimplifyCfg::PreOptimizations`, and phase change if `-Zvalidate-mir`) | `LowerIntrinsics`, `RemovePlaceMention`, `SimplifyCfg::PreOptimizations`; clears `decl.local_info = ClearCrossCrate::Clear` (`L695-697`) |
| `run_optimization_passes` | `L700-789` | `Runtime(PostCleanup)` | `Runtime(Optimized)` | `run_passes` + **UNCONDITIONAL phase-change validate at `Runtime(Optimized)`** (`pass_manager.rs:409`) | `CheckAlignment`, `CheckNull`, `CheckEnums`, `ForceInline`, `Inline`, `ReferencePropagation`, `SROA`, `GVN`, `SsaRangePropagation`, `CopyProp`, `DSE`, `DestinationPropagation`, `CriticalCallEdges` |

Notice two critical pass-manager subtleties established directly by `pass_manager.rs:403-413`:

1. **Why `Analysis(PostCleanup)` skips validation (`pass_manager.rs:406-408`):** Because `PostAnalysisNormalize` runs *after* the phase change to `Analysis(PostCleanup)` (`lib.rs:651-655`), opaque types have not yet been revealed at the moment `body.phase` flips to `Analysis(PostCleanup)`. Validation therefore skips the phase transition and runs after `PostAnalysisNormalize` instead (when `-Zvalidate-mir=yes`).
2. **Why `Runtime(Initial)` skips phase-change validation (`lib.rs:680` + `pass_manager.rs:237-244, 403`):** `run_runtime_lowering_passes` calls `pm::run_passes_no_validate(..., Some(MirPhase::Runtime(RuntimePhase::Initial)))`. Inside `run_passes_inner`, `validate_each` is `false`, so `validate = (false && ...) || (new_phase == Runtime(Optimized))` evaluates to **`false`**! The first validation after runtime lowering occurs only after `LowerIntrinsics` (if `-Zvalidate-mir=yes`, directly observed in Probe `V10`: `after pass LowerIntrinsics`), or unconditionally at `Runtime(Optimized)`.
3. **Unconditional validation at `Runtime(Optimized)` (`pass_manager.rs:409`):** Even when `-Zvalidate-mir` is **not** passed, `|| new_phase == MirPhase::Runtime(RuntimePhase::Optimized)` forces `Validator` to execute at the end of `run_optimization_passes`. Probe `V11` confirms this live on `14210df0e`: compiling `normal_to_cleanup` (`Goto(clean_bb)` where `clean_bb (cleanup) = { UnwindResume() }`) with **no** `-Zvalidate-mir` flag still triggers `broken MIR ... (after phase change to runtime-optimized)`. Strikingly, because `-Zvalidate-mir` was off during earlier passes, `SimplifyCfg` first merged `clean_bb`'s `UnwindResume` into non-cleanup `bb0`, transforming the original `(false, true, Normal)` edge violation into `Cannot UnwindResume from non-cleanup basic block` at `bb0[0]`.

#### 1.2 Complete Phase-Indexed Construct Matrix and Documentation-vs-Code Discrepancies

Direct audit of `validate.rs:89-97, 294-538, 650-1684` versus the doc comments in `compiler/rustc_middle/src/mir/syntax.rs:104-143` uncovers **seven concrete discrepancies** where the `syntax.rs` documentation claims an earlier or later phase boundary than `validate.rs` actually implements:

| MIR Construct | Documented Phase in `syntax.rs` | Enforced Phase in `validate.rs` (HEAD `137d1d49458b`) | Monotonicity Class | Source Lines (`validate.rs`) |
| :--- | :--- | :--- | :--- | :--- |
| `StatementKind::FakeRead` | Disallowed `>= Analysis(PostCleanup)` (`L107`) | **Disallowed `>= Runtime(Initial)`** (doc/code mismatch!) | Monotone ban | `L304-311`, `L1517-1524` |
| `StatementKind::AscribeUserType` | Disallowed `>= Analysis(PostCleanup)` (`L108`) | **Disallowed `>= Runtime(Initial)`** (doc/code mismatch!) | Monotone ban | `L296-303`, `L1509-1516` |
| `StatementKind::Coverage(kind)` (`Point`, `BlockMarker`) | Disallowed `>= Analysis(PostCleanup)` (`L109`) | Disallowed `>= Analysis(PostCleanup)` iff `kind.is_removed_after_analysis()` (`coverage.rs:123-128`; `VirtualCounter` stays allowed) | Monotone ban | `L317-326` |
| `StatementKind::SetDiscriminant` | Allowed `>= Runtime(Initial)` (`L135`) | **Disallowed `< Runtime(Initial)`**; allowed `>= Runtime(Initial)` (ADTs, coroutines, opaques) | Dialect-introduced (non-monotone across `Analysis -> Runtime`) | `L312-316`, `L1568-1586` |
| `StatementKind::BackwardIncompatibleDropHint` | Semantically `Nop` (`syntax.rs:449-456`) | **Allowed in all phases** (no phase check) | Always allowed | `L333`, `L1592` |
| `StatementKind::Retag` | Removed from `StatementKind` (`syntax.rs:490, 1369`) | **No longer exists**; replaced by `Rvalue::Use(Operand, WithRetag)` (no phase ban) | Removed / superseded | `L1027` (`Rvalue::Use(_, _) => {}`) |
| `Rvalue::CopyForDeref` | Disallowed `>= Runtime(Initial)` (`L130`) | Disallowed `>= Runtime(Initial)` | Monotone ban | `L1028-1032` |
| `Rvalue::Ref(_, BorrowKind::Fake(_), _)` | Disallowed `>= Analysis(PostCleanup)` (`L110`) | **Disallowed `>= Runtime(Initial)`** (doc/code mismatch!) | Monotone ban | `L1157-1164` |
| `CastKind::PointerCoercion(MutToConstPointer \| ArrayToPointer)` | Disallowed `>= Analysis(PostCleanup)` (`L111-113`) | Disallowed `>= Analysis(PostCleanup)` | Monotone ban | `L1314-1345` |
| `AggregateKind::RawPtr` | Not listed in `MirPhase` docs | **Allowed ONLY in `MirPhase::Runtime(_)`** (`>= Runtime(Initial)`) | Dialect-introduced | `L1115-1121` |
| `ProjectionElem::Deref` at index `>= 1` | Disallowed `>= Analysis(PostCleanup)` (`L117-118`) | **Disallowed `>= Runtime(Initial)`**, with explicit exemption for `NonUseContext::VarDebugInfo` (doc/code mismatch!) | Monotone ban | `L956-965` |
| `ProjectionElem::Deref` of `Box<T>` | Disallowed `>= Runtime(PostCleanup)` (`L140-142`) | **Disallowed `>= Runtime(Initial)`** after `ElaborateBoxDerefs` (doc/code mismatch! Confirmed live by `V10`) | Monotone ban | `L676-684` |
| `ProjectionElem::OpaqueCast` | Disallowed `>= Runtime(Initial)` (`L131`) | Disallowed `>= Runtime(Initial)` | Monotone ban | `L882-889` |
| `ProjectionElem::Downcast` not immediately followed by `Field` | Not phase-specific | **Disallowed in ALL phases** | Phase-invariant | `L968-980` |
| `ConstantIndex` or `Subslice` after `Subslice` | Allowed `>= Runtime(Initial)` (`L136`) | **Disallowed `< Runtime(Initial)`**; allowed `>= Runtime(Initial)` | Pre-runtime only (relaxed at `Runtime`) | `L996-1013` |
| `LocalInfo::DerefTemp` | Disallowed `>= Runtime(Initial)` (`L132`) | Disallowed `>= Runtime(Initial)`; pre-runtime must be dereferenceable and only dereferenced or assigned via `CopyForDeref` | Monotone ban | `L982-994`, `L1501-1507`, `L1669-1681` |
| `TerminatorKind::FalseEdge` / `FalseUnwind` | Disallowed `>= Analysis(PostCleanup)` (`L105-106`) | **Disallowed `>= Runtime(Initial)`** (doc/code mismatch!) | Monotone ban | `L479-498` |
| `TerminatorKind::Yield` / `CoroutineDrop` | Disallowed `>= Runtime(Initial)` (`L128-129`) | Disallowed `>= Runtime(Initial)` (and always banned outside coroutines) | Monotone ban | `L467-478`, `L505-515` |
| `TerminatorKind::Drop { drop: Some(_), .. }` (`async drop`) | Mentioned in `MirPhase::Runtime` prose (`L81-82`) | Disallowed `>= Runtime(Initial)` (HEAD `137d1d49458b`; absent in `14210df0e`) | Monotone ban | `L367-375` |
| Critical `Call` edge (`predecessors[target].len() > 1` with `Cleanup`/`Terminate` unwind) | Not listed in `syntax.rs` | Disallowed `>= Runtime(Optimized)` | Monotone ban | `L277-281`, `L391-401` |
| Un-inlined `#[rustc_force_inline]` `Call` / `TailCall` | Not listed in `syntax.rs` | Disallowed `>= Runtime(Optimized)` | Monotone ban | `L456-461` |
| `Operand::Copy` of non-`Copy` type | Allowed `>= Runtime(Initial)` (`L138`) | Disallowed `< Runtime(Initial)` **only when `-Zvalidate-mir`** | Pre-runtime only | `L652-663` |
| `Call`/`TailCall` `Move` of non-local, non-`Box` place | Not listed in `syntax.rs` | Disallowed `< Runtime(Initial)` **only when `-Zvalidate-mir`** (HEAD `137d1d49458b`) | Pre-runtime only | `L436-452` |
| `body.has_free_regions()` on `InstanceKind::Item(_)` | Not listed in `syntax.rs` | Disallowed in `MirPhase::Runtime(_)` (`>= Runtime(Initial)`) | Monotone ban | `L89-97` |
| `mir_assign_valid_types` variance | Subtyping explicit after borrowck | `Variance::Covariant` (`< Runtime(Initial)`) -> **`Variance::Invariant` (`>= Runtime(Initial)`)** | Monotone tightening | `L609-617` |

**Mechanized consequence (`mirPhase_invariant_monotonicity`):** Separating monotone-ban predicates from dialect-introduced constructs resolves a common misconception. Across the full 6-point lattice (`p <= q`), **only** the monotone-ban fragment satisfies `Valid(q) => Valid(p)` (`SetDiscriminant` and `AggregateKind::RawPtr` break global monotonicity at `Analysis(PostCleanup) -> Runtime(Initial)`, witnessed by `dialect_boundary_witnesses`). Within the `Runtime` dialect (`Runtime(Initial) <= p <= q`), however, **every** `Validator` phase predicate tightens monotonically: `FullValidAt q body -> FullValidAt p body`.

#### 1.3 `TerminatorKind::TailCall` Validation Reality (`validate.rs:377-462, 1623-1640`)

Primary-source inspection of `validate.rs` refutes the assumption that `Validator` enforces `TailCall` ABI or return-type signature compatibility. Both `CfgChecker` and `TypeChecker` handle `TailCall` in shared arms with `Call` and contain explicit unimplemented `FIXME` blocks:

- `validate.rs:377-379` (`CfgChecker`):
  ```rust
  TerminatorKind::Call { func, args, .. }
  | TerminatorKind::TailCall { func, args, .. } => {
      // FIXME(explicit_tail_calls): refactor this & add tail-call specific checks
  ```
  `CfgChecker` skips the `Call`-only block (`L380-417`: destination packedness, target edge, unwind edge, critical edge), and applies to `TailCall` ONLY: (i) `Operand::Move` argument packed-place check (`L420-432`), (ii) `-Zvalidate-mir` pre-runtime `Move` non-local/non-box check (`L436-452`), and (iii) `#[rustc_force_inline]` un-inlined check at `>= Runtime(Optimized)` (`L456-461`).
- `validate.rs:1623-1640` (`TypeChecker`):
  ```rust
  TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
      let func_ty = func.ty(&self.body.local_decls, self.tcx);
      match func_ty.kind() {
          ty::FnPtr(..) | ty::FnDef(..) => {}
          _ => self.fail(...),
      }
      if let TerminatorKind::TailCall { .. } = terminator.kind {
          // FIXME(explicit_tail_calls): implement tail-call specific checks here (such
          // as signature matching, forbidding closures, etc)
      }
  }
  ```
  Consequently, any MIR transformation pass or custom MIR producer that constructs or mutates `TerminatorKind::TailCall` with mismatched ABIs, mismatched return types, or closure callees will **not** be caught by `validate.rs` in either `14210df0e` or `137d1d49458b`.

---

### 2. Bipartite `(is_cleanup, EdgeKind)` Unwind Automaton, `START_BLOCK` Ban, and Contracted Cleanup Forest

Basis: source (`validate.rs:25-275, 516-537`, `rustc_mir_build/src/builder/custom/mod.rs:82-86`, `library/core/src/intrinsics/mir.rs`) + execution (`V1`–`V8`, `V11`, `V12`) + derived (Lean theorems `validEdgeTransition_exact_3_of_8`, `start_block_unreachable_after_step`, `cleanup_sticky_under_valid_edges`, `cleanup_automaton_path_separation`, `nounwind_path_cannot_resume`, `cleanup_contraction_unique_root`)

#### 2.1 Exact 3-of-8 `(src.is_cleanup, dst.is_cleanup, EdgeKind)` Transition Matrix

`CfgChecker::check_edge` (`validate.rs:139-166`) enforces two structural invariants on every CFG edge `(src, dst, edge_kind)`:
1. **`START_BLOCK` zero-predecessor rule (`L140-142`):** `if bb == START_BLOCK { self.fail(location, "start block must not have predecessors") }`.
2. **Bipartite cleanup transition matrix (`L145-162`):**

| `src.is_cleanup` | `dst.is_cleanup` | `EdgeKind` | Valid in `validate.rs`? | Exact Diagnostic / Live Probe |
| :---: | :---: | :--- | :---: | :--- |
| `false` | `false` | `Normal` | **VALID** | Standard normal control flow |
| `true` | `true` | `Normal` | **VALID** | Intra-cleanup / cleanup-chaining control flow |
| `false` | `true` | `Unwind` | **VALID** (`unwind_edge_count += 1`) | Entering a cleanup landing pad on panic |
| `false` | `true` | `Normal` | **INVALID** | `Normal edge to ... violates unwind invariants (cleanup false -> true)` (Probe `V2`, `rc=101`) |
| `true` | `false` | `Normal` | **INVALID** | `Normal edge to ... violates unwind invariants (cleanup true -> false)` (Probe `V3`, `rc=101`) |
| `false` | `false` | `Unwind` | **INVALID** | `Unwind edge to ... violates unwind invariants (cleanup false -> false)` (Probe `V4`, `rc=101`) |
| `true` | `false` | `Unwind` | **INVALID** | Rejected both by `check_unwind_edge` (`UnwindAction::Cleanup in cleanup block`) and `check_edge` |
| `true` | `true` | `Unwind` | **INVALID** | Rejected first by `check_unwind_edge` (`UnwindAction::Cleanup in cleanup block`, Probe `V5`, `rc=101`) and by `check_edge` |

Additionally, `CfgChecker::check_unwind_edge` (`validate.rs:246-275`) and `visit_terminator` (`L516-537`) govern `UnwindAction` and exit terminators under the `can_unwind` gate (`L47-65`):

- **`can_unwind` computation (`validate.rs:47-65`):**
  - `true` whenever `body.phase <= MirPhase::Runtime(RuntimePhase::Initial)` (because `AbortUnwindingCalls` runs inside `run_runtime_lowering_passes` before `Runtime(Initial)` completes, and validation at `<= Runtime(Initial)` allows un-aborted unwinds), OR `!tcx.def_kind(def_id).is_fn_like()`.
  - Otherwise (`> Runtime(Initial)` on fn-like items), `ty::layout::fn_can_unwind(tcx, Some(def_id), body_abi)`, where `Closure`/`CoroutineClosure` map to `ExternAbi::RustCall`, `Coroutine` maps to `ExternAbi::Rust`, `FnDef` uses `body_ty.fn_sig_abi(tcx)`, and `ty::Error(_)` returns early (skipping all validation).
- **`UnwindAction` legality (`validate.rs:246-275`):**
  - `UnwindAction::Cleanup(target)`: requires `!is_cleanup`, then checks `(false, dst.is_cleanup, EdgeKind::Unwind)`.
  - `UnwindAction::Continue`: requires `!is_cleanup` AND `can_unwind`.
  - `UnwindAction::Terminate(UnwindTerminateReason::InCleanup)`: requires `is_cleanup == true` (Probe `V12` confirms ICE in non-cleanup block!).
  - `UnwindAction::Unreachable` and `UnwindAction::Terminate(UnwindTerminateReason::Abi)`: allowed in **both** `is_cleanup == false` and `is_cleanup == true` blocks regardless of `can_unwind`.
- **Exit-terminator separation (`validate.rs:516-537`):**
  - `TerminatorKind::Return`: requires `!is_cleanup` (Probe `V6`, `rc=101`).
  - `TerminatorKind::UnwindResume`: requires `is_cleanup == true` AND `can_unwind == true` (Probe `V7` on `extern "C" fn` at `Runtime(PostCleanup)`, `rc=101`; Probe `V11` for non-cleanup block).
  - `TerminatorKind::UnwindTerminate(_)`: requires `is_cleanup == true`.
  - `TerminatorKind::Unreachable`: allowed anywhere.

**Mechanized separation property (`cleanup_automaton_path_separation`):** Any valid path `0 ->* dst` with edge-kind trace `ks` decomposes into Phase A (`is_cleanup == false`, `AllNormal ks`, `countUnwind ks == 0`) followed by at most one `Unwind` edge into Phase B (`is_cleanup == true`, `ks = ks₁ ++ [.unwind] ++ ks₂` with `AllNormal ks₁` and `AllNormal ks₂`, `countUnwind ks == 1`). No path can cross `Unwind` twice, no cleanup path can ever reach `Return`, and when `can_unwind == false` no reachable block can ever exit via `UnwindResume` (`nounwind_path_cannot_resume`).

#### 2.2 Why `START_BLOCK` Predecessors Are Structurally Unrepresentable in `#[custom_mir]`

In `compiler/rustc_mir_build/src/builder/custom/mod.rs:82-86`:
```rust
// Single `false` for entry block which is declared implicitly
block_decls: indexvec![false],
local_map: FxHashMap::default(),
block_map: FxHashMap::default(),
```
And in `library/core/src/intrinsics/mir.rs` (`__internal_declare_basic_blocks`), the `mir!` macro binds identifiers (`let $name = BasicBlock::{Normal, Cleanup};`) **only** for subsequent named blocks (`bb1 = { ... }`), never for the implicit entry block `{ ... }` (`bb0`). Consequently:
1. `#[custom_mir]` structurally enforces both `START_BLOCK.is_cleanup == false` and zero predecessors to `START_BLOCK` at HIR name resolution: writing `Goto(bb0)` fails with `error[E0425]: cannot find value bb0 in this scope` before MIR construction or validation runs (confirmed by Probe `V1`, `rc=1`, `has_broken_mir=false`).
2. `validate.rs:140-142` (`if bb == START_BLOCK`) is therefore an internal compiler-pass invariant guarding against MIR optimization passes (such as CFG threading or block merging) directly mutating `TerminatorKind` target indices to `BasicBlock::ZERO`.

#### 2.3 Contracted Cleanup Forest Invariant (`check_cleanup_control_flow`, `validate.rs:168-244`)

When a body has `self.unwind_edge_count > 1` (`validate.rs:169`), `CfgChecker::check_cleanup_control_flow` computes `body.basic_blocks.dominators()` and contracts every reachable cleanup block `bb` to `get_post_contract_node(bb)`: the unique highest cleanup ancestor in the dominator tree whose immediate dominator has `is_cleanup == false` (`L176-192`). Over all reachable cleanup blocks `bb` and every successor `s` of `bb` with `get_post_contract_node(s) != get_post_contract_node(bb)`:
1. **Out-degree `<= 1` (`L205-220`):** Each contracted cleanup root `r` may record at most ONE distinct contracted successor `parent[r] = Some(s)`. Finding two distinct contracted targets `s != e` triggers `"Cleanup control flow violation: The blocks dominated by {:?} have edges to both {:?} and {:?}"`.
2. **Acyclicity (`L224-243`):** Following `parent` pointers destructively (`parent.take()`) must never revisit a contracted root on the current DFS stack; cycles trigger `"Cleanup control flow violation: Cycle involving edge {bb:?} -> {parent:?}"`.

Probe `V8` confirms this live on `14210df0e` with three unwind pads (`clean_a`, `clean_b`, `clean_c`) where `clean_a` branches via `SwitchInt` to both `clean_b` and `clean_c`: `Validator` rejects it with `Cleanup control flow violation: The blocks dominated by bb4 have edges to both bb6 and bb5` (`rc=101`). Mechanically (`cleanup_contraction_unique_root`), out-degree `<= 1` plus acyclicity guarantees every contracted cleanup region terminates deterministically at a single unique root (required by MSVC Windows SEH funclet tables, which cannot represent arbitrary diverging or cyclic inter-funclet transfers).

#### 2.4 Live `Validator` Probe Matrix (`rustc 1.98.0-nightly`, `14210df0e`)

| Probe ID | Violation Constructed | Flags | Exit Code | `broken MIR`? | Observed Diagnostic Summary |
| :--- | :--- | :--- | :---: | :---: | :--- |
| `V1` | `Goto(bb0)` in `#[custom_mir]` | `-Zvalidate-mir=yes` | `1` | `false` | `error[E0425]: cannot find value bb0 in this scope` (structural `mir!` prevention) |
| `V2` | `(false, true, Normal)` (`Goto(clean_bb)`) | `-Zvalidate-mir=yes` | `101` | `true` | `Normal edge to ... violates unwind invariants (cleanup false -> true)` |
| `V3` | `(true, false, Normal)` (`Goto(ok_bb)` in cleanup) | `-Zvalidate-mir=yes` | `101` | `true` | `Normal edge to ... violates unwind invariants (cleanup true -> false)` |
| `V4` | `(false, false, Unwind)` (`UnwindCleanup(normal)`) | `-Zvalidate-mir=yes` | `101` | `true` | `Unwind edge to ... violates unwind invariants (cleanup false -> false)` |
| `V5` | `UnwindCleanup` inside a cleanup block | `-Zvalidate-mir=yes` | `101` | `true` | `` `UnwindAction::Cleanup` in cleanup block `` |
| `V6` | `Return()` inside a cleanup block | `-Zvalidate-mir=yes` | `101` | `true` | `` Cannot `Return` from cleanup basic block `` |
| `V7` | `UnwindResume()` in `extern "C"` fn (`Runtime(PostCleanup)`) | `-Zvalidate-mir=yes` | `101` | `true` | `` Cannot `UnwindResume` in a function that cannot unwind `` |
| `V8` | Cleanup diamond (`clean_a -> {clean_b, clean_c}`, 3 unwind edges) | `-Zvalidate-mir=yes` | `101` | `true` | `Cleanup control flow violation: The blocks dominated by bb4 have edges to both bb6 and bb5` |
| `V9` | `Runtime(Optimized)` nested deref (`*(*p)`) | `-Zvalidate-mir=yes` | `101` | `true` | `place (*(*_1)) has deref as a later projection (it is only permitted as the first projection)` |
| `V10` | `Runtime(Initial)` `Box<u32>` deref (`*b`) | `-Zvalidate-mir=yes` | `101` | `true` | `std::boxed::Box<u32> dereferenced after ElaborateBoxDerefs` (fires `after pass LowerIntrinsics`) |
| `V11` | Same broken body as `V2` **WITHOUT** `-Zvalidate-mir` | *(none)* | `101` | `true` | `` Cannot `UnwindResume` from non-cleanup basic block `` (`after phase change to runtime-optimized`) |
| `V12` | `UnwindTerminate(InCleanup)` in non-cleanup block | `-Zvalidate-mir=yes` | `101` | `true` | `` `UnwindAction::Terminate(InCleanup)` in a non-cleanup block `` |

---

### 3. `TypeChecker`, `ObligationCtxt` Trait Checking, `validate_debuginfos`, and Fail-Open Bypasses

Basis: source (`validate.rs:36-98, 125-137, 561-1712`, `rustc_mir_dataflow/src/debuginfo.rs`)

#### 3.1 Structural Split Between `CfgChecker` and `TypeChecker`

`validate.rs:105-110` and `556-576` separate validation into two visitors specifically because the MIR inliner invokes `validate_types(tcx, typing_env, body, caller_body)` directly when instantiating generic parameters:
- **`CfgChecker`** (`L111-554`) checks substitution-stable CFG, statement, terminator, local-bounds, and source-scope properties.
- **`TypeChecker`** (`L561-1685`) checks type-dependent invariants (returning `Vec<(Location, String)>` rather than immediately ICEing, allowing the MIR inliner to bail out cleanly on ambiguous where-clauses or rigid projections):
  1. **Assignment and projection type relation (`mir_assign_valid_types`, `L593-618`):** Fast-paths `src == dest`; **skips validation (`return true`) whenever `(src, dest).has_opaque_types()`**; then calls `crate::util::relate_types(tcx, typing_env, variance, src, dest)` with `Variance::Invariant` for `body.phase >= Runtime(Initial)` (after `Subtyper` inserts explicit `CastKind::Subtype`) and `Variance::Covariant` earlier. As its own comment notes (`L592`), this check is intentionally incomplete and accepts some incorrect assignments.
  2. **`ObligationCtxt` predicate check (`predicate_must_hold_modulo_regions`, `L621-646`):** Builds an inference context (`tcx.infer_ctxt().ignoring_regions().build_with_typing_env(self.typing_env)` in `137d1d49458b`), registers a single `Obligation`, and checks `ocx.evaluate_obligations_error_on_ambiguity().no_errors()`. In `validate.rs`, this helper has **exactly one caller**: `CastKind::PointerCoercion(PointerCoercion::Unsize, _)` (`L1346-1359`), verifying `CoerceUnsized` holds modulo regions. Under the legacy trait solver (`!tcx.next_trait_solver_globally()`), opaque types bypass the check (`return true`, `L632-634`).
  3. **Projection typing & bans (`L668-912`):**
     - `Field(f, ty)`: bans projecting fields of `LangItem::DynMetadata` and `#[repr(simd)]` types (`adt_def.can_project_fields`, MCP#838, `L719-732`); checks field bounds and `mir_assign_valid_types(ty, f_ty)` across tuples, `Pat`, ADTs, closures, coroutine-closures, and coroutines (handling `caller_body.coroutine_layout_raw()` to avoid query cycles during coroutine construction, `L757-812`).
     - `Index(idx)`: base must be `Array | Slice`, index must be `usize`.
     - `ConstantIndex { offset, min_length, from_end }`: arrays forbid `from_end`; enforces `offset <= min_length` (when `from_end`) and `offset < min_length` (otherwise).
     - `Subslice { from, to, from_end }`: arrays forbid `from_end`, slices require `from_end`, and `!from_end` requires `from <= to`.
     - `UnwrapUnsafeBinder` / `Rvalue::WrapUnsafeBinder`: validates `ty::UnsafeBinder` wrapping/unwrapping modulo erased regions (`L890-908, 1461-1477`).
  4. **Cast & `BinOp` / `UnOp` / `SwitchInt` checks (`L1166-1455, 1601-1622`):**
     - `CastKind::PointerWithExposedProvenance` and `CastKind::PointerExposeProvenance` have empty validation arms (`// FIXME: Add Checks for these`, `L1273-1274`).
     - `CastKind::Transmute | CastKind::BoxDerefTransmute` (`L1404-1445`): requires both normalized operand and target types to be `Sized` (does *not* check equal byte size — unequal sizes are well-formed MIR and UB only if executed); `BoxDerefTransmute` additionally requires `target_type.is_raw_ptr()`.
     - `CastKind::Subtype` (`L1446-1453`): invokes `util::sub_types(tcx, typing_env, op_ty, *target_type)`.
     - `SwitchInt` (`L1601-1622`): checks every branch discriminant fits in `ScalarInt::try_from_uint(value, size)` (1 bit for `bool`, 32 for `char`, target-normalized bit width for `Int`/`Uint`).
  5. **`VarDebugInfo` checks (`L914-950`):** Composite fragments forbid `union`/`enum` types, empty projections, or non-`Field` projections; place values require every element to satisfy `p.can_use_in_debuginfo()`.

#### 3.2 `validate_debuginfos` (`validate.rs:1687-1712`, `rustc_mir_dataflow/src/debuginfo.rs`)

`validate_debuginfos(body)` first calls `debuginfo_locals(body)`, which visits every `body.var_debug_info` entry and collects every referenced `Local` into a `DenseBitSet<Local>`. `DebuginfoChecker` then visits every `StmtDebugInfo` attached to statements and `after_last_stmt_debuginfos`:
- Both `StmtDebugInfo::AssignRef(local, _)` and `StmtDebugInfo::InvalidAssign(local)` must satisfy `self.debuginfo_locals.contains(local)`. Any orphaned per-statement debuginfo targeting a local absent from `body.var_debug_info` fails validation with `"{local:?} is not in debuginfo"`.

#### 3.3 Explicit Fail-Open Bypasses in `Validator`

Downstream verifiers assuming `Validator` guarantees invariants on every MIR body must account for three fail-open early exits:
1. `InstanceKind::Intrinsic(..) | InstanceKind::Virtual(..)` skip `Validator::run_pass` completely (`validate.rs:42-44`).
2. `ty::Error(_)` bodies return early at `validate.rs:60`.
3. `CfgChecker::fail` suppresses all `span_bug!` reports whenever `self.tcx.dcx().has_errors().is_some()` (`validate.rs:127`).

---

### 4. `SsaLocals`: `Set1` Dominance, Reachability Guard, `Freeze` Shared-Borrow Soundness, and Copy Classes

Basis: normative (`rust-lang/reference@c9cc32825b03`, `r[undefined.alias]`, `r[interior-mut.unsafe-cell]`) + source (`ssa.rs:1-455`, `rustc_middle/src/mir/mod.rs:1676-1704`, `rustc_middle/src/mir/visit.rs:1411-1446`, `dominators/mod.rs:378-403`, `copy_prop.rs:1-194`, `gvn.rs:124-550`, `ref_prop.rs:73-395`) + execution (`S1`, `S2`, `S3` including Miri `-Zmiri-tree-borrows`) + derived (Lean theorems `ssaLocals_freeze_shared_borrow_value_sound`, `ssaLocals_nonFreeze_counterexample`, `ssaLocals_move_deinit_counterexample`, `computeCopyClasses_soundness`, `meetCopyEquivalence_uniform_iff_all_copies`, `meetCopyEquivalence_requires_idempotence`)

#### 4.1 `Set1<DefLocation>` Dominance and Mandatory Reachable-Only RPO Traversal

`SsaLocals` (`compiler/rustc_mir_transform/src/ssa.rs:20-101`) identifies locals assigned at most once (`Set1::One(DefLocation)`) whose unique definition dominates every reachable use:

```rust
pub enum DefLocation {
    Argument,
    Assignment(Location),
    CallReturn { call: BasicBlock, target: Option<BasicBlock> },
}
```

`DefLocation::dominates` (`compiler/rustc_middle/src/mir/mod.rs:1684-1703`) defines:
- `Argument` -> always `true`.
- `Assignment(def)` -> `def.successor_within_block().dominates(location, dominators)` (strictly after `def` in the same block, or `dominators.dominates(def.block, location.block)` across blocks).
- `CallReturn { target: None, .. }` -> always `false` (diverging call never writes its return place).
- `CallReturn { call, target: Some(target) }` -> `call != target && dominators.dominates(call, target) && dominators.dominates(target, location.block)` (the definition happens on the `call -> target` edge, which dominates `location` iff `call` strictly dominates `target` and `target` dominates `location.block`).

**Why unreachable blocks MUST be skipped (`ssa.rs:64-67` + `dominators/mod.rs:378-388`):**
In `compiler/rustc_data_structures/src/graph/dominators/mod.rs:378-388`, `Dominators::dominates(a, b)` for non-path graphs (`Kind::General(g)`) executes:
```rust
let a = g.time[a];
let b = g.time[b];
assert!(b.start != 0, "node {b:?} is not reachable");
a.start <= b.start && b.finish <= a.finish
```
Unreachable basic blocks retain discovery timestamp `start == 0`, so calling `dominates` on any use inside an unreachable block immediately panics (ICE). `SsaLocals::new` prevents this by driving `SsaVisitor` over `traversal::reverse_postorder(body)` (`ssa.rs:65-67`), which yields **two** simultaneous guarantees:
1. Only blocks reachable from `START_BLOCK` are visited, keeping `Dominators::dominates` panic-free (verified empirically by Probe `S3`: a `#[custom_mir]` body containing an unreachable block with assignments and reads compiles cleanly at `-Zmir-opt-level=2 -Zvalidate-mir=yes`, `rc=0`).
2. For any SSA local whose single definition dominates all its uses, reverse postorder visits the defining block before every dominated use block, so `visitor.assignments[local]` is already `Set1::One(def)` when `check_dominates` runs—and `visitor.assignment_order` records SSA definitions in topological dominance order for single-pass downstream consumers (`GVN`, `compute_copy_classes`).

#### 4.2 `PlaceContext::may_observe_address`, `Deref` Exemption, and `Ty::is_freeze` Shared-Borrow Soundness

`SsaVisitor` (`ssa.rs:227-293`) classifies every place occurrence using three distinct paths:

1. **Direct assignment LHS (`ssa.rs:256-278`):** `MutatingUse(Store)` on a bare local inserts `DefLocation::Assignment(loc)`; `MutatingUse(Call)` on a bare local inserts `DefLocation::CallReturn { call, target }`. On the first insert (`Set1::Empty -> Set1::One`), `local` is appended to `assignment_order`; any second insert transitions `Set1::One -> Set1::Many`.
2. **Indirect first projection `(*local)...` (`ssa.rs:279-287`):** When `place.projection.first() == Some(&PlaceElem::Deref)` and `ctxt.is_use()`, `SsaVisitor` does **not** treat a store `*ptr = val` as mutating `ptr` itself: it visits the projection with `NonMutatingUse(Copy)` and calls `check_dominates(place.local, loc)` without incrementing `direct_uses[place.local]`. This enables `ReferencePropagation` (`ref_prop.rs:361-375`) to identify pointer locals whose `num_direct_uses(local) == 0` (used solely through `*local`).
3. **All other places (`ssa.rs:228-253, 289-291`):** `visit_local` first executes:
   ```rust
   if ctxt.may_observe_address() {
       self.borrowed_locals.insert(local);
   }
   ```
   where `PlaceContext::may_observe_address()` (`rustc_middle/src/mir/visit.rs:1411-1425`) returns `true` for:
   - `NonMutatingUse::{SharedBorrow, RawBorrow, FakeBorrow}`, and
   - `MutatingUse::{Drop, Borrow, RawBorrow, AsmOutput}`.
   Then `visit_local` dispatches on `ctxt`:
   - `NonMutatingUse(RawBorrow) | MutatingUse(_)` -> immediately sets `assignments[local] = Set1::Many` (mutable borrows, raw borrows, field stores, drops, and inline-asm outputs disqualify SSA).
   - `NonMutatingUse(SharedBorrow | FakeBorrow)` and all other `NonMutatingUse(_)` (`Copy`, `Move`, `Inspect`, `CopyForDeref`, `PlaceMention`) -> calls `check_dominates(local, loc)` and increments `direct_uses[local] += 1`.
   - `NonUse(_)` (`StorageLive`, `StorageDead`, `VarDebugInfo`, `AscribeUserType`, `BackwardIncompatibleDropHint`) -> ignored (note `VarDebugInfo` is still visited at `ssa.rs:69-71`, and because `NonUse(VarDebugInfo)` has `is_use() == false` and `may_observe_address() == false`, it affects neither `assignments` nor `borrowed_locals`).

**Post-visit `Freeze` demotion (`ssa.rs:77-81`):**
```rust
for local in visitor.borrowed_locals.iter() {
    if !body.local_decls[local].ty.is_freeze(tcx, typing_env) {
        visitor.assignments[local] = Set1::Many;
    }
}
```
Notice a subtle documentation inaccuracy in `ssa.rs:32, 168`: `borrowed_locals` is documented as *"Set of SSA locals that are immutably borrowed"*, yet `visit_local` inserts **every** local with `ctxt.may_observe_address()` (including mutably/raw-borrowed locals and `!Freeze` locals later demoted to `Set1::Many`), and `SsaLocals::new` never filters `borrowed_locals` to SSA locals.

**Normative justification (`rust-lang/reference@c9cc32825b03`, `r[undefined.alias]`, `r[undefined.immutable]`, `r[interior-mut.unsafe-cell]`):** Under Rust's aliasing rules, mutating any byte pointed to by a live shared reference `&T` is immediate undefined behavior unless those bytes lie inside an `UnsafeCell<U>`. `Ty::is_freeze(tcx, typing_env)` returns `true` iff `T` contains no `UnsafeCell` outside indirections; thus, on any UB-free execution, an opaque callee receiving `&x` for `x: T` (`T: Freeze`) cannot mutate `x`, allowing `SsaLocals` to keep `x` in `Set1::One` while demoting `!Freeze` types (`Cell<u32>`, `RefCell<T>`, `AtomicU32`, generic `T` lacking `T: Freeze`) to `Set1::Many`.

**Empirical verification (`S1`, `rustc 1.98.0-nightly` `14210df0e` + Miri `-Zmiri-tree-borrows`):**
Compiling `freeze_shared_borrow` (`let x: u32 = 42; touch_u32(&x); x + 1`) vs. `non_freeze_cell_shared_borrow` (`let c = Cell::new(42); mutate_cell(&c); c.get()` where `mutate_cell` calls `r.set(100)`) with `-C opt-level=2 -Zmir-opt-level=2 -Zdump-mir=GVN`:
- **`freeze_shared_borrow` after `GVN`:** `GVN` retains `_2 = &_1; _3 = touch_u32(copy _2)` in `bb0`, then in `bb1` folds `_5 = const 42_u32; _0 = const 43_u32;` (`freeze_folded_const_43_in_gvn: true`), because `_1: u32` satisfies `is_freeze == true` and remains SSA across `&_1`.
- **`non_freeze_cell_shared_borrow` after `GVN`:** `GVN` does **not** fold `c.get()` (`non_freeze_folded_const_43_in_gvn: false`), because `Cell<u32>` contains `UnsafeCell<u32>`, so `ssa.rs:78-80` demotes `_1` to `Set1::Many`.
- **Differential runtime & Miri agreement:** Both the native compiled binary (`rc=0`) and `cargo miri run` under `-Zmiri-tree-borrows` (`rc=0`) output `FREEZE=43 CELL=100`.
- **Mechanized soundness & counterexample:** Lean theorems `ssaLocals_freeze_shared_borrow_value_sound` and `ssaLocals_nonFreeze_counterexample` formally prove both halves: `isFreeze == true` preserves the assigned value across arbitrary UB-free shared-borrow calls, while omitting `applyFreezeDemotion` on `Cell<u32>` is refuted by a UB-free trace ending at `some 100 != some 42`.

#### 4.3 `Operand::Move` Soundness Hazard vs. Miri and Anneal's `deinitMovedPlace = true`

A critical semantic seam connects `ssa.rs`, `copy_prop.rs`, `ref_prop.rs`, and `joshlf/anneal@c131b320eeeb`:
- `SsaVisitor::visit_local` (`ssa.rs:247-250`) classifies `PlaceContext::NonMutatingUse(NonMutatingUseContext::Move)` identically to `Copy` (a pure read that preserves `Set1::One`).
- However, in Miri—and explicitly in Anneal's `Trusted.MirSemantics.evalOperandToSlot` (`trusted/lean/Trusted/MirSemantics.lean:67-69, 140-145, 942-947`, matching `lean-miri`'s `deinitMovedPlace = true`)—evaluating `Operand::Move` on a non-ZST local **deinitializes** the source local slot to `liveUninitSlot` (`.live none`).
- Upstream `rustc` explicitly acknowledges this hazard in `compiler/rustc_mir_transform/src/ref_prop.rs:88-92`:
  > *"The SSA analysis done by `SsaLocals` treats `Operand::Move` as a read, even though in general `Operand::Move` represents pass-by-pointer where the callee can overwrite the pointee (Miri always considers the place deinitialized)."*
- Therefore, **every** MIR pass that reuses an SSA local across multiple uses based on `SsaLocals` must neutralize `Operand::Move` into `Operand::Copy`:
  - `CopyProp::Replacer::visit_operand` (`copy_prop.rs:127-137`) rewrites `Operand::Move(place)` -> `Operand::Copy(place)` whenever `!place.is_indirect_first_projection() && self.unified.contains(place.local)`.
  - `ReferencePropagation::move_to_copy_pointers` (`ref_prop.rs:93-118`) rewrites all pointer-typed `Operand::Move(place)` into `Operand::Copy(place)` before calling `SsaLocals::new`.
- Lean corollary `ssaLocals_move_deinit_counterexample` mechanizes this exact divergence: on `[assign 1 42, moveRead 1, copyRead 1]`, `analyzeSsa` marks local `1` as `Set1.one 0`, `deinitMove = false` evaluates to `some 42`, and `deinitMove = true` evaluates to `none != some 42`.

#### 4.4 `compute_copy_classes`: RPO Union-Find, `RETURN_PLACE` Re-Rooting, and the Subtle Borrowed-Temp Invariant

`compute_copy_classes` (`ssa.rs:296-361`) initializes `copies = [0, 1, ..., n-1]` and iterates `(local, rvalue, _)` in `ssa.assignments(body)` (which yields **only** locals with `Set1::One(DefLocation::Assignment(_))`, never `LocalKind::Arg` locals initialized with `DefLocation::Argument` at `ssa.rs:58-61`, in RPO order):

1. Match `Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)` where `place.as_local() == Some(rhs)` (`L301-305`).
2. Skip if `local_ty != rhs_ty` (subtyping guard, `L308-312`), `!ssa.is_ssa(rhs)` (`L314-316`), or `ssa.borrowed_locals().contains(local)` (`L327-329`).
3. Let `head = copies[rhs]` (`L320`). Because RPO visits `rhs` before `local`, `head` is already the transitive class representative.
4. **`RETURN_PLACE` barrier (`L331-345`):**
   - If `local == RETURN_PLACE` (`_0`): `_0` cannot be renamed away. Only if `body.local_kind(head) == LocalKind::Temp` (`L335`, rejecting `LocalKind::Arg` and `RETURN_PLACE` itself), sweep `copies` and rewrite every entry `*h == head` to `RETURN_PLACE` (`L338-342`).
   - Otherwise (`local != RETURN_PLACE`): set `copies[local] = head` (`L344`).
5. Decrement `direct_uses[rhs] -= 1` (`L346`). Debug assertions check union-find idempotence `copies[head] == head` (`L354-356`) and `copies[RETURN_PLACE] == RETURN_PLACE` (`L357`).

**Non-obvious invariant uncovered by Lean mechanization (`computeCopyClasses_soundness`):**
A naive reading of line 327 (`if ssa.borrowed_locals().contains(local) { continue; }`) suggests that no borrowed local ever gets `copies[l] != l`. That claim is **FALSE**! Suppose `_2` is a `LocalKind::Temp` with `borrowed_locals.contains(_2) == true` (e.g., `_3 = &_2`), `_0` (`RETURN_PLACE`) is *not* borrowed, and `_0 = copy _2`. When `compute_copy_classes` processes `(_0, copy _2)`:
- `borrowed_locals.contains(_0)` is `false` (line 327 passes);
- `local == RETURN_PLACE` is `true` and `local_kind(_2) == LocalKind::Temp` is `true` (line 335 passes);
- Lines 338-342 therefore rewrite `copies[_2] = _0`, giving `local = _2 != _0 = head` **even though `_2` is in `borrowed_locals`!**

This exact mechanism is why `copy_prop.rs:65-69` explicitly writes:
```rust
for (local, &head) in ssa.copy_classes().iter_enumerated() {
    if local != head && borrowed_locals.contains(local) {
        storage_to_remove.insert(head);
    }
}
```
Without `_0`'s re-rooting sweep, `local != head && borrowed_locals.contains(local)` would be dead code! Soundness holds because `_0` itself is SSA (`FreshClass copies _0`, appearing as LHS at most once) and unborrowed (`borrowed _0 == false`), so re-rooting `_2`'s class into `_0` merges zero additional borrowed locals into the class. The exact inductive invariant proved in `computeCopyClasses_soundness` is therefore:
- `idempotent`: `∀ x, copies (copies x) = copies x` (`computeCopyClasses_idempotent`);
- `retFixed`: `copies _0 = _0` (`computeCopyClasses_return_place_fixed`);
- `argFixed`: `∀ l, kind l = .arg -> copies l = l` (hence `copies l != _0`, `computeCopyClasses_arg_never_return_place`);
- `atMostOneBorrowed`: `∀ x y, copies x = copies y -> borrowed x = true -> borrowed y = true -> x = y` (`computeCopyClasses_at_most_one_borrowed`).

**Empirical confirmation (`S2`, `CopyProp` MIR dumps on `14210df0e`):**
- `copy_chain_temp_to_ret`: `_2 = Add(copy _1, const 7_u64); _3 = copy _2; _4 = copy _2; _0 = copy _2;` collapses completely into `_0 = Add(copy _1, const 7_u64); return;` (including `debug t1/t2/t3 => _0`), demonstrating `RETURN_PLACE` absorbing the `LocalKind::Temp` chain.
- `copy_arg_to_ret`: `_2 = copy _1; _0 = copy _1;` collapses `_2` into `_1` (`debug a => _1`), while preserving `_0 = copy _1;` because `local_kind(_1) == LocalKind::Arg != LocalKind::Temp`.
- `copy_borrowed_distinct_addrs`: `_2 = Add(copy _1, const 1_u64); _3 = copy _2; _4 = &_2; _5 = &_3; observe_addrs(copy _4, copy _5)` leaves `_3 = copy _2` unpropagated because `borrowed_locals.contains(_3) == true`, preserving `SAME_ADDR=false` at runtime.

#### 4.5 Two-Pass In-Place `meet_copy_equivalence` and Companion Analyses

`SsaLocals::meet_copy_equivalence(&self, property: &mut DenseBitSet<Local>)` (`ssa.rs:174-198`, consumed by `ReferencePropagation::fully_replaceable_locals` at `ref_prop.rs:361-375`) shrinks `property` in-place to be uniform across every copy equivalence class:
- **Pass 1 (`L179-184`):** For each `(local, &head)`, if `!property.contains(local)` then `property.remove(head)`.
- **Pass 2 (`L185-191`):** For each `(local, &head)`, if `!property.contains(head)` then `property.remove(local)`.
- **Debug invariant (`L194-197`):** `assert_eq!(property.contains(local), property.contains(head))`.

Notice why in-place mutation during Pass 2 is safe **iff** `copy_classes` is idempotent: whenever Pass 2 executes `property.remove(local)` on a non-head `local != head`, idempotence guarantees no `x` has `copies[x] == local`, so clearing `local` never mutates `property[copies[x]]` for any later iteration; and if `local == head`, `!property.contains(head)` implies `property[head]` is already `false`. Mechanized theorems `meetCopyEquivalence_uniform_iff_all_copies` and `meetCopyEquivalence_requires_idempotence` prove:
1. Under idempotence, `result l = true <-> ∀ m, copies m = copies l -> prop m = true`, `result l = result (copies l)`, `result l = true -> prop l = true`, and `meetCopyEquivalence` is itself idempotent.
2. Without idempotence (`copies = [0, 0, 1]`, `prop = [true, true, false]`), two-pass execution yields `[true, false, false]`, violating uniformity at local `1` (`false != true`).

`ssa.rs` also defines two companion utilities consumed across `rustc_mir_transform`:
- **`StorageLiveLocals` (`ssa.rs:364-394`, consumed by `ref_prop.rs:157`):** Tracks `Set1<DefLocation>` over `StatementKind::StorageLive` (seeding `always_storage_live_locals` with `DefLocation::Argument`) to answer `has_single_storage(local)`.
- **`MaybeUninitializedLocals` (`ssa.rs:400-455`, consumed by `copy_prop.rs:71` and `gvn.rs:161`):** A forward bitset dataflow analysis (`bottom = empty` / all initialized; entry block sets all bits except `args_iter()`; bare-local `Assign` and `CallReturnPlaces` clear bits; `StorageLive`/`StorageDead` set bits). `CopyProp`'s `StorageChecker` (`copy_prop.rs:162-194`) queries it before each use of a non-head `local` to remove storage markers on `head` whenever `head` might be uninitialized at `local`'s use site (preventing UB from extending `head`'s lifetime across `StorageDead(head)`).

---

### 5. `CheckPointers`, `CheckAlignment`, and `CheckNull`: Instrumentation Semantics, Projection Modes, and Terminator Gap

Basis: normative (`rust-lang/reference@c9cc32825b03`, `r[undefined.pointer-access]`, `r[undefined.misaligned.*]`, `r[undefined.dangling.*]`, `r[undefined.validity.reference-box]`) + source (`check_pointers.rs:1-251`, `check_alignment.rs:1-148`, `check_null.rs:1-128`, `lib.rs:710-713`) + execution (`P1`, `P2`, `P3`) + derived (Lean theorems `checkPointers_splitBlock_preserves_validCfg`, `aligned_base_iff_aligned_field`)

#### 5.1 `check_pointers` Core Mechanism and `BorrowedFieldProjectionMode`

`compiler/rustc_mir_transform/src/check_pointers.rs:1-251` provides the shared MIR UB-check instrumentation driver invoked at the very start of `run_optimization_passes` (`lib.rs:710-712`, before inlining or optimizations can exploit or erase UB) by `CheckAlignment` and `CheckNull`.

Its exact public-in-crate API (`check_pointers.rs:18-59`) defines:
```rust
pub(crate) enum BorrowedFieldProjectionMode {
    FollowProjections,
    NoFollowProjections,
}
```
*(Note: the upstream enum is named `BorrowedFieldProjectionMode`, not `BorrowCheckMode`.)*

Execution proceeds as follows:
1. **`#![no_std]` panic-handler guard (`check_pointers.rs:62-64`):** Returns immediately if `tcx.lang_items().get(LangItem::PanicImpl).is_none()`, avoiding unresolved panic-impl link errors in bare-metal crates without a panic handler.
2. **Backwards block and statement traversal (`L74-88`):** Iterates `for block in basic_blocks.indices().rev()` and `for statement_index in (0..basic_blocks[block].statements.len()).rev()`, running `PointerFinder::visit_statement(statement, location)`. Backwards iteration ensures splitting `block` at `statement_index` only shifts indices of already-processed trailing statements.
3. **`PointerFinder` filtering (`L182-250`):**
   - `should_visit_place` accepts `MutatingUse::{Store, Call, Yield, Drop, Borrow}` and `NonMutatingUse::{Copy, Move, SharedBorrow}` (rejecting `RawBorrow`, `FakeBorrow`, `PlaceMention`, `Inspect`, and all `NonUse` contexts—matching `r[undefined.misaligned.raw]`, which permits `&raw const (*p)` on misaligned/null pointers).
   - Requires `place.is_indirect()` and base `Place::from(place.local)` having `ty::RawPtr(mut pointee_ty, _)` (references and `Box`es are skipped).
   - **Field-projection override (`L219-228`):** If `field_projection_mode` is `FollowProjections` AND `context` is `SharedBorrow | Borrow`, replaces `pointee_ty` with `place.ty(self.local_decls, self.tcx).ty` (the projected field type), while still passing the **base** raw pointer `Place::from(place.local)` to `on_finding`!
   - Skips unsized `pointee_ty` (`!pointee_ty.is_sized(tcx, typing_env)`, `L231-234`).
   - Extracts `element_ty` (unwrapping `ty::Array(ty, _)` to `*ty`, `L237-240`) and skips if `excluded_pointees.contains(&element_ty)` (`L242-245`).
4. **Block splitting & `UnwindAction::Unreachable` (`L89-142`):** Splits `statements` at `location.statement_index`, appends the check statements generated by `on_finding` to `block`, replaces `block`'s terminator with:
   ```rust
   TerminatorKind::Assert {
       cond: pointer_check.cond,
       expected: true,
       target: new_block_idx,
       msg: pointer_check.assert_kind,
       unwind: UnwindAction::Unreachable,
   }
   ```
   and pushes the continuation `new_block_idx` inheriting **`block_data.is_cleanup`** (`L139`). As documented at `L113-117`, `UnwindAction::Unreachable` is mandatory because the pointer-check panic lang items are `#[rustc_nounwind]`; initiating unwinding inside unsafe code on a UB check failure could trigger worse UB. Mechanized theorem `checkPointers_splitBlock_preserves_validCfg` proves this block-splitting step preserves all `ValidCfg` invariants in both `is_cleanup == false` and `is_cleanup == true` blocks.

#### 5.2 Exact Semantic Comparison: `CheckAlignment` vs. `CheckNull`

| Property | `CheckAlignment` (`check_alignment.rs`) | `CheckNull` (`check_null.rs`) |
| :--- | :--- | :--- |
| **Pass Policy (HEAD `137d1d49458b`)** | `PassPolicy::optional(ctx.ub_checks())` (`L15-18`) | `PassPolicy::optional(ctx.ub_checks())` (`L13-16`) |
| **Pass Policy (`14210df0e`)** | `is_enabled -> sess.ub_checks()`, `is_required -> true` | `is_enabled -> sess.ub_checks()`, `is_required -> true` |
| **`excluded_pointees`** | `[bool, i8, u8]` (`L22`) — **does NOT exclude `()` (`unit`)!** | `&[]` (empty; checks all sized types, using runtime `SIZE != 0` guard) |
| **`BorrowedFieldProjectionMode`** | **`FollowProjections`** (`L32`) | **`NoFollowProjections`** (`L24`) |
| **Address extraction** | `PtrToPtr` to `*const ()`, then `Transmute` to `usize` (`L49-57`) | `PtrToPtr` to `*const ()`, then `Transmute` to `usize` (`L39-47`) |
| **Checked condition (`is_ok`)** | `(addr & ((align_of::<pointee_ty>() - 1) [& max_reliable_mask])) == 0` (`L60-137`) | `!((addr == 0) & should_check)` where `should_check = true` on `SharedBorrow \| Borrow`, else `size_of::<pointee_ty>() != 0` (`L55-123`) |
| **Target `max_reliable_alignment()` clamp** | Yes (`L86-108`): if `max_align < Align::MAX`, masks `alignment_mask &= max_align.bytes() - 1` | Not applicable |
| **`AssertKind` on failure (HEAD `137d1d49458b`)** | `AssertKind::MisalignedPointerDereference { required, found }` (`L143-146`) | `AssertKind::NullReferenceConstructed` on `SharedBorrow \| Borrow`; `AssertKind::NullPointerDereference` otherwise (`L55-88`) |
| **`AssertKind` on failure (`14210df0e`)** | `AssertKind::MisalignedPointerDereference { required, found }` | `AssertKind::NullPointerDereference` for **both** borrows and derefs |

**Why `CheckAlignment` passing base `pointer` with field `pointee_ty` under `FollowProjections` is sound (and why `#[repr(packed)]` cannot break it):**
For a struct `#[repr(C)] struct Pair { a: u32, b: u8 }`, Rust Reference `r[undefined.misaligned.ptr]` specifies that loading `(*p).b` requires `p` to be aligned to `Pair` (4 bytes), whereas `r[undefined.misaligned.reference]` specifies that creating `&(*p).b` only requires the resulting `&u8` reference to be aligned to `u8` (1 byte). When taking `&(*p).f` for any field `f: F` of a non-packed struct, Rust layout guarantees `offset_of!(S, f) % align_of::<F>() == 0` (and taking `&(*p).f` on a `#[repr(packed)]` field with `align_of::<F>() > packed_align` is a hard compile error per `r[undefined.misaligned.packed]`). By mechanized theorem `aligned_base_iff_aligned_field`, `offset % align == 0` implies `addr % align == 0 <-> (addr + offset) % align == 0`, so checking `addr(p) % align_of::<F>() == 0` is mathematically identical to checking `(addr(p) + offset_of!(S, f)) % align_of::<F>() == 0`.

**Live empirical matrix (`P1` MIR dumps + `P2` runtime traps on `14210df0e`, `-Zub-checks=yes`):**

| Function / Case | `CheckAlignment` MIR Changed? | `CheckNull` MIR Changed? | `CheckNull` `SIZE != 0` Guard? | Runtime Result (`P2`, `-Zub-checks=yes`) |
| :--- | :---: | :---: | :---: | :--- |
| `read_u32(*p)` | **Yes** (`<u32>::ALIGN`, `unwind unreachable`) | **Yes** (`unwind unreachable`) | Yes (`<u32>::SIZE != 0`) | Misaligned -> `rc=-6` (`SIGABRT`, misaligned); Null -> `rc=-6` (`SIGABRT`, null) |
| `read_u8(*p)` | **No** (`u8` in `excluded_pointees`) | **Yes** | Yes (`<u8>::SIZE != 0`) | *(alignment skipped; null checked)* |
| `read_zst(*p)` (`*const ()`) | **Yes** (`<()>::ALIGN` — `()` not excluded!) | **Yes** | **Yes** (`<()>::SIZE != 0` -> false) | Null ZST read -> **`rc=0`, `ZST_READ_OK`** |
| `borrow_zst(&*p)` (`*const ()`) | **Yes** (`<()>::ALIGN`) | **Yes** | **No** (`const true`, unconditional!) | Null ZST borrow -> **`rc=-6` (`SIGABRT`, null pointer dereference)** |
| `borrow_u8_field(&(*p).b)` (`*const Pair`) | **No** (`FollowProjections` -> `u8` excluded!) | **Yes** (`NoFollowProjections`) | **No** (`const true`) | Misaligned `&(*p).b` -> **`rc=0`, `BORROW_U8_FIELD=170`** |
| `read_u8_field((*p).b)` (`*const Pair`) | **Yes** (`<Pair>::ALIGN`, `Copy` not borrow) | **Yes** | Yes (`<Pair>::SIZE != 0`) | *(checks 4-byte `Pair` alignment)* |

#### 5.3 Primary-Source & Empirical Finding: `check_pointers` Statement-Only Loop Omits Terminators (`P3`)

Inspection of `check_pointers.rs:74-88` reveals a structural gap relative to `PointerFinder::should_visit_place` (`check_pointers.rs:182-198`):
- `should_visit_place` explicitly matches `MutatingUseContext::Call | MutatingUseContext::Yield | MutatingUseContext::Drop`—contexts that occur exclusively on `TerminatorKind::{Call, Yield, Drop}`!
- Yet `check_pointers` (`L75-87`) loops solely over `statements`:
  ```rust
  for statement_index in (0..basic_blocks[block].statements.len()).rev() {
      let location = Location { block, statement_index };
      let statement = &basic_blocks[block].statements[statement_index];
      ...
      finder.visit_statement(statement, location);
  ```
  It **never** calls `finder.visit_terminator(terminator, terminator_location)`.
- **Empirical confirmation (`P3` on `14210df0e`):** Compiling a `#[custom_mir(dialect = "runtime", phase = "post-cleanup")]` function whose sole block terminator is `Call(RET = sink(copy (*_1)), ReturnTo(bb1), UnwindContinue())` with `-Zub-checks=yes -Zmir-opt-level=0 -Zvalidate-mir=yes -Zdump-mir=Check`:
  - `Validator` accepts the MIR (`compile_rc=0`, `has_broken_mir=false`).
  - Both `CheckAlignment` and `CheckNull` leave the MIR **100% unchanged** (`changed: false`).
- In normal surface Rust, MIR building (`rustc_mir_build`) typically lowers `sink(*p)` into a statement temporary `_2 = copy (*_1)` followed by `Call(sink(move _2))`, masking this omission for ordinary Rust call arguments; however, any `TerminatorKind::Drop(*p)` or custom/transformed MIR placing `copy (*p)` directly in a `Call` or `SwitchInt` terminator bypasses `CheckAlignment` and `CheckNull` completely.

---

### 6. Version Deltas (`14210df0e` vs. `137d1d49458b`) and Anneal Trusted Boundary Alignment

Basis: source (`rust-lang/rust@14210df0e` vs. `137d1d49458b`; `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) + derived

#### 6.1 Complete Source Delta Summary (`14210df0e` -> `137d1d49458b`)

| Module | `14210df0e` (2026-05-31, executed) | `137d1d49458b` (2026-11-22, HEAD) | Semantic Impact |
| :--- | :--- | :--- | :--- |
| `validate.rs` (1,683 -> 1,712 LOC) | `is_required(&self) -> bool { true }` | `policy(&self, _) -> PassPolicy::optional(true)` | Unified pass-policy API (`pass_manager.rs:88-107`); `Validator` is invoked explicitly via `validate_body` |
| `validate.rs:317-326` | Matches `CoverageKind::BlockMarker \| SpanMarker` | Calls `kind.is_removed_after_analysis()` (`Point \| BlockMarker`, `coverage.rs:123-128`) | Tracks renamed coverage marker variants |
| `validate.rs:367-375` | Only checks `drop` edge target | Adds `>= Runtime(Initial)` ban on `Drop { drop: Some(_), .. }` (`async drop`) | Enforces `StateTransform` elimination of async drops |
| `validate.rs:436-452` | No pre-runtime `Call` `Move` shape check | Under `-Zvalidate-mir && < Runtime(Initial)`, requires `Call`/`TailCall` `Operand::Move` args to be plain local or `Box` deref | Prevents misaligned/projected call-by-move MIR |
| `validate.rs:632-645` | `if pred.has_opaque_types() { return true; }` + `infer_ctxt().build_with_typing_env(...)` | Gates opaque bypass on `!next_trait_solver_globally()` + adds `.ignoring_regions()` | Tighter `CoerceUnsized` checking under `-Znext-solver=globally` |
| `validate.rs:1404-1445` | Handles `CastKind::Transmute` only | Handles `CastKind::Transmute \| CastKind::BoxDerefTransmute` (requiring `target_type.is_raw_ptr()`) | Supports `ElaborateBoxDerefs` raw-ptr transmute lowering |
| `ssa.rs` (455 -> 455 LOC) | `use rustc_middle::bug;` | `use rustc_span::bug;` | **Zero semantic change** |
| `check_pointers.rs` (245 -> 251 LOC) | Uses helper `split_block` with `block_data.terminator.take()` | Uses `basic_blocks.push_with(...)` + `std::mem::replace(block_data.terminator_mut(), ...)` | Eliminates transient `terminator = None`; preserves statement-only loop and `UnwindAction::Unreachable` |
| `check_alignment.rs` (146 -> 148 LOC) | `is_enabled -> sess.ub_checks()`, `is_required -> true` | `policy -> PassPolicy::optional(ctx.ub_checks())` | Can now be toggled via `-Zmir-enable-passes=±CheckAlignment` |
| `check_null.rs` (124 -> 128 LOC) | `is_required -> true`; always emits `AssertKind::NullPointerDereference` | `PassPolicy::optional(ctx.ub_checks())`; emits **`AssertKind::NullReferenceConstructed`** for `SharedBorrow \| Borrow` | Distinct runtime panic message/kind for null reference creation vs. dereference |

#### 6.2 Alignment With Anneal's Trusted Boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Direct audit of `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes the exact boundary contract between `rustc` MIR validation and Anneal:

1. **Pinned compiler proximity:** `trusted/rustc-capture/src/driver.rs:25` pins `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"`, one day prior to our executed `14210df0e` (`2026-05-31`). Currently `driver.rs` is a minimal clean-analysis callback skeleton (`L75-84, 148-150`) that does not yet serialize MIR bodies.
2. **AST representation of `validate.rs` & `check_pointers.rs` artifacts (`Trusted/MirAst.lean`):**
   - `BasicBlock` (`L810-813`) carries `cleanup : Bool := false`, directly mirroring `BasicBlockData::is_cleanup`.
   - `AssertKind` (`L738-739`) explicitly includes `.misalignedPtrDeref` and `.nullPtrDeref` (corresponding to `CheckAlignment` and `14210df0e`-era `CheckNull`; capturing HEAD `137d1d49458b` will additionally encounter `AssertKind::NullReferenceConstructed`).
   - `StatementKind` (`L650-657`) admits `.assign`, `.storageLive`, `.storageDead`, `.nop`, and maps analysis-only variants (`FakeRead`, `AscribeUserType`, `Coverage`, `BackwardIncompatibleDropHint`) to `.unsupported`; `TerminatorKind` (`L770-795`) admits `.goto`, `.switchInt`, `.return_`, `.unreachable`, `.unwindResume`, `.assert`, `.call`, and maps `Drop`, `TailCall`, `Yield`, `FalseEdge`, `FalseUnwind`, `UnwindTerminate` to `.unsupported`.
3. **Static vs. dynamic enforcement gap (`Trusted/MirSemantics.lean`):**
   - `BodyStaticAdmitted` (`L1730-1737`) checks 64-bit pointer width, profile version 1, non-empty `identity`, non-empty `basicBlocks`, `argumentCount < locals.length`, in-bounds storage annotations, and supported scalar/unit local types. It does **not** statically validate `START_BLOCK` zero-predecessor, the 3-of-8 `(is_cleanup, EdgeKind)` matrix, `Deref` index `0`, or `check_cleanup_control_flow`.
   - Dynamically, `evalStep` fails closed on `bb.cleanup == true` at `.return_` (`MirSemantics.lean:1542-1544`, matching `validate.rs:531-536`) and faults `.unsupported` on `.unwindResume`, `.assert`, and `.call` (`L1568-1569`).
   - Any future verified MIR optimization pass operating inside Anneal (or capturing `Runtime(PostCleanup)` MIR before `rustc`'s `run_optimization_passes`) must account for two findings from this report: (a) `MirSemantics.lean:67-69, 942-947` enables `deinitMovedPlace = true`, so any `SsaLocals`-style optimization over Anneal MIR must rewrite `Operand.move` to `Operand.copy` on reused non-ZST locals (Section `4.3`); and (b) capturing at `Runtime(PostCleanup)` rather than `Runtime(Optimized)` avoids both `CheckAlignment`/`CheckNull` block splits (which inject `.assert` terminators) and `rustc`'s unverified `GVN`/`CopyProp` optimizations, while inheriting `Validator`'s `Runtime(Initial)` elimination of `FakeRead`, `AscribeUserType`, `CopyForDeref`, `FalseEdge`, `FalseUnwind`, `Yield`, `Box` derefs, and later-`Deref` projections—provided `-Zvalidate-mir=yes` or an explicit `validate_body` call is invoked at capture time, because `pass_manager.rs:409` otherwise validates unconditionally only at `Runtime(Optimized)`.

---

### 7. Kernel-Checked Lean 4 (`v4.34.1`) Formalization Summary

Basis: source (`support/MirValidatorPhaseAutomatonAndSsaLocalsSoundness.lean`) + execution (Lean `v4.34.1` kernel check & `MetaM` environment audit) + derived

`support/MirValidatorPhaseAutomatonAndSsaLocalsSoundness.lean` (2,253 lines, 93,502 bytes, 842 kernel constants) mechanizes all four subsystems constructively using only Lean 4's `Init` prelude.

#### 7.1 Constructive Purity & Elimination of `._unsafe_rec` and `Classical.choice`

During mechanization, two Lean `v4.34.1` kernel-hygiene hazards were discovered and eliminated at the source:
1. **Zero `._unsafe_rec` constants:** In Lean `v4.34.1`, writing recursive `def`s via equation-compiler pattern matching generates auxiliary `._unsafe_rec` constants for the code generator, and `deriving DecidableEq, Repr` on payload-carrying inductives does the same. Replacing all 16 recursive helpers with zero-recursor standard combinators (`List.foldl`, `List.foldr`, `List.any`, `Nat.repeat`) and `inductive` `Prop` predicates (`AllNormal`, `TraceUbFree`, `NoMoveOn`, `ValidRpoEdges`), with zero `deriving` clauses, reduces `UNSAFE_REC_COUNT` across all 842 module constants to **`0`**.
2. **Zero `Classical.choice`:** In Lean `v4.34.1`, calling `beq_self_eq_true` on `Nat` traverses `ReflBEq`/`LawfulBEq` instances that pull in `Classical.choice`. Defining `natEq (a b : Nat) : Bool := Nat.beq a b` with direct structural-induction lemmas (`natEq_self`, `natEq_true_iff`, `natEq_false_iff`, `finEq_true_iff`, `finEq_false_iff`) eliminates `Classical.choice` completely (`FORBIDDEN_AXIOM_DECL_COUNT = 0`).

#### 7.2 Complete Catalog of Kernel-Verified Theorems

| Part | Exported Theorem (`MirValidatorSsaSoundness.*`) | Formal Statement Summary | Kernel Axioms |
| :---: | :--- | :--- | :--- |
| I | `mirPhase_invariant_monotonicity` | Monotone-ban validity strengthens across all `p <= q`; full `Validator` phase validity strengthens across all `Runtime(Initial) <= p <= q` | `[propext]` |
| I | `dialect_boundary_witnesses` | Witnesses non-monotonicity of `SetDiscriminant` and `AggregateKind::RawPtr` across `Analysis(PostCleanup) -> Runtime(Initial)`, `VarDebugInfo` exemption for later `Deref`, and all-phase `Downcast -> Field` | `[propext]` |
| I | `validEdgeTransition_exact_3_of_8` | Exhaustively verifies all 3 valid and 5 invalid `(srcCleanup, dstCleanup, EdgeKind)` transitions | `[propext]` |
| I | `start_block_unreachable_after_step` | Any non-empty valid CFG path from `START_BLOCK` ends at `dst != 0` | `[propext]` |
| I | `cleanup_sticky_under_valid_edges` | Any valid path starting in `isCleanup = true` stays in `isCleanup = true` using only `Normal` edges | `[propext]` |
| I | `cleanup_automaton_path_separation` | Every valid path from `0` decomposes into Phase A (`countUnwind = 0`) or Phase A + single `Unwind` + Phase B (`countUnwind = 1`), separating `Return` (Phase A) from `UnwindResume`/`UnwindTerminate` (Phase B) | `[propext]` |
| I | `nounwind_path_cannot_resume` | When `canUnwind = false`, no reachable block can exit via `UnwindResume` | `[propext]` |
| I | `cleanup_contraction_unique_root` | Every node in an acyclic out-degree-`<= 1` `ContractedCleanupForest` reaches a unique root within `rank u` steps | `[]` |
| II | `ssaLocals_freeze_shared_borrow_value_sound` | If `analyzeSsa isFreeze` classifies `l` as `Set1.one defIdx` on a UB-free trace (with shared borrows of `Freeze` locals) and either `deinitMove = false` or `NoMoveOn l suff`, `l` retains `some v₀` | `[propext, Quot.sound]` |
| II | `ssaLocals_nonFreeze_counterexample` | Concrete `Cell<u32>` UB-free trace: omitting `applyFreezeDemotion` falsely marks `Set1.one 0` while execution yields `some 100 != some 42`; `applyFreezeDemotion` demotes to `Set1.many` | `[propext]` |
| II | `ssaLocals_move_deinit_counterexample` | Concrete `Move`-deinit trace: `analyzeSsa` marks `Set1.one 0`, `deinitMove = false` yields `some 42`, `deinitMove = true` yields `none != some 42` | `[propext]` |
| III | `computeCopyClasses_soundness` | Full inductive loop invariant for RPO `compute_copy_classes`: idempotence, `RETURN_PLACE` fixed-point, `Arg` fixed-point, and `atMostOneBorrowed` per copy class | `[propext]` |
| III | `computeCopyClasses_idempotent` | Projection: `copies (copies x) = copies x` (`ssa.rs:355`) | `[propext]` |
| III | `computeCopyClasses_return_place_fixed` | Projection: `copies _0 = _0` (`ssa.rs:357`) | `[propext]` |
| III | `computeCopyClasses_arg_never_return_place` | Projection: no `LocalKind.arg` is ever merged into `RETURN_PLACE` | `[propext]` |
| III | `computeCopyClasses_at_most_one_borrowed` | Projection: at most one local per copy class is in `borrowed_locals` | `[propext]` |
| III | `meetCopyEquivalence_uniform_iff_all_copies` | Under idempotent `copies`, two-pass in-place `meetCopyEquivalence` satisfies exact class-conjunction iff, class uniformity (`ssa.rs:196`), monotone shrinking, and idempotence | `[propext]` |
| III | `meetCopyEquivalence_requires_idempotence` | Concrete 3-local non-idempotent counterexample (`2 -> 1 -> 0`) violating two-pass uniformity (`false != true`) | `[]` |
| IV | `checkPointers_splitBlock_preserves_validCfg` | Splitting any valid block with inherited `is_cleanup`, `Normal` edge `b -> newBb`, and `UnwindAction.unreachable` preserves all `ValidCfg` invariants | `[propext, Quot.sound]` |
| IV | `aligned_base_iff_aligned_field` | `offset % align = 0 -> (addr % align = 0 <-> (addr + offset) % align = 0)` | `[propext]` |

## Boundaries

The following explicit negative-space classifications define what this investigation does **not** establish:

1. **Known not to apply:**
   - **Global `MirPhase` monotonicity across `Analysis -> Runtime`:** Does *not* hold for `StatementKind::SetDiscriminant`, `AggregateKind::RawPtr`, pre-runtime `Subslice` ordering, or pre-runtime `Operand::Copy` / `Call` `Move` restrictions, all of which either enter or relax at `Runtime(Initial)` (Section `1.2`, `dialect_boundary_witnesses`).
   - **`TailCall` ABI/signature enforcement in `validate.rs`:** Known *not* to be implemented in `validate.rs` at either `14210df0e` or `137d1d49458b` (`validate.rs:379, 1636-1639` are empty `FIXME` blocks).
   - **Borrowed-local immovability in `compute_copy_classes`:** The stronger claim *"every `l ∈ borrowed_locals` satisfies `copy_classes[l] == l`"* is **false**; when `RETURN_PLACE` (`_0`) is unborrowed and receives `_0 = copy _t` from a borrowed `LocalKind::Temp`, `ssa.rs:338-342` re-roots `_t` to `_0`. The true invariant is `atMostOneBorrowed` per copy class (Section `4.4`).
   - **Terminator raw-pointer instrumentation in `check_pointers.rs`:** Known *not* to apply to `Terminator` places (`Call`, `Drop`, `Yield`, `SwitchInt`), because `check_pointers.rs:87` only calls `finder.visit_statement` (confirmed by Probe `P3`).
   - **Unsized pointees and `#[no_std]` crates without `#[panic_handler]` in `check_pointers.rs`:** Explicitly skipped by `check_pointers.rs:62-64, 231-234`.
   - **`InstanceKind::Intrinsic` and `InstanceKind::Virtual` in `Validator`:** Explicitly skipped by `validate.rs:42-44`.

2. **Unsupported (by upstream tools / interfaces):**
   - **Testing `START_BLOCK` predecessor ICEs via `#[custom_mir]`:** Unsupported by `library/core/src/intrinsics/mir.rs` and `rustc_mir_build/src/builder/custom/mod.rs:82-86`, which never bind an identifier for `bb0` (Probe `V1` fails at HIR resolution with `E0425`). Exercising `validate.rs:140-142` directly requires a custom `rustc_driver` pass mutating `TerminatorKind` targets or a unit test inside `rustc_mir_transform`.
   - **Runtime execution of `CheckNull`'s `AssertKind::NullReferenceConstructed` distinction on `14210df0e`:** That variant split landed between `14210df0e` and `137d1d49458b`, so `14210df0e` reports `"null pointer dereference occurred"` for both `p2.null` and `p2.null_zst_borrow`.

3. **Not examined:**
   - **HIR/THIR `become` tail-call signature checking outside `validate.rs`:** Where `rustc_hir_typeck` or `rustc_mir_build` rejects incompatible `become` signatures was not audited; only `validate.rs` was checked.
   - **Full MIR inliner interaction with `validate_types`:** How `compiler/rustc_mir_transform/src/inline.rs` consumes `validate_types` failures to cancel inlining (including rigid-projection and cycle bailouts) was not examined.
   - **Non-x86_64 targets with `max_reliable_alignment() < Align::MAX`:** The `check_alignment.rs:86-108` mask-clamping branch was audited from source only, not executed on a target with reduced reliable alignment (such as AVR or MSP430).
   - **Miri execution of `CheckAlignment`/`CheckNull` probes (`P2`) or `S2`/`S3`:** Only `S1` (`Freeze` vs. `Cell<u32>`) was executed under `cargo miri run -Zmiri-tree-borrows`.
   - **Direct import of `joshlf/anneal`'s `Trusted.MirSemantics` in Lean:** `support/MirValidatorPhaseAutomatonAndSsaLocalsSoundness.lean` is a standalone `Init`-only formalization of `rustc`'s algorithms and operational abstractions rather than a proof linked against Anneal's `Trusted` Lake workspace.

4. **Unknown:**
   - Whether any downstream MIR optimization pass in `run_optimization_passes` between `Runtime(PostCleanup)` and `CheckAlignment`/`CheckNull` can synthesize a direct raw-pointer dereference inside a `TerminatorKind` operand from safe or unsafe surface Rust (making the `P3` statement-only gap reachable without `#[custom_mir]`). Notice `CheckAlignment` and `CheckNull` run first in `run_optimization_passes` (`lib.rs:711-712`), immediately after `run_runtime_cleanup_passes` (`LowerIntrinsics`, `RemovePlaceMention`, `SimplifyCfg::PreOptimizations`), so only `rustc_mir_build`, drop elaboration, or those three cleanup passes could introduce a terminator-position raw-pointer dereference before `check_pointers` runs; whether `ElaborateDrops` emits `Drop(*raw_ptr)` directly on a raw-pointer deref was not exhaustively audited.

## Evidence

### 1. Immutable Upstream Primary Sources

All Git commit SHAs below were resolved live against GitHub on `2026-11-23`:

- **`rust-lang/rust` HEAD (`137d1d49458b73b7b85d2c1599d8730886d65e47`, 2026-11-22):**
  - `compiler/rustc_mir_transform/src/validate.rs` (`L1-1712`): `EdgeKind` (`L25-29`), `Validator::run_pass` & `can_unwind` (`L36-98`), `CfgChecker::check_edge` (`L139-166`), `check_cleanup_control_flow` (`L168-244`), `check_unwind_edge` (`L246-275`), `is_critical_call_edge` (`L277-281`), `CfgChecker` visitor (`L284-554`), `validate_types` & `TypeChecker` (`L561-1685`), `validate_debuginfos` (`L1687-1712`).
  - `compiler/rustc_mir_transform/src/ssa.rs` (`L1-455`): `SsaLocals::new` & `is_freeze` demotion (`L37-101`), `assignments` (`L133-148`), `meet_copy_equivalence` (`L174-198`), `SsaVisitor` (`L201-293`), `compute_copy_classes` (`L296-361`), `StorageLiveLocals` (`L364-394`), `MaybeUninitializedLocals` (`L400-455`).
  - `compiler/rustc_mir_transform/src/check_pointers.rs` (`L1-251`): `BorrowedFieldProjectionMode` (`L19-22`), `check_pointers` (`L43-145`), `PointerFinder` (`L147-251`).
  - `compiler/rustc_mir_transform/src/check_alignment.rs` (`L1-148`): `CheckAlignment` (`L12-35`), `insert_alignment_check` (`L39-148`).
  - `compiler/rustc_mir_transform/src/check_null.rs` (`L1-128`): `CheckNull` (`L10-27`), `insert_null_check` (`L29-128`).
  - `compiler/rustc_mir_transform/src/pass_manager.rs` (`L86-107, 235-425`): `PassPolicy`, `run_passes_no_validate`, `run_passes_inner` (phase-change validation gates at `L403-413`).
  - `compiler/rustc_mir_transform/src/lib.rs` (`L395-789`): exact query and pass schedule across all 6 `MirPhase` stages.
  - `compiler/rustc_mir_transform/src/copy_prop.rs` (`L22-194`): `borrowed_locals` head storage removal (`L65-69`), `Operand::Move -> Copy` rewrite (`L127-137`), `StorageChecker` (`L162-194`).
  - `compiler/rustc_mir_transform/src/ref_prop.rs` (`L73-135, 361-375`): `move_to_copy_pointers` (`L88-118`), `fully_replaceable_locals` calling `ssa.meet_copy_equivalence` (`L361-375`).
  - `compiler/rustc_mir_transform/src/gvn.rs` (`L124-165, 396-550`): `SsaLocals` and `MaybeUninitializedLocals` consumption.
  - `compiler/rustc_middle/src/mir/syntax.rs` (`L42-144, 448-505, 1369`): `MirPhase`, `AnalysisPhase`, `RuntimePhase`, `BackwardIncompatibleDropHint`, `WithRetag`, `Rvalue::Use(Operand, WithRetag)`.
  - `compiler/rustc_middle/src/mir/mod.rs` (`L1676-1704`): `DefLocation` and `DefLocation::dominates`.
  - `compiler/rustc_middle/src/mir/visit.rs` (`L1411-1446`): `PlaceContext::may_observe_address`, `is_use`.
  - `compiler/rustc_middle/src/mir/coverage.rs` (`L123-128`): `CoverageKind::is_removed_after_analysis`.
  - `compiler/rustc_data_structures/src/graph/dominators/mod.rs` (`L378-403`): `assert!(b.start != 0, "node {b:?} is not reachable")`.
  - `compiler/rustc_mir_dataflow/src/debuginfo.rs` (`L1-25`): `debuginfo_locals`.
  - `compiler/rustc_mir_build/src/builder/custom/mod.rs` (`L31-100`): implicit `START_BLOCK` allocation (`block_decls: indexvec![false]`).
  - `library/core/src/intrinsics/mir.rs`: `mir!` macro documentation and `__internal_declare_basic_blocks`.
- **`rust-lang/rust` executed nightly (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `miri 0.1.0`):**
  - Audited `validate.rs` (`1,683` LOC), `ssa.rs` (`455` LOC), `check_pointers.rs` (`245` LOC), `check_alignment.rs` (`146` LOC), `check_null.rs` (`124` LOC), and `syntax.rs` directly against HEAD `137d1d49458b`.
- **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, 2026-11-17):**
  - `src/behavior-considered-undefined.md`: `r[undefined.pointer-access]`, `r[undefined.alias]`, `r[undefined.immutable]`, `r[undefined.misaligned.*]`, `r[undefined.dangling.*]`, `r[undefined.validity.reference-box]`.
  - `src/interior-mutability.md`: `r[interior-mut.shared-ref]`, `r[interior-mut.unsafe-cell]`.
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, 2026-11-19):**
  - `trusted/lean/Trusted/MirAst.lean` (`L650-868`): `StatementKind`, `AssertKind`, `TerminatorKind`, `BasicBlock.cleanup`, `Body`.
  - `trusted/lean/Trusted/MirSemantics.lean` (`L64-70, 140-146, 916-955, 1538-1570, 1730-1796`): `deinitMovedPlace = true`, `evalOperandToSlot`, `evalStep` (`if bb.cleanup then .fault .unsupported`), `BodyStaticAdmitted`, `BodyVerified`.
  - `trusted/rustc-capture/src/driver.rs` (`L25-152`): pinned `1.98.0-nightly (f8a08b688 2026-05-30)` analysis-callback driver.
- **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):**
  - Used for all Lean kernel checks and `MetaM` environment audits.

### 2. Preserved Package Support Artifacts

All evidence artifacts are preserved inside this report package under `support/`:

| Artifact Path | Size | Lines | SHA-256 Digest | Role |
| :--- | ---: | ---: | :--- | :--- |
| `support/probe_mir_validator_ssa_locals_and_check_pointers.py` | 26,471 B | 900 | `0fa3f02441d4f1e3319555a30b433fcac73acf8d09d5b6efe982649f007943f1` | Standalone Python 3.10+ differential probe driver executing `rustc` (`V1`–`V12`, `S1`–`S3`, `P1`–`P3`) and `cargo miri` (`S1`) inside a `TemporaryDirectory` |
| `support/probe_results.json` | 45,546 B | 409 | `ddc11473f9b6062ffcdd1ae1820f0d522b4d5d821dad9bf7276cefcbfa40ae57` | Recorded JSON receipts (exit codes, sanitized `broken MIR` diagnostics, `GVN`/`CopyProp`/`CheckAlignment`/`CheckNull` MIR dumps, native & Miri outputs) acquired `2026-11-23` |
| `support/MirValidatorPhaseAutomatonAndSsaLocalsSoundness.lean` | 93,502 B | 2,253 | `4bd795c1ffab43e0b0d36a7c28765981b890727ffc4ee3c6c0bf4f2d9c708ed0` | Standalone `Init`-only Lean `v4.34.1` formalization (20 exported theorems, 842 constants) |

### 3. Execution Receipts (`2026-11-23`)

1. **Differential `rustc` & Miri execution:**
   ```console
   python3 support/probe_mir_validator_ssa_locals_and_check_pointers.py support/probe_results.json
   ```
   - Environment: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `miri 0.1.0 (14210df0e2 2026-05-31)`, `x86_64-unknown-linux-gnu`, `RUST_BACKTRACE=0`, `MIRIFLAGS=-Zmiri-tree-borrows`.
   - Observed summary:
     - `V1`: `rc=1`, `E0425: cannot find value bb0 in this scope`.
     - `V2`–`V12`: all 11 exited `rc=101` with `has_broken_mir: true` matching the exact diagnostic strings in Table `2.4`.
     - `S1`: `compile_rc=0`, native `rc=0` stdout `FREEZE=43 CELL=100`, Miri `rc=0` stdout `FREEZE=43 CELL=100`, `freeze_folded_const_43_in_gvn: true`, `non_freeze_folded_const_43_in_gvn: false`.
     - `S2`: `compile_rc=0`, native `rc=0` stdout `TEMP=12 ARG=9 SAME_ADDR=false`, `CopyProp` MIR dumps confirming temp-chain absorption into `_0`, `Arg` preservation (`_0 = copy _1`), and `borrowed_locals` non-merging of `_3 = copy _2`.
     - `S3`: `rc=0`, `has_broken_mir: false` (unreachable block survives `SsaLocals` under `-Zmir-opt-level=2`).
     - `P1`: `CheckAlignment` modified `read_u32`, `read_zst`, `borrow_zst`, `read_u8_field` and left `read_u8` and `borrow_u8_field` unchanged; `CheckNull` modified all 6 functions (using `SizedTypeProperties>::SIZE != 0` on non-borrows and `const true` on `borrow_zst` and `borrow_u8_field`).
     - `P2`: `misaligned` (`rc=-6`), `null` (`rc=-6`), `null_zst_borrow` (`rc=-6`), `null_zst_read` (`rc=0`, `ZST_READ_OK`), `misaligned_borrow_u8_field` (`rc=0`, `BORROW_U8_FIELD=170`).
     - `P3`: `compile_rc=0`, `has_broken_mir: false`, `CheckAlignment.changed: false`, `CheckNull.changed: false` on `Call(RET = sink(copy (*_1)))`.

2. **Strict Lean `v4.34.1` kernel check and environment audit:**
   ```console
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MirValidatorPhaseAutomatonAndSsaLocalsSoundness.lean
   ```
   - Exit code: `0` (zero errors, zero warnings).
   - `MetaM` kernel audit across all `842` module constants: `UNSAFE_REC_COUNT=0`, `FORBIDDEN_AXIOM_DECL_COUNT=0`, `ALL_AXIOMS_USED=[propext, Quot.sound]`.
   - Static source scan outside comments: `0` occurrences each of `sorry`, `omega`, `bv_decide`, `native_decide`, `partial`, `Classical`, `deriving`, `axiom`, `admit`.

## Revalidation

Use the following narrow, cheap checks when upgrading `rustc`, Lean 4, or Anneal's MIR capture boundary:

1. **Re-run the live `rustc` & Miri differential probe (~10 seconds):**
   ```console
   python3 support/probe_mir_validator_ssa_locals_and_check_pointers.py /tmp/reval_probe.json
   ```
   Check for behavioral drift against `support/probe_results.json`:
   - If `V1` changes from `E0425` to `broken MIR`, `mir!` has gained explicit start-block binding.
   - If `P2.null_zst_borrow` stderr changes from `"null pointer dereference occurred"` to a null-reference-specific message, the executed toolchain has picked up `137d1d49458b`'s `AssertKind::NullReferenceConstructed` split (`check_null.rs:66`).
   - If `P3` flips from `changed: false` to `changed: true`, `check_pointers.rs` has been fixed to visit terminators as well as statements.
   - If `S1.freeze_folded_const_43_in_gvn` or `S1.non_freeze_folded_const_43_in_gvn` changes, inspect `ssa.rs` and `gvn.rs` for changes to `is_freeze` handling or GVN folding policy.

2. **Targeted upstream source diff check against `137d1d49458b73b7b85d2c1599d8730886d65e47`:**
   ```console
   git diff 137d1d49458b73b7b85d2c1599d8730886d65e47..HEAD -- \
     compiler/rustc_mir_transform/src/validate.rs \
     compiler/rustc_mir_transform/src/ssa.rs \
     compiler/rustc_mir_transform/src/check_pointers.rs \
     compiler/rustc_mir_transform/src/check_alignment.rs \
     compiler/rustc_mir_transform/src/check_null.rs \
     compiler/rustc_mir_transform/src/pass_manager.rs \
     compiler/rustc_middle/src/mir/syntax.rs
   ```
   Specifically inspect diffs touching:
   - `validate.rs:1636-1639` (whether `FIXME(explicit_tail_calls)` has been replaced with actual `TailCall` ABI/signature validation);
   - `validate.rs:294-335, 956-965, 1157-1164` and `pass_manager.rs:403-413` (whether `Analysis(PostCleanup)` validation skip or the `syntax.rs` vs. `validate.rs` phase threshold discrepancies were reconciled);
   - `ssa.rs:77-81, 228-292, 327-345` (any change to `is_freeze` demotion, `Operand::Move` handling, or `RETURN_PLACE` re-rooting);
   - `check_pointers.rs:74-88` (whether `finder.visit_terminator` was added) and `check_alignment.rs:22` (whether `tcx.types.unit` was added to `excluded_pointees`).

3. **Re-verify the Lean 4 mechanization (~7 seconds):**
   ```console
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MirValidatorPhaseAutomatonAndSsaLocalsSoundness.lean
   ```
   To re-audit axioms and `._unsafe_rec` counts on a newer Lean version, prepend `import Lean`, append a `MetaM` loop over `env.constants.map₂` checking `(n.toString.splitOn "_unsafe_rec").length > 1` and `Lean.collectAxioms n`, and assert `UNSAFE_REC_COUNT=0` and `FORBIDDEN_AXIOM_DECL_COUNT=0`.

4. **Anneal capture boundary check:**
   Diff `joshlf/anneal` from `c131b320eeeb26ef692e5afd5ec8db49ee518613` on `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs` to check whether `BodyStaticAdmitted` adds CFG/cleanup-automaton checks, whether `AssertKind` adds `NullReferenceConstructed`, or whether `driver.rs` begins capturing MIR at `Runtime(PostCleanup)` with an explicit `validate_body` invocation.
