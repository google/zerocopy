# `rustc` Post-Borrowck and Pre-Codegen MIR Lowerings: `CleanupPostBorrowck`, `ElaborateBoxDerefs`, `CheckMutRestriction`, `RemoveNoopLandingPads`, and `AddCallGuards`

## Summary

This report establishes primary-source, empirical (`rustc` + Miri), and kernel-checked (`Lean v4.34.1`) ground truth for five coupled `rustc_mir_transform` passes spanning the `Built`, `Analysis(PostCleanup)`, `Runtime(Initial)`, `Runtime(PostCleanup)`, and `Runtime(Optimized)` MIR phases in `rust-lang/rust`, comparing `rust-lang/rust` HEAD (`ce66487ebbd7541212d22d01c39a808057d69f1f`) against `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), normative rules in `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`), and the `Runtime(PostCleanup)` capture boundary in `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`).

Core findings to retain:

1. **`CleanupPostBorrowck` (`PassPolicy::Required`, `Analysis(Initial) -> Analysis(PostCleanup)`) is the mandatory administrative-erasure boundary that discharges borrowck-only MIR constructs before runtime lowering and validation.** At `ce66487ebbd7541212d22d01c39a808057d69f1f`, it overwrites `AscribeUserType`, `Assign((_, Rvalue::Ref(_, BorrowKind::Fake(_), _)))`, `FakeRead`, `BackwardIncompatibleDropHint`, and post-analysis `Coverage` statements (`CoverageKind::is_removed_after_analysis()`, i.e. `Point` and `BlockMarker`, while preserving `VirtualCounter`) with `StatementKind::Nop` via `statement.make_nop(true)` (`drop_debuginfo = true`); lowers exactly `PointerCoercion::{ArrayToPointer, MutToConstPointer}` to `CastKind::PtrToPtr` (leaving `Unsize`, `ReifyFnPointer`, `UnsafeFnPointer`, and `ClosureFnPointer` intact); collapses `FalseEdge` and `FalseUnwind` to `TerminatorKind::goto(real_target)` with explicit `body.basic_blocks.invalidate_cfg_cache()` whenever any terminator changed; and clears `body.user_type_annotations.raw` and every `decl.user_ty`. Live `rustc 1.98.0-nightly` MIR dumps confirm exact conservation (`12 FakeRead + 1 &fake + 5 AscribeUserType = 18 nop`; `2 falseEdge + 1 falseUnwind` increasing `goto` count `6 -> 9`; `1 ArrayToPointer + 1 MutToConstPointer` increasing `PtrToPtr` count `0 -> 2`; `1 Unsize` preserved; `4 Coverage::BlockMarker -> 4 nop` with `7 Coverage::VirtualCounter` preserved).
2. **`ElaborateBoxDerefs` (`PassPolicy::Required`, `Runtime(Initial)`) splits basic-block `Box` dereference lowering from 4-level `VarDebugInfo` expansion—and evolved between `14210df0e` and `ce66487eb` to close a real Miri UB-elision soundness gap.** Because `NonNull<T>` wraps `pattern_type!(*const T is !null)` (`PatternKind::NotNull`), which cannot be field-projected in runtime basic blocks, basic-block `ElaborateBoxDerefs` must stop before the pattern type and emit a transmute to `*const T` (always an immutable raw pointer, relying on `Derefer` having moved every `PlaceElem::Deref` to projection index `0`). By contrast, `VarDebugInfo` iterates arbitrarily nested projections and expands every `Box` dereference into four nested `Field(0)` projections (`Unique`/`BoxRaw` -> `NonNull` -> `(*const T) is !null` -> `*const T`) plus `Deref`, empirically confirmed verbatim on live `rustc 1.98.0-nightly`. Crucially, `1.98.0-nightly` (`14210df0e`) projected two fields (`Unique -> NonNull`) and emitted generic `CastKind::Transmute`; live Miri execution (`0.1.0 (14210df0e)`) empirically demonstrates that generic `Transmute` silently exits `rc = 0` (`UNALIGNED_BOX_RAW_DEREF_MOD4=1`) on `&raw const (*b)` for a local `Box<u32>` holding an unaligned non-null pointer—violating `PassPolicy::Required`'s "must not remove any UB" rule. At `ce66487eb`, `Box<T, A>` replaced `Unique<T>` with `alloc::boxed::BoxRaw<T>`, basic-block `ElaborateBoxDerefs` projects only one field (`Field(0, BoxRaw<T>)`), and emits dedicated `CastKind::BoxDerefTransmute`, whose interpreter rule (`rustc_const_eval/src/interpret/cast.rs:206-214`) reconstructs `Ty::new_box(*self.tcx, pointee_ty)` and executes `self.deref_pointer(&ptr)?` to preserve full `Box<T>` dereferenceability and alignment UB checks while `rustc_codegen_ssa` compiles it identically to `CastKind::Transmute`.
3. **`CheckMutRestriction` (`MirLint` in `mir_built`, absent in `14210df0e`, active at `ce66487eb`) enforces `#![feature(mut_restriction)]` across three MIR surfaces while intentionally permitting whole-ADT replacement.** At `ce66487eb`, `check_mut_restriction.rs` checks: (i) `visit_const_operand` for first-class tuple-struct/variant `FnDef` constructors (`DefKind::Ctor`), preventing function-pointer bypasses; (ii) `visit_place` for every `PlaceContext::is_mutating_use()` whose projection chain contains `ProjectionElem::Field` on a `ty::Adt` base (catching nested indexing like `s.arr[0] = 42` while intentionally permitting whole-ADT overwrite `*s = inner::S::new(99)` because zero `ProjectionElem::Field` elements occur); and (iii) `visit_rvalue` for `Rvalue::Aggregate(AggregateKind::Adt)` checking all fields via `RestrictionKind::stricter_of` fold on structs/enums, but checking only the `active_field` on unions. Live execution on `1.98.0-nightly` (`14210df0e`) proves a sharp version boundary: the parser already accepted `#![feature(mut_restriction)]` syntax with an `incomplete_features` warning, yet `check_mut_restriction.rs` did not yet exist, so all seven test cases compiled fail-open with `rc = 0`.
4. **`RemoveNoopLandingPads` and `AddCallGuards::CriticalCallEdges` are tightly coupled across two pipeline positions (`Analysis(PostCleanup) -> Runtime(Initial)` and `Runtime(Optimized)` pre-codegen) and a post-monomorphization codegen hook.** Codegen emits LLVM `invoke` for `UnwindAction::{Cleanup(_), Terminate(_)}` (`generates_invoke == true`) and places post-call `lifetime_end` and `store_return` at the start of the normal-return successor block (`rustc_codegen_ssa/src/mir/block.rs:294-309`); any critical edge (`pred_count[dest] > 1`) would violate SSA dominance and corrupt non-call paths. When `RemoveNoopLandingPads` rewrites an empty/drop-flag-only cleanup pad to `UnwindAction::Continue`, `generates_invoke` flips from `true` to `false` and `AddCallGuards::CriticalCallEdges` splits zero edges (`5 -> 5` and `4 -> 4` live on `critical_noop_lp`), whereas a live `Drop` guard keeps `Cleanup` active and forces a trampoline split (`8 -> 9` and `7 -> 8` live on `critical_real_drop_guard`). Similarly, `InlineAsm` splits critical targets if and only if `self == CriticalCallEdges && has_outputs && (has_labels || generates_invoke(unwind))` (confirmed live across four positive/negative `asm!` discriminators, including `options(may_unwind)` retaining a split even under `-C panic=abort`). Diffing `14210df0e` against `ce66487eb` also exposes a real `PassPolicy` bug fix: in `14210df0e`, `WithMinOptLevel::is_enabled` ignored its inner pass's `is_enabled`, causing `o1(RemoveNoopLandingPads)` to execute even under `-C panic=abort`, whereas `ce66487eb`'s `PassPolicy::optional(ctx.panic_strategy().unwinds())` composes opt-level and panic-strategy gating cleanly and adds `find_noop_landing_pads_for_instance` to prune monomorphically trivial `DropGlue(_, None)` pads during codegen.
5. **All four core properties are mechanically verified in standalone Lean `v4.34.1`** (`support/CleanupBoxDerefsMutRestrictionAndCallGuardsSoundness.lean`, `2,658` LOC, `169` unique declarations, `18` exported theorems) under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec` constants, and `0` module axioms (depending solely on `[]`, `[propext]`, or `[propext, Quot.sound]`).

---

## Applicability

### Examined Subjects and Their Relationships

This report combines five durable subjects recorded in `REPORT.json`, linked in a four-way relationship (**cross-revision upstream audit**, **live execution**, **normative/TCB alignment**, and **mechanized soundness**):

| Subject | Exact Revision / Version | Role in This Report |
| :--- | :--- | :--- |
| `rust-lang/rust` (HEAD) | `ce66487ebbd7541212d22d01c39a808057d69f1f` | Primary-source authority for all five passes (`cleanup_post_borrowck.rs`, `elaborate_box_derefs.rs`, `check_mut_restriction.rs`, `add_call_guards.rs`, `remove_noop_landing_pads.rs`), pass manager (`lib.rs`, `pass_manager.rs`, `validate.rs`), `BoxRaw<T>` / `NonNull<T>` library definitions, `CastKind::BoxDerefTransmute` Miri/codegen handlers, and `RestrictionKind` / `PlaceContext` definitions. |
| `rust-lang/rust` (`1.98.0-nightly`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly 2026-05-31`, `miri 0.1.0 2026-05-31`, `LLVM 22.1.6`, `x86_64-unknown-linux-gnu`) | Both primary-source diff baseline and **live empirical execution host** for `support/probe_cleanup_box_mut_and_call_guards.py` (MIR dumps, `cargo miri` Stacked Borrows & Tree Borrows runs, `panic=unwind` vs `panic=abort` runs, and `-C instrument-coverage -Z coverage-options=branch` runs). |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative language-level specification for pointer coercions (`src/type-coercions.md`), visibility/module ancestor hierarchy (`src/visibility-and-privacy.md`), and destructor/unwinding semantics (`src/destructors.md`). |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Target verification TCB whose `Runtime(PostCleanup)` capture contract (`Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `TrustedBoundary.lean`) depends directly on these passes. |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `x86_64-unknown-linux-gnu`) | Proof kernel checking `support/CleanupBoxDerefsMutRestrictionAndCallGuardsSoundness.lean` and its `.olean` axiom/`_unsafe_rec` environment audit. |

### Cross-Revision Scope Matrix: Shared vs. Divergent Behaviors

Do not assume continuity across `rustc` nightlies; the two audited revisions (`14210df0e` vs. `ce66487eb`) share core CFG/statement lowering invariants while diverging in four material ways:

| Subsystem / Pass | Shared Across `14210df0e` and `ce66487eb` | Specific to `14210df0e` (`rustc 1.98.0-nightly`) | Specific to `ce66487eb` (`rust-lang/rust` HEAD) |
| :--- | :--- | :--- | :--- |
| **`CleanupPostBorrowck`** | Mandatory pass in `run_analysis_cleanup_passes`; erases `AscribeUserType`, `Fake` borrow, `FakeRead`, `BackwardIncompatibleDropHint` to `Nop` via `make_nop(true)`; lowers `ArrayToPointer` and `MutToConstPointer` to `PtrToPtr`; preserves `Unsize`; collapses `FalseEdge`/`FalseUnwind` to `Goto` with `invalidate_cfg_cache()`; clears `user_type_annotations` and `decl.user_ty`. | Hardcodes `CoverageKind::{BlockMarker, SpanMarker}` removal; uses `fn is_required(&self) -> bool { true }`. | Delegates coverage filtering to `CoverageKind::is_removed_after_analysis()` (`Point \| BlockMarker`, preserving `VirtualCounter`); uses `fn policy(&self, _) -> PassPolicy { PassPolicy::Required }`. |
| **`ElaborateBoxDerefs`** | Mandatory pass in `run_runtime_lowering_passes` after `Derefer`/`ElaborateDrops`/`EraseDerefTemps` and before `StateTransform`; relies on `Derefer` placing `Deref` at index `0` in basic blocks; expands `VarDebugInfo` places via 4 nested `Field(0)` projections through `PatternKind::NotNull` + `Deref`. | `Box<T, A>(Unique<T>, A)`; basic blocks project 2 fields (`Unique -> NonNull`) and emit generic `CastKind::Transmute`; Miri silently misses unaligned/dangling `Box` UB under `&raw const (*b)`. | `Box<T, A>(BoxRaw<T>, A)` (`BoxRaw` wraps `NonNull`); basic blocks project 1 field (`BoxRaw<T>`) and emit `CastKind::BoxDerefTransmute`; Miri checks full `Box<T>` validity via `deref_pointer` (`interpret/cast.rs:206-214`); codegen treats it as `Transmute`. |
| **`CheckMutRestriction`** | `#![feature(mut_restriction)]` surface syntax parses (`pub mut(in path) field: Ty`). | **Pass absent** (`check_mut_restriction.rs` returns 404); all restricted mutations, aggregates, and tuple-ctor `FnDef` values compile fail-open (`rc = 0`). | Active `MirLint` in `mir_built` (`lib.rs:424`) enforcing all 3 surfaces (`visit_const_operand`, `visit_place`, `visit_rvalue`) via `RestrictionKind` (`ty/mod.rs:285-342`) while permitting whole-ADT overwrite. |
| **`RemoveNoopLandingPads`** | Postorder traversal (`traversal::postorder`) pruning empty/marker/local-write landing pads to `UnwindAction::Continue` and folding jumps to a clean `resume_block`; runs at both `Analysis(PostCleanup)` and `Runtime(Optimized)`. | `is_required() = true` combined with `is_enabled() = panic_strategy().unwinds()`; `WithMinOptLevel::is_enabled` drops inner `is_enabled`, so `o1(RemoveNoopLandingPads)` still executes under `-C panic=abort`; `Drop` always returns `false`. | `PassPolicy::optional(ctx.panic_strategy().unwinds())` composes properly with `WithMinOptLevel::policy`; adds post-monomorphization `find_noop_landing_pads_for_instance` hook pruning `Drop` with trivial `ShimKind::DropGlue(_, None)` during codegen. |
| **`AddCallGuards`** | Mandatory pass (`AllCallEdges` / `CriticalCallEdges` enum); active pipeline runs `CriticalCallEdges` twice (`run_runtime_lowering_passes` before `ElaborateDrops`, and final `run_optimization_passes` after `SimplifyCfg::Final`); saturating `u8` `pred_count`; identical `generates_invoke` and `InlineAsm` splitting conditions. | `fn is_required(&self) -> bool { true }`. | `fn policy(&self, _) -> PassPolicy { PassPolicy::Required }`; `TerminatorKind::goto(target)` constructor helper. |

### Invocation Modes, Host Constraints, and Scope Limits

- **Live execution coverage:** Empirical probes ran on `x86_64-unknown-linux-gnu` with `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)` across `--edition=2021`, `-C opt-level=0` and `-C opt-level=2`, `-C debuginfo=2`, `-C panic=unwind` and `-C panic=abort`, `-C instrument-coverage -Z coverage-options=branch`, default Miri Stacked Borrows, and `-Zmiri-tree-borrows`.
- **No live execution on `ce66487eb`:** Because the local execution host carries `rustc 1.98.0-nightly (14210df0e)`, all claims specific to `ce66487eb` (`CastKind::BoxDerefTransmute`, `BoxRaw<T>`, `CheckMutRestriction` diagnostic enforcement, and `find_noop_landing_pads_for_instance`) rest on direct primary-source inspection plus mechanized Lean modeling—not live execution of a `ce66487eb` binary. `support/probe_cleanup_box_mut_and_call_guards.py` is written to run identically on a `ce66487eb`-era toolchain to execute those discriminators directly.
- **Inline assembly architecture constraint:** The live `asm!` critical-edge probes (`asm_label_with_output`, `asm_label_no_output`, `asm_may_unwind_with_output`, `asm_may_unwind_no_output`) use x86-64 instructions (`add`, `jmp`, `nop`) and unstable features `#![feature(asm_goto_with_outputs, asm_unwind)]`; the MIR-level splitting predicate in `add_call_guards.rs:57-76` is target-independent.

---

## Findings

### 1. MIR Pipeline Placement and `PassPolicy` Phase Boundaries

**Basis:** source (`rust-lang/rust@ce66487eb` `compiler/rustc_mir_transform/src/{lib.rs,pass_manager.rs}`, `rust-lang/rust@14210df0e` `compiler/rustc_mir_transform/src/{lib.rs,pass_manager.rs}`) + execution (`rustc 1.98.0-nightly`).

The five passes do not run as a contiguous block; instead, they punctuate the full progression from raw built MIR to codegen-ready optimized MIR (`compiler/rustc_mir_transform/src/lib.rs:395-838` at `ce66487eb`):

```text
mir_built (MirPhase::Built, lib.rs:395-433)
  ├── [EARLY EXIT if trivial_const(tcx, def, || &body).is_some() — skips ALL lints!]
  ├── LintAndRemoveUninhabited
  ├── Lint(CheckForceInline), Lint(CheckCallRecursion), Lint(CheckPackedRef),
  │   Lint(CheckConstItemMutation),
  ├── Lint(CheckMutRestriction)                       <-- [PASS 3: line 424, MirLint]
  ├── Lint(FunctionItemReferences), SimplifyCfg::Initial, Lint(SanityCheck)
  ▼
mir_promoted -> MirPhase::Analysis(AnalysisPhase::Initial) (lib.rs:436-498)
  ├── PromoteTemps, SimplifyCfg::PromoteConsts, InstrumentCoverage
  ├── mir_borrowck (lib.rs:553) & check_liveness (lib.rs:568)
  ▼
run_analysis_cleanup_passes -> Analysis(PostCleanup) (lib.rs:642-656)
  ├── ImpossibleClauses
  ├── CleanupPostBorrowck                             <-- [PASS 1: line 645, Required]
  ├── RemoveNoopLandingPads                           <-- [PASS 5a: line 646, Optional(unwinds)]
  ├── SimplifyCfg::PostAnalysis                       <-- collapses dead blocks after false-edge removal
  ├── Derefer                                         <-- establishes Deref-first invariant for Box
  └── PostAnalysisNormalize                           <-- enters TypingMode::PostAnalysis
  ▼
run_runtime_lowering_passes -> Runtime(Initial) (lib.rs:659-681, run_passes_no_validate)
  ├── AddCallGuards::CriticalCallEdges                <-- [PASS 4a: line 662, Required, for ElaborateDrops]
  ├── Subtyper, ElaborateDrops, Lint(CheckDropRecursion),
  ├── AbortUnwindingCalls, AddMovesForPackedDrops, EraseDerefTemps,
  ├── ElaborateBoxDerefs                              <-- [PASS 2: line 676, Required]
  └── StateTransform (coroutines), Lint(KnownPanicsLint)
  ▼
run_runtime_cleanup_passes -> Runtime(PostCleanup) (lib.rs:684-698)
  ├── LowerIntrinsics, RemovePlaceMention, SimplifyCfg::PreOptimizations
  └── Clear decl.local_info   <== [MIRI / CTFE / ANNEAL CAPTURE BOUNDARY]
  ▼
run_optimization_passes -> Runtime(Optimized) (lib.rs:700-789)
  ├── CheckAlignment, CheckNull, CheckEnums, LowerSliceLenCalls, InstSimplify,
  │   ForceInline, Inline, RemoveStorageMarkers, RemoveZsts, RemoveUnneededDrops,
  │   UnreachableEnumBranching, SROA, GVN, JumpThreading, ...
  ├── o1(RemoveNoopLandingPads)                       <-- [PASS 5b: line 770, Optional(unwinds && opt>=1)]
  ├── o1(SimplifyCfg::Final)                          <-- line 771 (destroys earlier call guards!)
  ├── StripDebugInfo, CopyProp, DSE::Final, DestinationPropagation,
  │   TailCopyToMove, MoveElimination, SimplifyLocals::Final, MultipleReturnTerminators,
  └── AddCallGuards::CriticalCallEdges                <-- [PASS 4b: line 782, Required, pre-codegen!]
  ▼
rustc_codegen_ssa::mir::codegen_mir (codegen_ssa/src/mir/mod.rs:220)
  └── tcx.find_noop_landing_pads_for_instance(...)    <-- [PASS 5c: post-monomorphization DropGlue hook]
```

#### `PassPolicy` Contract and the `WithMinOptLevel` Bug Fix (`14210df0e` -> `ce66487eb`)

At `ce66487eb`, `compiler/rustc_mir_transform/src/pass_manager.rs:88-107` replaces the legacy two-method `MirPass::{is_required, is_enabled}` API with an explicit two-variant `PassPolicy`:

```rust
pub(crate) enum PassPolicy {
    /// Passes using this cannot be disabled via any means. They must not remove any UB,
    /// as they will run in Miri. They must also come with a comment justifying why they must always run.
    Required,
    Optional {
        enabled_by_default: bool,
    },
}
```

And `WithMinOptLevel::policy` (`pass_manager.rs:224-232`) enforces two invariants by construction:
1. Wrapping a `PassPolicy::Required` pass in `WithMinOptLevel` ICEs (`bug!("required pass cannot be gated by an opt level")`).
2. Wrapping `PassPolicy::Optional { enabled_by_default }` conjoins `enabled_by_default && ctx.mir_opt_level() >= self.0`.

By contrast, in `14210df0e` (`pass_manager.rs:160-181`), `RemoveNoopLandingPads` declared both `is_required() -> true` and `is_enabled(sess) -> sess.panic_strategy().unwinds()`, while `WithMinOptLevel::is_enabled` implemented only `sess.mir_opt_level() >= self.0 as usize`—silently discarding `self.1.is_enabled(sess)`! Live execution on `rustc 1.98.0-nightly (14210df0e)` with `-C opt-level=2 -C panic=abort -Z dump-mir=RemoveNoopLandingPads` directly observed this bug: phase `2-1-003.RemoveNoopLandingPads` was skipped (`0` dumps), yet phase `3-2-026.RemoveNoopLandingPads` (wrapped in `o1(...)`) still executed (`1` dump pair for every function in the crate). At `ce66487eb`, changing `RemoveNoopLandingPads::policy` to `PassPolicy::optional(ctx.panic_strategy().unwinds())` (`remove_noop_landing_pads.rs:18`) resolved both the `is_required` contradiction and the `WithMinOptLevel` composition bug.

Note also that `Lint<T>::policy` (`pass_manager.rs:205-207`) returns `PassPolicy::optional(true)`, meaning `-Z mir-enable-passes=-CheckMutRestriction` can disable `CheckMutRestriction` on nightly, and `mir_built` skips all `MirLint`s—including `CheckMutRestriction`—for `trivial_const` items (`lib.rs:403-408`).

---

### 2. `CleanupPostBorrowck`: Administrative Statement Erasure, Coercion Lowering, and False-Edge Collapsing

**Basis:** normative (`rust-lang/reference@c9cc32825` `src/type-coercions.md`) + source (`rust-lang/rust@ce66487eb` `cleanup_post_borrowck.rs:1-90`, `coverage.rs:119-129`, `statement.rs:28-43`, `validate.rs:296-325, 479-498, 1157-1162, 1314-1345`, `codegen_ssa/src/mir/block.rs:1794-1796`) + execution (`rustc 1.98.0-nightly`) + derived (Lean theorem `cleanupPostBorrowck_bisim`).

#### Exact Transformation Rules (`cleanup_post_borrowck.rs:26-90`)

`CleanupPostBorrowck` iterates over `body.basic_blocks.as_mut_preserves_cfg().iter_mut()` (avoiding eager CFG-cache invalidation on the common path where no false edges exist) and applies four orthogonal rewrites:

| MIR Element | Input Pattern (`cleanup_post_borrowck.rs`) | Output After `CleanupPostBorrowck` | MIR Validator Enforcement (`validate.rs`) |
| :--- | :--- | :--- | :--- |
| **Administrative statements** (lines 33-38) | `AscribeUserType(..)`, `Assign((_, Rvalue::Ref(_, BorrowKind::Fake(_), _)))`, `FakeRead(..)`, `BackwardIncompatibleDropHint { .. }` | `statement.make_nop(true)` (`StatementKind::Nop`, dropping any stmt debuginfo) | `AscribeUserType` (`validate.rs:296-302`), `FakeRead` (`304-310`), `BorrowKind::Fake` (`1157-1162`) forbidden for `phase >= Runtime(Initial)`. |
| **Post-analysis coverage markers** (lines 39-41) | `StatementKind::Coverage(ref kind) if kind.is_removed_after_analysis()` (`Point` or `BlockMarker`, `coverage.rs:123-128`; in `14210df0e`: `BlockMarker \| SpanMarker`) | `statement.make_nop(true)` (`StatementKind::Nop`); **`CoverageKind::VirtualCounter` is preserved** | Forbidden for `phase >= Analysis(PostCleanup)` (`validate.rs:318-323`). |
| **Pointer coercions** (lines 42-58) | `Assign((_, Rvalue::Cast(CastKind::PointerCoercion(ArrayToPointer \| MutToConstPointer, _), ..)))` | `*cast_kind = CastKind::PtrToPtr`; **all other `PointerCoercion` variants (`Unsize`, `ReifyFnPointer`, `UnsafeFnPointer`, `ClosureFnPointer`) are preserved** | `MutToConstPointer` (`validate.rs:1326-1328`) and `ArrayToPointer` (`1340-1342`) forbidden for `phase >= Analysis(PostCleanup)`. |
| **Phantom borrowck terminators** (lines 64-77) | `TerminatorKind::FalseEdge { real_target, .. }` or `TerminatorKind::FalseUnwind { real_target, .. }` | Sets `invalidate_cfg = true` and rewrites `terminator.kind = TerminatorKind::goto(real_target)`; calls `body.basic_blocks.invalidate_cfg_cache()` if `invalidate_cfg` is true | Forbidden for `phase >= Runtime(Initial)` (`validate.rs:479-498`); codegen ICEs `bug!("borrowck false edges in codegen")` (`codegen_ssa/src/mir/block.rs:1794-1796`). |
| **User type metadata** (lines 79-83) | `body.user_type_annotations.raw` and `decl.user_ty` on every local | `raw.clear()` and `decl.user_ty = None` | Prevents post-borrowck passes from observing borrowck-only canonical user-type annotations. |

#### Semantic Justification of Each Rewrite

1. **Why `make_nop(true)` instead of `Vec::remove` (`statement.rs:29-42`):** Replacing a statement in-place with `StatementKind::Nop` is $O(1)$ per statement and preserves `Location { block, statement_index }` indices for any sideband data structures; passing `drop_debuginfo = true` explicitly suppresses `StatementKind::as_debuginfo()` (which would ICE because administrative statements have no debuginfo lowering).
2. **Why ONLY `ArrayToPointer` and `MutToConstPointer` lower to `PtrToPtr`:** Normatively (`rust-lang/reference@c9cc32825` `src/type-coercions.md`, `r[coerce.types.mut-pointer]` for `*mut T -> *const T`, plus `as`-cast array-to-element-pointer decay), both coercions are representation-preserving thin-pointer casts whose sole distinction from `CastKind::PtrToPtr` exists during borrowck to track pointee lifetime variance (`cleanup_post_borrowck.rs:53-56`). By contrast, `PointerCoercion::Unsize` (`r[coerce.types.unsize]`, `r[coerce.unsize.slice]`) constructs fat-pointer metadata (slice length or vtable pointer) and MUST remain `PointerCoercion::Unsize` through codegen and Miri; `ReifyFnPointer` / `ClosureFnPointer` materialize function-pointer addresses from zero-sized `FnDef`/closure items.
3. **Why `validate.rs` enforces phase thresholds unevenly:** Notice an architectural subtlety directly visible in `validate.rs`: `Coverage` removable markers (`validate.rs:318`) and `PointerCoercion::{MutToConstPointer, ArrayToPointer}` (`validate.rs:1326, 1340`) are rejected immediately at `MirPhase::Analysis(AnalysisPhase::PostCleanup)`, whereas `AscribeUserType` (`297`), `FakeRead` (`305`), `FalseEdge` (`480`), `FalseUnwind` (`490`), and `BorrowKind::Fake` (`1158`) are only rejected starting at `MirPhase::Runtime(RuntimePhase::Initial)` (while `BackwardIncompatibleDropHint` has no phase rejection in `validate.rs:333`!). This asymmetry matters for custom drivers or MIR-injection tests: even though `CleanupPostBorrowck` erases all of them at `Analysis(PostCleanup)`, the validator's hard gate for `FakeRead`/`FalseEdge`/`FalseUnwind`/`Fake` borrows triggers one phase later.

#### Live `rustc 1.98.0-nightly` Empirical Conservation Measurements

Compiling `cleanup_full_matrix` (containing a `DropGuard`, typed `let` bindings, `arr as *const u32`, `*mut u32 -> *const u32`, `&[u32; 4] -> &[u32]`, a `match` guard `Some(v) if *v > 10`, and a `loop { break; }`) and `cov_branch` (`if a && b { 1 } else { 2 }` under `-C instrument-coverage -Z coverage-options=branch`) on `rustc 1.98.0-nightly (14210df0e)` with `-Z dump-mir=CleanupPostBorrowck` yields exact conservation across every category (`support/probe_results.json`):

| MIR Metric | `cleanup_full_matrix` Before (`2-1-002`) | `cleanup_full_matrix` After (`2-1-002`) | Exact Conservation / Delta |
| :--- | ---: | ---: | :--- |
| `FakeRead(...)` | `12` | `0` | `-12` -> `nop;` |
| `&fake` (`BorrowKind::Fake`) | `1` | `0` | `-1` -> `nop;` |
| `AscribeUserType(...)` | `5` | `0` | `-5` -> `nop;` |
| `nop;` statements | `0` | `18` | `+18 = 12 + 1 + 5` (exact!) |
| `user_ty:` annotations table entries | `10` | `0` | `-10` (table cleared + all local `as UserTypeProjection` stripped) |
| `falseEdge ->` | `2` | `0` | `-2` -> `goto -> real_target;` |
| `falseUnwind ->` | `1` | `0` | `-1` -> `goto -> real_target;` |
| `goto -> bbN;` terminators | `6` | `9` | `+3 = 2 + 1` (exact!) |
| `PointerCoercion(ArrayToPointer, ...)` | `1` | `0` | `-1` -> `(PtrToPtr)` |
| `PointerCoercion(MutToConstPointer, ...)` | `1` | `0` | `-1` -> `(PtrToPtr)` |
| `(PtrToPtr)` casts | `0` | `2` | `+2 = 1 + 1` (exact!) |
| `PointerCoercion(Unsize, ...)` | `1` | `1` | `0` (intentionally preserved!) |
| Basic block count (`bb_count`) | `25` | `25` | `0` (unreachable imaginary blocks removed later by `SimplifyCfg::PostAnalysis`) |

And on `cov_branch` with `-C instrument-coverage -Z coverage-options=branch`:

| Coverage Metric | `cov_branch` Before (`2-1-002`) | `cov_branch` After (`2-1-002`) | Conservation |
| :--- | ---: | ---: | :--- |
| `Coverage::BlockMarker(...)` | `4` | `0` | `-4` -> `nop;` |
| `nop;` statements | `0` | `4` | `+4` (exact!) |
| `Coverage::VirtualCounter(...)` | `7` | `7` | `0` (all runtime counters preserved!) |

---

### 3. `ElaborateBoxDerefs`: `CastKind::BoxDerefTransmute` Stopping Before `NonNull<T>` Pattern Types vs. 4-Level `VarDebugInfo` Expansion

**Basis:** source (`rust-lang/rust@ce66487eb` `elaborate_box_derefs.rs:1-157`, `library/alloc/src/boxed.rs:238-241, 308-311`, `library/core/src/ptr/non_null.rs:75-80`, `rustc_middle/src/mir/syntax.rs:1520-1529`, `rustc_const_eval/src/interpret/cast.rs:192-218`, `rustc_codegen_ssa/src/mir/rvalue.rs:618-623`, `validate.rs:677-684, 1435-1445`; `rust-lang/rust@14210df0e` `elaborate_box_derefs.rs:1-167`, `boxed.rs:234-237`) + execution (`rustc 1.98.0-nightly` + `miri 0.1.0`) + derived (Lean theorems `elaborateBoxDerefs_preserves_place_eval`, `legacyTransmute_elides_unaligned_raw_deref_ub`, `elaborateVarDebug_four_level_expansion_and_addr_eq`).

#### Internal Field Hierarchy of `Box<T, A>` and Why Basic Blocks Stop Before `NonNull<T>`

At `rust-lang/rust@ce66487eb`, the four-layer transparent wrapper chain from `Box<T, A>` to `*const T` is:

1. `library/alloc/src/boxed.rs:308-311`: `pub struct Box<T: ?Sized, A: Allocator = Global>(BoxRaw<T>, A);` (in `14210df0e`, `boxed.rs:234-237`: `pub struct Box<T: ?Sized, A: Allocator = Global>(Unique<T>, A);`).
2. `library/alloc/src/boxed.rs:238-241`: `struct BoxRaw<T: ?Sized> { pointer: NonNull<T>, _marker: PhantomData<T> }` (replacing `core::ptr::Unique<T>`, which no longer exists at `library/core/src/ptr/unique.rs` in `ce66487eb`—notably, `elaborate_box_derefs.rs:84-98` still retains the historical variable names `unique_did`/`unique_def` and `span_bug!("expected Box to contain Unique")`!).
3. `library/core/src/ptr/non_null.rs:75-80`: `#[repr(transparent)] pub struct NonNull<T: PointeeSized> { pointer: crate::pat::pattern_type!(*const T is !null) }` (`PatternKind::NotNull`).
4. Inside the pattern type `(*const T) is !null`, field `0` yields the underlying raw pointer `*const T`.

Because `rustc`'s MIR semantics forbid runtime field projection into a `PatternKind::NotNull` pattern type inside basic blocks (`elaborate_box_derefs.rs:60-61` and `133-135`), basic-block lowering MUST use a transmute cast before reaching the pattern type. `ElaborateBoxDerefs` operates in two completely separate phases inside `run_pass`:

1. **Basic-Block Phase (`ElaborateBoxDerefVisitor::visit_place`, `elaborate_box_derefs.rs:40-75`):**
   - **Precondition from `Derefer` (`lib.rs:648`):** `Derefer` splits every nested dereference (`**bb` or `(*(*p)).0`) into a separate temporary so that `PlaceElem::Deref` can ONLY appear at `place.projection.first()` (`elaborate_box_derefs.rs:50-51`).
   - When `place.projection.first() == Some(PlaceElem::Deref)` and `base_ty.boxed_ty() == Some(boxed_ty)`:
     - Allocates a fresh temporary `ptr_local` of **immutable** raw-pointer type `ptr_ty = Ty::new_imm_ptr(tcx, boxed_ty)` (`*const T`, even when the place is mutated like `(*b).0 = ...`—in MIR, raw-pointer dereference mutability is governed by the `PlaceContext`, not `*const` vs `*mut`!).
     - **At `ce66487eb` (`elaborate_box_derefs.rs:62-68`):** Projects **ONLY 1 field** (`FieldIdx::ZERO`, type `BoxRaw<T>`) and inserts before `location`:
       ```rust
       let field_place =
           Place::from(place.local).project_to_field(FieldIdx::ZERO, &*self.local_decls, tcx);
       self.patch.add_assign(
           location,
           Place::from(ptr_local),
           Rvalue::Cast(CastKind::BoxDerefTransmute, Operand::Copy(field_place), ptr_ty),
       );
       place.local = ptr_local;
       ```
     - **At `14210df0e` (`elaborate_box_derefs.rs:65-83`):** Projected **2 fields** (`FieldIdx::ZERO` -> `Unique<T>`, then `FieldIdx::ZERO` -> `NonNull<T>` via `build_projection`) and inserted `Rvalue::Cast(CastKind::Transmute, Operand::Copy(...), ptr_ty)`.
   - Keeps `place.projection` completely untouched (still starting with `PlaceElem::Deref` followed by any field/index tail), changing only `place.local = ptr_local`. After `ElaborateBoxDerefs`, `validate.rs:677-684` rejects any `ProjectionElem::Deref` on a `Box` base type for `phase >= Runtime(Initial)`.

2. **`VarDebugInfo` Phase (`elaborate_box_derefs.rs:112-150`):**
   - Debug info is NOT rewritten by `Derefer`, so a `VarDebugInfoContents::Place` may contain `PlaceElem::Deref` on a `Box<T>` at **any depth** in its projection list.
   - `run_pass` walks `place.iter_projections()` and replaces every `Box` `Deref` with **five projection elements** (four nested `Field(0)` projections + `Deref`, `elaborate_box_derefs.rs:129-138`):
     1. `PlaceElem::Field(FieldIdx::ZERO, unique_ty)` (`BoxRaw<T>` at `ce66487eb`; `Unique<T>` at `14210df0e`)
     2. `PlaceElem::Field(FieldIdx::ZERO, nonnull_ty)` (`NonNull<T>`)
     3. `PlaceElem::Field(FieldIdx::ZERO, pat_ty)` where `pat_ty = Ty::new_pat(tcx, ptr_ty, tcx.mk_pat(PatternKind::NotNull))`
     4. `PlaceElem::Field(FieldIdx::ZERO, ptr_ty)` (`*const T`)
     5. `PlaceElem::Deref`
   - As `elaborate_box_derefs.rs:133-134` explains: *"While we can't project into a pattern type in a basic block, this is debug info where it's fine."*

#### Live Empirical Proof of Both the 4-Level `VarDebugInfo` Expansion and the `Transmute` -> `BoxDerefTransmute` Soundness Gap

Live execution of `support/probe_cleanup_box_mut_and_call_guards.py` on `rustc 1.98.0-nightly (14210df0e)` + `miri 0.1.0 (14210df0e)` empirically established three critical facts:

1. **Exact 4-level `VarDebugInfo` expansion observed verbatim (`custom_box_var_debug`, `-C debuginfo=2`):**
   ```text
   // BEFORE ElaborateBoxDerefs:
   debug inner => (*_1);
   // AFTER ElaborateBoxDerefs (2-2-009):
   debug inner => (*((((_1.0: std::ptr::Unique<u32>).0: std::ptr::NonNull<u32>).0: (*const u32) is !null).0: *const u32));
   ```
   Simultaneously, the basic block in the exact same function stopped before the pattern type:
   ```text
   bb0: {
       _2 = copy ((_1.0: std::ptr::Unique<u32>).0: std::ptr::NonNull<u32>) as *const u32 (Transmute);
       _0 = copy (*_2);
       return;
   }
   ```
2. **Basic-block coverage across sized, nested, DST slice, and ZST boxes (`box_tuple_and_nested` + Miri):**
   On `box_tuple_and_nested(Box<(u32, u32)>, Box<Box<u32>>, Box<[u32]>, Box<()>)`, `ElaborateBoxDerefs` emitted `14` transmute temporaries (`_26.._39`), all typed `*const T` (including wide `*const [u32]` for `Box<[u32]>` and `*const ()` for ZST `Box<()>`). For nested `**bb`, `Derefer` first extracted `_23 = no_retag copy (*_2)` so `ElaborateBoxDerefs` lowered outer `(*_2)` and inner `(*_23)` independently. Running `mutate_boxes` natively and under `cargo miri run` (both default Stacked Borrows and `-Zmiri-tree-borrows`) produced identical deterministic output `CHECKSUM=60` (`rc = 0` across all 3 modes) with invariant field address across mutation; negative Miri probes caught `Undefined Behavior` (`rc = 1`) for both dangling `Box::from_raw` (use-after-free) and unaligned `transmute::<*mut u32, Box<u32>>` (`required 4 byte alignment but found 1`).
3. **Empirical reproduction of the `1.98.0-nightly` `CastKind::Transmute` UB-elision bug that motivated `CastKind::BoxDerefTransmute`:**
   Consider a live local `mut b: Box<u32>` whose backing slot is temporarily overwritten via raw pointer `*mut *mut u32` with an unaligned non-null pointer (`align = 1 mod 4` inside `#[repr(align(8))] struct Aligned([u8; 8])`), dereferenced strictly under `&raw const (*b)` (which does not load memory), and then restored to the original valid pointer before `b` drops (`miri_box_transmute_raw_deref_discriminator` in `support/probe_cleanup_box_mut_and_call_guards.py`):
   - **Observed on `miri 0.1.0 (14210df0e)` (`CastKind::Transmute`):** Exits **`rc = 0`**, prints **`UNALIGNED_BOX_RAW_DEREF_MOD4=1`**, **`detected_ub = false`**! Why? Because `ElaborateBoxDerefs` emitted `copy ((_b.0: Unique<u32>).0: NonNull<u32>) as *const u32 (Transmute)` followed by `&raw const (*_tmp)`. Reading `NonNull<u32>` only validates `!null`, `CastKind::Transmute` checks only size equality and `NonNull`/`*const u32` validity, and `&raw const (*_tmp)` performs no alignment or dereferenceability check on a raw pointer. Thus `ElaborateBoxDerefs` in `14210df0e` **silently erased `Box<T>` dereference UB**, directly violating `PassPolicy::Required`'s requirement (`pass_manager.rs:91`: *"They must not remove any UB, as they will run in Miri"*).
   - **Closed at `ce66487eb` (`CastKind::BoxDerefTransmute`):** `compiler/rustc_middle/src/mir/syntax.rs:1521-1528` defines `CastKind::BoxDerefTransmute` specifically so that *"if the input would not be valid as `Box<T>`, the cast is UB. Backends that do not care about UB detection can treat this like a regular transmute."* In `compiler/rustc_const_eval/src/interpret/cast.rs:206-214`, Miri/CTFE executes:
     ```rust
     if matches!(cast_kind, CastKind::BoxDerefTransmute) {
         // Do the extra UB checking by making the input an actual `Box<T>` pointer
         // and dereferencing it.
         let ptr = self.read_immediate(src)?;
         let pointee_ty = cast_ty.builtin_deref(true).unwrap();
         let box_ty = Ty::new_box(*self.tcx, pointee_ty);
         let ptr = ptr.transmute(self.layout_of(box_ty)?, self)?;
         self.deref_pointer(&ptr)?;
     }
     ```
     Meanwhile `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:618-620` lowers `CastKind::Transmute | CastKind::BoxDerefTransmute | CastKind::Subtype` identically via `self.codegen_transmute_operand(bx, operand, cast)`, incurring zero runtime overhead. (`validate.rs:1435-1444` additionally checks that `BoxDerefTransmute`'s input and target are `Sized` and that `target_type.is_raw_ptr()`.)

---

### 4. `CheckMutRestriction`: Three-Surface Access Control vs. Permitted Whole-ADT Overwrite

**Basis:** normative (`rust-lang/reference@c9cc32825` `src/visibility-and-privacy.md`) + source (`rust-lang/rust@ce66487eb` `check_mut_restriction.rs:1-161`, `lib.rs:403-424`, `rustc_middle/src/ty/mod.rs:285-342`, `rustc_middle/src/mir/visit.rs:1336-1440`) + execution (`rustc 1.98.0-nightly` fail-open version-boundary check) + derived (Lean theorem `checkMutRestriction_blocks_field_mut_and_ctor_fn_permits_whole_adt`).

#### Restriction Lattice (`rustc_middle/src/ty/mod.rs:285-342`)

Field mutability restrictions under `#![feature(mut_restriction)]` are represented by:

```rust
pub enum RestrictionKind {
    Unrestricted,
    Restricted(DefId, Span),
}
```

- `is_allowed_in(self, module: DefId, tcx)`: returns `true` for `Unrestricted`, and `tcx.is_descendant_of(module, restricted_to)` for `Restricted(restricted_to, _)` (`ty/mod.rs:293-300`), matching Rust's module-tree visibility hierarchy (`rust-lang/reference` `r[vis.name-hierarchy]`, `r[vis.access]`).
- `stricter_of(self, rhs, tcx)` (`ty/mod.rs:328-341`): treats `Unrestricted` as the identity element; when both operands are `Restricted(left_did, _)` and `Restricted(right_did, _)`, asserts `left_did.krate == right_did.krate` and returns `if tcx.is_descendant_of(left_did, right_did) { self } else { rhs }`.
  - **Key algebraic precondition (mechanized in Lean `restriction_stricterOf_chain_sound` & `foldStricter_sound`):** `stricter_of` computes a sound meet (`isAllowedIn m (stricterOf r1 r2) ↔ isAllowedIn m r1 ∧ isAllowedIn m r2`) **if and only if** `left_did` and `right_did` are comparable in the module tree! Because every `mut(in path)` annotation on fields of a single ADT must name an ancestor of that ADT's defining module, all field restrictions on a single ADT lie on a single root-to-ADT ancestor chain and are pairwise comparable. If two incomparable sibling modules were ever passed to `stricter_of`, the `else { rhs }` branch would silently discard `left_did`!

#### Exact Three-Surface Enforcement (`check_mut_restriction.rs:11-161`)

`CheckMutRestriction` runs as `&Lint(check_mut_restriction::CheckMutRestriction)` in `mir_built` (`lib.rs:424`), immediately exiting if `body.tainted_by_errors.is_some()` (`check_mut_restriction.rs:13-15`). It tracks `self.mutating_span` updated on each `visit_statement` and `visit_terminator`, and checks exactly three MIR surfaces:

| Surface | Visitor Method (`check_mut_restriction.rs`) | What Triggers the Check | Restriction Computation | Diagnostic Emitted |
| :--- | :--- | :--- | :--- | :--- |
| **Surface 1: Tuple constructor as first-class value** | `visit_const_operand` (lines 39-70) | `ty::FnDef(def_id, _)` where `tcx.def_kind(def_id)` is `DefKind::Ctor(CtorOf::Struct \| CtorOf::Variant, _)` | Folds `stricter_of` across ALL `variant.fields`; rejects if `!mut_restriction.is_allowed_in(body_did, tcx)` | `ConstructionOfTyWithMutRestrictedField` (using `constant.span`) |
| **Surface 2: Mutating place projection** | `visit_place` (lines 72-118) | `context.is_mutating_use()` (`PlaceContext::MutatingUse(Store \| SetDiscriminant \| AsmOutput \| Call \| Yield \| Drop \| Borrow \| RawBorrow \| Projection)`, `visit.rs:1336-1440`) AND `place.iter_projections()` contains `ProjectionElem::Field(field_idx, _)` whose `place_base.ty` is `ty::Adt(adt_def, _)` | Checks `variant_def.fields[field_idx].mut_restriction.is_allowed_in(body_did, tcx)` individually for each ADT field projection in the chain | `MutOfRestrictedField` (using `self.mutating_span`) |
| **Surface 3: ADT aggregate construction** | `visit_rvalue` (lines 120-160) | `Rvalue::Aggregate(AggregateKind::Adt(adt_did, variant_idx, _, _, active_field), _)` | If `active_field == Some(field_idx)` (**union**): checks ONLY `variant.fields[*field_idx].mut_restriction`. If `None` (**struct / enum variant**): folds `stricter_of` across ALL `variant.fields`. | `ConstructionOfTyWithMutRestrictedField` (using `self.mutating_span`) |

#### Four Non-Obvious Consequences Verified from Primary Source

1. **Why whole-ADT overwrite (`*s = inner::S::new(99)`) is intentionally permitted outside `crate::inner`:** In MIR, assigning to `*s` (`Place { local: _1, projection: [Deref] }`) or `s` (`projection: []`) has `context = PlaceContext::MutatingUse(Store)`, so `visit_place` enters the loop over `place.iter_projections()` (`lines 76-114`), encounters zero `ProjectionElem::Field` elements (only `Deref` or empty), and emits zero errors! This matches Rust's encapsulation model: a caller outside `crate::inner` can replace an entire `S` value with another legitimately constructed `S` (produced via `inner::S::new(99)` inside `crate::inner`, preserving all module invariants), while being blocked from mutating `s.x` in-place or forging a fresh `S { x: ..., y: ... }` outside `crate::inner`.
2. **Why deep projections (`s.arr[0] = 42`, closure-captured fields) are caught:** As `check_mut_restriction.rs:77-94` documents, `s.arr[0]` produces `[Deref, Field(arr), Index(0)]`, which still contains `ProjectionElem::Field` with base `ty::Adt(S)`; similarly, mutating an ADT field through a closure capture has a separate `Field` projection whose base type is `ty::Adt(S)` (while the closure's own field projection has `ty::Closure` and is skipped at line 92).
3. **Why `visit_const_operand` is indispensable:** Writing `let ctor: fn(u32) -> inner::Tup = inner::Tup;` outside `crate::inner` never emits an `Rvalue::Aggregate(AggregateKind::Adt)` in the caller's MIR—it emits a `ConstOperand` of type `ty::FnDef(Tup_ctor_def_id)` (whose synthetic MIR body `shim::build_adt_ctor` lives in `mir_for_ctfe` / `optimized_mir` and bypasses `mir_built` completely!). Without `visit_const_operand` (`lines 39-70`), taking `inner::Tup` as a function item or coercing it to `fn(u32) -> inner::Tup` would completely bypass `CheckMutRestriction`!
4. **Union active-field precision (`lines 128-140`):** When constructing a `union U { pub a: u32, pub mut(in crate::inner) b: u32 }`, `Rvalue::Aggregate` carries `active_field = Some(field_idx)`. `visit_rvalue` checks ONLY `variant.fields[*field_idx]`: initializing `U { a: 1 }` outside `crate::inner` is allowed even though `b` is restricted, whereas `U { b: 1 }` is rejected.
5. **Empirical version boundary on `rustc 1.98.0-nightly (14210df0e)`:** Running all seven `CheckMutRestriction` test cases (`direct_field_mut_err`, `index_proj_field_mut_err`, `struct_aggregate_err`, `tuple_ctor_fn_val_err`, `whole_struct_overwrite_allowed`, `union_unrestricted_field_allowed`, `union_restricted_field_err`) on `rustc 1.98.0-nightly (14210df0e)` empirically established **`status = "syntax_accepted_lint_absent_fail_open"`**: all seven files compiled with `rc = 0` and only the warning `the feature mut_restriction is incomplete and may not be safe to use and/or cause compiler crashes` (issue `#105077`). Any downstream tool pinning to a pre-`check_mut_restriction.rs` nightly cannot rely on `#![feature(mut_restriction)]` enforcement.

---

### 5. `RemoveNoopLandingPads` and `AddCallGuards::CriticalCallEdges`: Invoke Splitting, `InlineAsm` Edges, and Codegen Coupling

**Basis:** normative (`rust-lang/reference@c9cc32825` `src/destructors.md`) + source (`rust-lang/rust@ce66487eb` `remove_noop_landing_pads.rs:1-185`, `add_call_guards.rs:1-140`, `lib.rs:646, 662, 770-782`, `rustc_codegen_ssa/src/mir/{mod.rs:220, block.rs:278-315, 340-405}`) + execution (`rustc 1.98.0-nightly`, `panic=unwind` and `panic=abort`) + derived (Lean theorems `removeNoopLandingPads_flips_generatesInvoke`, `removeNoopLandingPads_preserves_unwind_outcome`, `addCallGuards_eliminates_invoke_critical_edges_and_preserves_semantics`).

#### `RemoveNoopLandingPads` Exact Admissibility and Post-Monomorphization Extension (`remove_noop_landing_pads.rs:14-185`)

1. **Early skip (`lines 27-34`):** If no block in `body` terminates with `TerminatorKind::UnwindResume`, the pass returns immediately without allocating a `DenseBitSet`.
2. **Postorder analysis (`find_noop_landing_pads`, `lines 166-185`):** Iterates `traversal::postorder(body)` in a single pass (not a worklist fixpoint). On acyclic cleanup DAGs, every successor is visited before its predecessor; on a cyclic landing pad, back-edges conservatively see `false` in `nop_landing_pads`.
3. **Statement admissibility (`is_nop_landing_pad`, `lines 84-113`):**
   - **Admitted:** `FakeRead`, `StorageLive`, `StorageDead`, `PlaceMention`, `AscribeUserType`, `Coverage`, `ConstEvalCounter`, `BackwardIncompatibleDropHint`, `Nop`, AND `Assign((place, Rvalue::Use(..) | Rvalue::Discriminant(_)))` **if and only if `place.as_local().is_some()`** (lines 98-105: writing to a local drop flag has no observable effect when the frame unwinds and dies, whereas writing through a dereference/projection mutates memory outside the dying frame!).
   - **Rejected (`return false`):** Any `Assign` with a non-local LHS or non-`Use`/`Discriminant` RHS, any `SetDiscriminant`, and any `Intrinsic`.
4. **Terminator admissibility (`lines 115-152`):**
   - `Goto`, `UnwindResume`, `SwitchInt`, `FalseEdge`, `FalseUnwind`: noop iff `terminator.successors().all(|succ| nop_landing_pads.contains(succ))` (vacuously `true` for `UnwindResume`).
   - **`TerminatorKind::Drop { place, .. }` (`lines 124-142`, NEW in `ce66487eb` vs. `14210df0e`):** During generic MIR passes (`extra = None`), always returns `false`. When invoked via `tcx.find_noop_landing_pads_for_instance(mir, instance, typing_env)` in `rustc_codegen_ssa/src/mir/mod.rs:220` (`extra = Some((instance, typing_env))`), instantiates `place.ty` for the concrete monomorphization, calls `Instance::resolve_drop_glue(tcx, ty)`, and if `drop_fn.def` is `ShimKind::DropGlue(_, None)` (trivial empty drop glue), admits the block iff all successors are in `nop_landing_pads`!
   - All other terminators (`Call`, `TailCall`, `Assert`, `InlineAsm`, `Return`, `UnwindTerminate`, `Unreachable`, `CoroutineDrop`, `Yield`): always `false`.
5. **Rewrite (`lines 44-70`):** Ensures a clean statement-free `resume_block` via `MirPatch::resume_block()`, then for every block:
   - Rewrites `UnwindAction::Cleanup(unwind_bb)` to **`UnwindAction::Continue`** whenever `nop_landing_pads.contains(unwind_bb)` (never alters `UnwindAction::Terminate(_)`!).
   - Folds any remaining successor `*target != resume_block` with `nop_landing_pads.contains(*target)` directly to `resume_block`.

#### `AddCallGuards::CriticalCallEdges` Exact Conditions and Codegen Dominance Necessity (`add_call_guards.rs:25-140`, `codegen_ssa/src/mir/block.rs:278-405`)

`AddCallGuards` computes saturating `u8` predecessor counts `pred_count[succ] = pred_count[succ].saturating_add(1)` over **all** `data.terminator().successors()` (counting both normal and unwind cleanup edges, lines 34-39), and defines (`lines 135-140`):

```rust
fn generates_invoke(unwind: UnwindAction) -> bool {
    match unwind {
        UnwindAction::Continue | UnwindAction::Unreachable => false,
        UnwindAction::Cleanup(_) | UnwindAction::Terminate(_) => true,
    }
}
```

It splits edges into fresh trampoline blocks `BasicBlockData::new(Terminator { source_info, kind: TerminatorKind::goto(old_dest) }, src.is_cleanup)` (inheriting the source block's `is_cleanup` flag, `lines 89-120`) in exactly two cases:

1. **`TerminatorKind::Call { target: Some(destination), unwind, .. }` (`lines 50-56`):**
   Split iff `pred_count[destination] > 1 && (generates_invoke(unwind) || self == &AllCallEdges)`.
   - **Why codegen requires this (`rustc_codegen_ssa/src/mir/block.rs:278-315`):** When `generates_invoke(unwind)` is `true`, codegen emits an LLVM `invoke` terminator. Because `invoke` terminates the caller's LLVM basic block, codegen cannot emit post-call argument `lifetime_end` intrinsics or `fx.store_return(bx, ret_dest, &fn_abi.ret, invokeret)` inside the caller block; instead, `block.rs:295-308` calls `bx.switch_to_block(fx.llbb(target))`, emits `lifetime_end` and `store_return` at the head of `target`, and updates `fx.cached_llbbs[target]`. If `target` had another predecessor (`pred_count[target] > 1`), non-call paths entering `target` would execute `store_return(invokeret)`—violating LLVM SSA dominance (since `invokeret` does not dominate `target`) and corrupting `ret_dest`! When `generates_invoke(unwind)` is `false` (`Continue` or `Unreachable`), codegen emits a non-terminator LLVM `call` (`block.rs:312`), placing `lifetime_end` and `store_return` directly in the caller block before branching to `target`.
2. **`TerminatorKind::InlineAsm { asm_macro: InlineAsmMacro::Asm, targets, operands, unwind, .. }` (`lines 57-76`):**
   Split **only when `self == &CriticalCallEdges`** (excluded under `AllCallEdges` and excluded for `InlineAsmMacro::NakedAsm`) iff:
   - `has_outputs`: at least one operand is `InlineAsmOperand::InOut { .. } | InlineAsmOperand::Out { .. }`, **AND**
   - `has_labels || generates_invoke(unwind)`: at least one operand is `InlineAsmOperand::Label { .. }` (lowered to LLVM `callbr`, `block.rs:366-383`) OR `generates_invoke(unwind)` is `true` (lowered to LLVM `invoke` of inline asm, `block.rs:384-400`; note `block.rs:367` asserts `unwind_target.is_none()` when labels are present).
   - When triggered, every `(target_index, target)` in `targets` with `pred_count[*target] > 1` receives its own fresh `Goto` trampoline block.
3. **Why `AddCallGuards::CriticalCallEdges` MUST run TWICE (`lib.rs:662` and `lib.rs:782`):**
   - First at `lib.rs:662` (immediately before `Subtyper` and `ElaborateDrops`) so `ElaborateDrops` can insert drop-flag updates along call return edges without polluting sibling predecessors.
   - Because `SimplifyCfg::PreOptimizations` (`lib.rs:688`) and `o1(SimplifyCfg::Final)` (`lib.rs:771`) collapse trivial `Goto` trampolines (`add_call_guards.rs:16`: *"NOTE: Simplify CFG will happily undo most of the work this pass does"*), `AddCallGuards::CriticalCallEdges` MUST run a second time at `lib.rs:782`—after the final `SimplifyCfg` and immediately before codegen.

#### Live 7-Function Empirical Matrix Across Both Pipeline Positions and Both Panic Strategies

Executing `support/probe_cleanup_box_mut_and_call_guards.py` on `rustc 1.98.0-nightly (14210df0e)` with `-C opt-level=2` under both default `panic=unwind` and `-C panic=abort` produced the exact matrix below (`support/probe_results.json`):

| Function | `panic=unwind`: `RemoveNoopLP` `cleanup` (`2-1-003` / `3-2-026`) | `panic=unwind`: `AddCallGuards` BBs (`2-2-001` / `3-2-032`) | `panic=abort`: `AddCallGuards` BBs (`2-2-001` / `3-2-032`) | Discriminating Behavior Observed |
| :--- | :---: | :---: | :---: | :--- |
| `critical_noop_lp` | `2->0` / `0->0` | `5->5 (0)` / **`4->4 (0)`** | `6->7 (+1)` / **`4->4 (0)`** | `RemoveNoopLP` flips `Cleanup -> Continue` (`generates_invoke: true -> false`), preventing any split under `unwind`. Under `panic=abort`, skipping `2-1-003` leaves a transient `2-2-001` split (`6->7`) before `AbortUnwindingCalls` + `SimplifyCfg` reduce final `3-2-032` to `4->4 (0)`. |
| `critical_real_drop_guard` | `3->2` / `2->1` | `8->9 (+1)` / **`7->8 (+1)`** | `8->9 (+1)` / **`5->5 (0)`** | Live `Drop` guard keeps `unwind: bb6`/`bb5` (`generates_invoke = true`) and `pred_count[bb3] = 2`, inserting trampoline `bb7: goto -> bb3` under `unwind`; under `panic=abort`, `AbortUnwindingCalls` turns Rust-ABI call unwind into `Unreachable`, eliminating the final split (`5->5`). |
| `non_critical_invoke_single_pred` | `3->2` / `2->1` | `6->6 (0)` / **`5->5 (0)`** | `6->6 (0)` / **`3->3 (0)`** | Active `Cleanup` pad (`generates_invoke = true`), but `pred_count[dest] = 1` -> **0 splits** at all phases! |
| `asm_label_with_output` | `1->0` / `0->0` | `7->8 (+1)` / **`4->5 (+1)`** | `8->9 (+1)` / **`4->5 (+1)`** | `has_outputs && has_labels` is `true` and `pred_count[bb2] = 2` -> **splits (`+1`)** under BOTH `unwind` and `abort`! |
| `asm_label_no_output` | `0->0` / `0->0` | `6->6 (0)` / **`4->4 (0)`** | `6->6 (0)` / **`4->4 (0)`** | `has_labels` is `true` and `pred_count > 1`, but `has_outputs = false` -> **0 splits**! |
| `asm_may_unwind_with_output` | `2->1` / `2->1` | `8->8 (0)` / **`6->7 (+1)`** | `8->8 (0)` / **`6->7 (+1)`** | At `2-2-001`, `StorageDead(_6)` block gives `pred_count = 1` (`0` splits); after `RemoveStorageMarkers` + `SimplifyCfg`, `asm!` directly targets join block `bb2` (`pred_count = 2`), so final `3-2-032` **splits (`6->7`) under BOTH `unwind` AND `panic=abort`** (because `options(may_unwind)` retains active unwinding cleanup/terminate)! |
| `asm_may_unwind_no_output` | `2->1` / `2->1` | `8->8 (0)` / **`7->7 (0)`** | `8->8 (0)` / **`7->7 (0)`** | `generates_invoke = true`, but `has_outputs = false` -> **0 splits**! |

---

### 6. `joshlf/anneal` TCB Seam Analysis (`Runtime(PostCleanup)` Capture Boundary)

**Basis:** source (`joshlf/anneal@c131b320e` `trusted/lean/Trusted/MirAst.lean:466-476, 608-663, 682-698, 773-795`, `trusted/lean/Trusted/MirSemantics.lean:61-77, 133-149, 916-955`, `trusted/correspondence/Trusted/Correspondence.lean:1317`, `trusted/audit/TrustedBoundary.lean`) + derived.

Auditing `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` directly against `rustc`'s pass pipeline exposes four concrete TCB boundary contracts:

1. **Exact capture phase (`Runtime(PostCleanup)`):** `Trusted/MirAst.lean:53` and `Trusted/Correspondence.lean:1317` pin Anneal's MIR semantics to `MirPhase::Runtime(RuntimePhase::PostCleanup)` (the output of `mir_drops_elaborated_and_const_checked`, `lib.rs:608-637`). Consequently:
   - **`CleanupPostBorrowck` (`lib.rs:645`), first `RemoveNoopLandingPads` (`lib.rs:646`), `Derefer` (`lib.rs:648`), first `AddCallGuards::CriticalCallEdges` (`lib.rs:662`), `ElaborateDrops` (`lib.rs:665`), `ElaborateBoxDerefs` (`lib.rs:676`), and `SimplifyCfg::PreOptimizations` (`lib.rs:688`) have ALL already executed** before Anneal captures MIR.
   - Because `CleanupPostBorrowck` ran before capture, `Trusted/MirAst.lean:654-656, 782-785` can safely map `FakeRead`, `AscribeUserType`, `Coverage`, `BackwardIncompatibleDropHint`, `FalseEdge`, and `FalseUnwind` fail-closed to `.unsupported` without rejecting real Rust bodies—except when `-C instrument-coverage` leaves `CoverageKind::VirtualCounter` statements in `Runtime(PostCleanup)` MIR, which WILL hit `.unsupported`!
2. **`CastKind::PtrToPtr` and `CastKind::BoxDerefTransmute` fail-closed boundary:** At `c131b320e`, `Trusted/MirAst.lean:612-628` maps **all** `Rvalue::Cast` variants—including `PtrToPtr`, `Transmute`, and `BoxDerefTransmute`—fail-closed to `Rvalue.unsupported`. Whenever Anneal extends its admitted MIR fragment to cover `Box<T>` dereferences:
   - On `rustc 1.98.0-nightly` (`14210df0e`), `Runtime(PostCleanup)` MIR contains `CastKind::Transmute` from `NonNull<T>` to `*const T` (2-level field projection), which **erased `Box<T>` dereference UB** on `&raw const (*b)`. Modeling `Box` dereferences soundly on `14210df0e` cannot rely solely on `CastKind::Transmute` without losing soundness relative to Rust's `Box<T>` validity invariant.
   - On `ce66487eb`-era `rustc`, `Runtime(PostCleanup)` MIR emits `CastKind::BoxDerefTransmute` from `BoxRaw<T>` to `*const T`; any future Anneal `Trusted.MirSemantics` rule for `BoxDerefTransmute` MUST enforce full `Box<T>` non-null, live-allocation, and pointee-alignment checks (mirroring `interpret/cast.rs:206-214`) rather than collapsing it to raw-pointer `Transmute`.
3. **`deinitMovedPlace = true` and `CleanupPostBorrowck`:** `Trusted/MirSemantics.lean:67-69, 140-148, 941-951` deliberately sets `deinitMovedPlace = true` (moving a non-ZST local transitions its slot to `liveUninitSlot`). Because `CleanupPostBorrowck` operates strictly on `Copy`/administrative/cast/terminator constructs and never introduces new `Operand::Move` uses or reorders moves, our Lean formalization explicitly models move-deinitialization in `CleanupPostBorrowck.evalRvalue` and proves `cleanupPostBorrowck_bisim` holds with `deinitMovedPlace = true` enabled.
4. **Post-capture `RemoveNoopLandingPads` + `AddCallGuards::CriticalCallEdges` belong to the unverified-compiler / verified-backend seam:** Because `SimplifyCfg::PreOptimizations` (`lib.rs:688`) runs *after* the first `AddCallGuards::CriticalCallEdges` (`lib.rs:662`), `Runtime(PostCleanup)` MIR does **not** guarantee absence of critical invoke edges. Both `o1(RemoveNoopLandingPads)` (`lib.rs:770`), final `AddCallGuards::CriticalCallEdges` (`lib.rs:782`), and post-monomorphization `find_noop_landing_pads_for_instance` (`codegen_ssa/src/mir/mod.rs:220`) execute strictly *downstream* of Anneal's `Runtime(PostCleanup)` boundary; any verified Rust backend lowering from `Runtime(PostCleanup)` MIR to LLVM/SSA IR must discharge those exact critical-edge invariants before emitting `invoke`/`callbr` terminators.

---

### 7. Kernel-Checked Lean `v4.34.1` Formalization Summary

**Basis:** derived (kernel-checked Lean `v4.34.1` proof in `support/CleanupBoxDerefsMutRestrictionAndCallGuardsSoundness.lean`, `2,658` LOC, `169` unique declarations, `1,395` module constants).

All definitions are marked `noncomputable def` (matching `joshlf/anneal`'s `Trusted/MirSemantics.lean:174-181` discipline to prevent Lean's code generator from emitting `._unsafe_rec` helpers), and `Nat` boolean equality uses constructive `decide_eq_true` / `of_decide_eq_true` / `decide_eq_false` rather than `beq_self_eq_true` (which in Lean `v4.34.1` traverses `Nat.instTransOrd -> Classical.not_not -> Classical.choice`). Every exported theorem was kernel-checked under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and audited via `#print axioms` and full environment inspection (`UNSAFE_REC_COUNT=0`, `UNSAFE_CONST_COUNT=0`, `PARTIAL_CONST_COUNT=0`, `MODULE_AXIOMS_COUNT=0`):

| Namespace & Exported Theorem | What It Mechanically Establishes | Kernel Axioms |
| :--- | :--- | :--- |
| `CleanupPostBorrowck.cleanupPostBorrowck_bisim` | Exact fuel-indexed multi-step trace, return-value, and observable `covTrace` bisimulation (`runCfg (cleanupPostBorrowck body) fuel bb st = runCfg body fuel bb st`) with explicit move deinitialization (`deinitMovedPlace`). | `[propext]` |
| `CleanupPostBorrowck.cleanupPostBorrowck_post_invariants` | `bodyPostBorrowckClean (cleanupPostBorrowck body) = true`: zero `AscribeUserType`, `FakeRead`, `Fake` borrow, `BackwardIncompatibleDropHint`, removable `Coverage`, `ArrayToPointer`, `MutToConstPointer`, `FalseEdge`, `FalseUnwind`, `userTypeAnnotations`, or `localUserTys`. | `[propext]` |
| `CleanupPostBorrowck.cleanupPostBorrowck_idempotent` | `cleanupPostBorrowck (cleanupPostBorrowck body) = cleanupPostBorrowck body`. | `[propext]` |
| `CleanupPostBorrowck.cleanupPostBorrowck_preserves_unsize_and_virtual_counter` | Negative-space preservation: `PointerCoercion.unsize` is not rewritten to `ptrToPtr`, and `CoverageKind.virtualCounter` is not erased to `nop`. | `[propext]` |
| `ElaborateBoxDerefs.elaborateBoxDerefs_preserves_place_eval` | Basic-block 1-field `BoxRaw` + `CastKind::BoxDerefTransmute` preserves both resolved `(addr, allocId)` on valid boxes and `.ub` on null/dangling/unaligned boxes across arbitrary field tails. | `[propext]` |
| `ElaborateBoxDerefs.elaborateBoxDerefs_removes_box_deref` | Post-pass `hasDirectBoxDeref` is `false` (satisfying `validate.rs:681-683`). | `[propext]` |
| `ElaborateBoxDerefs.legacyTransmute_elides_unaligned_raw_deref_ub` | Constructive separation witness (`addr = 4097`, `align = 4`): direct `Box` deref and `BoxDerefTransmute` both return `.ub`, while legacy `NonNull` `Transmute` silently returns `.ok 4097 1`. | `[propext]` |
| `ElaborateBoxDerefs.elaborateVarDebug_four_level_expansion_and_addr_eq` | `VarDebugInfo` expands `Box` dereference into the exact 4-level `Field(0)` chain (`BoxRaw -> NonNull -> pat(!null) -> *const T`) + `Deref` and preserves evaluated allocation address. | `[propext]` |
| `CheckMutRestriction.restriction_stricterOf_chain_sound` & `foldStricter_sound` | Under transitive module descent and ancestor-chain comparability, `foldStricter` allows `bodyMod` iff every field's restriction allows `bodyMod`. | `[propext]` |
| `CheckMutRestriction.checkMutRestriction_blocks_field_mut_and_ctor_fn_permits_whole_adt` | Joint 4-part theorem: (1) rejects any mutating use containing a restricted ADT `Field` projection at any depth; (2) rejects restricted struct/enum aggregates and tuple-ctor `FnDef` const operands; (3) checks only `active_field` on unions; (4) unconditionally permits whole-ADT overwrites with zero `Field` projections. | `[propext]` |
| `CheckMutRestriction.concrete_mut_restriction_witness` | Concrete decision witness verifying union active-field precision, whole-ADT `*s` overwrite permission, restricted `(*s).0` rejection, and tuple-ctor `FnDef` rejection. | `[]` (axiom-free!) |
| `CallGuardsAndLandingPads.removeNoopLandingPads_flips_generatesInvoke` | Rewriting `UnwindAction.cleanup bb` for `bb ∈ nopSet` produces `.continue_` and flips `generatesInvoke` from `true` to `false`. | `[propext]` |
| `CallGuardsAndLandingPads.removeNoopLandingPads_preserves_unwind_outcome` | Unwinding through any acyclic verified noop landing-pad DAG (including post-monomorphization trivial `Drop`) preserves exact heap state and produces `.unwound st.heap`, identical to `UnwindAction.continue_`. | `[propext]` |
| `CallGuardsAndLandingPads.addCallGuards_no_invoke_critical_edges` | Proves exact predecessor-count conservation on all original blocks `k < cfg.length`, exact unit predecessor count (`= 1`) on all fresh trampoline blocks `k ∈ [cfg.length, cfg'.length)`, and zero remaining critical `Call` invoke or `InlineAsm` output-target edges (`CfgNoCriticalEdges`). | `[propext, Quot.sound]` |
| `CallGuardsAndLandingPads.addCallGuards_sim_forward` | Proves stuttering forward operational simulation (`EvalCfg cfg bb st out → EvalCfg (addCallGuards mode cfg) bb st out`) across all 11 terminator transition rules including split `Call` and multi-target `InlineAsm` trampolines. | `[propext, Quot.sound]` |
| `CallGuardsAndLandingPads.addCallGuards_eliminates_invoke_critical_edges_and_preserves_semantics` | Combined theorem unifying `CfgNoCriticalEdges`, predecessor-count conservation, unit trampoline predecessor counts, and operational semantics preservation. | `[propext, Quot.sound]` |
| `CallGuardsAndLandingPads.concrete_call_guards_and_noop_lp_witness` | Concrete MIR witness matching live probes (`cfgInvoke`: `6->7`, `removeNoopLandingPads` + `addCallGuards` on `cfgNoop`: `5->5`, `cfgAsmOut`: `4->5`, `cfgAsmNoOut`: `4->4`). | `[propext]` |

---

## Boundaries

To prevent over-generalization, negative space is classified using the exact four `reference-corpus/1` boundary categories:

1. **Known not to apply:**
   - **`CheckMutRestriction` enforcement on `rustc 1.98.0-nightly (14210df0e)`:** Live execution proved that `#![feature(mut_restriction)]` compiles fail-open (`rc = 0`) on `14210df0e` because `check_mut_restriction.rs` had not yet landed. The three-surface enforcement findings apply to `ce66487eb` (and toolchains including `check_mut_restriction.rs`), **known not to apply** to `14210df0e`.
   - **`CastKind::BoxDerefTransmute` and `BoxRaw<T>` on `rustc 1.98.0-nightly (14210df0e)`:** `14210df0e` uses `Box(Unique<T>, A)` and generic `CastKind::Transmute`; `BoxDerefTransmute` is **known not to apply** to `14210df0e`.
   - **`CheckMutRestriction` on `trivial_const` items or with `-Z mir-enable-passes=-CheckMutRestriction`:** Because `mir_built` early-exits for `trivial_const` (`lib.rs:403-408`) and `Lint<T>::policy` is `PassPolicy::optional(true)` (`pass_manager.rs:205-207`), `CheckMutRestriction` is **known not to apply** in those two cases.
   - **`AddCallGuards::CriticalCallEdges` on `InlineAsmMacro::NakedAsm`, non-output `asm!`, or single-predecessor invokes:** Source (`add_call_guards.rs:50-76`) and live execution prove splitting is **known not to apply** to `naked_asm!`, `asm!` without `Out`/`InOut` operands, or calls/asm targets with `pred_count[target] <= 1`.
   - **`CleanupPostBorrowck` on `PointerCoercion::Unsize` and `CoverageKind::VirtualCounter`:** Source and live MIR dumps prove erasure/lowering is **known not to apply** to `Unsize` coercions or `VirtualCounter` statements.
   - **Standalone Lean formalization vs. live `joshlf/anneal` TCB proof:** `support/CleanupBoxDerefsMutRestrictionAndCallGuardsSoundness.lean` is a standalone formalization over faithful pass-specific abstract machines; it does **not** import `joshlf/anneal`'s `Trusted.MirSemantics`, does not model full Stacked/Tree Borrows aliasing provenance, and does not prove backward simulation (`EvalCfg cfg' → EvalCfg cfg`) or divergence preservation for `AddCallGuards`. Do not cite it as a direct proof over `Trusted.MirSemantics` or full LLVM IR.
2. **Unsupported:**
   - **Runtime field projection into `PatternKind::NotNull` pattern types inside MIR basic blocks:** Explicitly **unsupported** by `rustc`'s MIR semantics (`elaborate_box_derefs.rs:60-61, 133-135`), which is the exact structural reason basic-block `ElaborateBoxDerefs` uses a transmute while `VarDebugInfo` projects all four levels.
   - **Combined `InlineAsm` `label` + active `unwind_target`:** Explicitly **unsupported** in `rustc_codegen_ssa/src/mir/block.rs:367` (`assert!(unwind_target.is_none())`).
   - **Live execution of `CastKind::BoxDerefTransmute` and `CheckMutRestriction` diagnostics on the `1.98.0-nightly (14210df0e)` host toolchain:** **Unsupported** on the installed `14210df0e` compiler binary itself (requiring a newer nightly carrying those commits to execute the `ce66487eb` path dynamically).
3. **Not examined:**
   - **Windows MSVC SEH funclet cleanup-ret trampolines (`llbb_with_cleanup`, `codegen_ssa/src/mir/block.rs:100-131`):** Only inspected briefly at source level; no live Windows MSVC/SEH binaries or LLVM IR were compiled or executed.
   - **`Cranelift` and `rustc_codegen_gcc` backends' consumption of `AddCallGuards::CriticalCallEdges` and `BoxDerefTransmute`:** Only `rustc_codegen_ssa` (shared SSA/LLVM frontend) was audited; Cranelift/GCC backend-specific lowering was **not examined**.
   - **Custom allocators `Box<T, A>` where `A` is non-ZST or has non-trivial `Drop`:** `ElaborateBoxDerefs` only projects `FieldIdx::ZERO` (independent of `FieldIdx::ONE: A`), but live Miri execution only tested the default `Global` allocator; custom non-ZST `A` layouts were **not examined**.
   - **`BackwardIncompatibleDropHint` live generation under Edition 2024 lint scenarios:** Verified in `cleanup_post_borrowck.rs:36-38` and `validate.rs:333`, and mechanized in Lean, but no Edition 2024 drop-order hint snippet was executed live.
   - **Non-`x86_64` inline assembly targets (AArch64 / RISC-V):** Live `asm!` probes executed only on `x86_64-unknown-linux-gnu`.
4. **Unknown:**
   - **Whether any future `rustc` refactor will allow `PatternKind::NotNull` projection in basic blocks or remove `CastKind::BoxDerefTransmute`:** Resolved as **unknown** (depends on upstream stabilization/evolution of pattern types and `Box` lang-item semantics).
   - **Whether `CheckMutRestriction` will eventually reject incompatible sibling-module restrictions at HIR/typeck time (or whether `RestrictionKind::stricter_of` is strictly protected by HIR ancestor-only validation for all future syntax extensions, e.g., multiple visibility/mutability modifiers):** Only `RestrictionKind::stricter_of` (`ty/mod.rs:328-341`) and `check_mut_restriction.rs` were audited; HIR parsing/resolution enforcement of ancestor-only `mut(in path)` was not exhaustively audited, so whether any edge case can reach `stricter_of` with incomparable modules remains **unknown** from this investigation alone.

---

## Evidence

All observations were acquired on **`2026-11-22`**. Source facts and execution outputs are separated explicitly from derived synthesis below.

### 1. Primary Upstream Source Citations (Immutable 40-Hex Revisions)

#### `rust-lang/rust` HEAD (`ce66487ebbd7541212d22d01c39a808057d69f1f`)
- `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:1-90` — `CleanupPostBorrowck::run_pass` (lines 27-84), statement erasure via `make_nop(true)` (lines 31-41), `PointerCoercion::{ArrayToPointer, MutToConstPointer} -> CastKind::PtrToPtr` (lines 42-58), `FalseEdge`/`FalseUnwind -> goto` + `invalidate_cfg_cache()` (lines 64-77), clearing `user_type_annotations` and `decl.user_ty` (lines 79-83), `PassPolicy::Required` (lines 86-89).
- `compiler/rustc_mir_transform/src/elaborate_box_derefs.rs:1-157` — `build_ptr_tys` (lines 15-27), `ElaborateBoxDerefVisitor::visit_place` 1-field `BoxRaw` projection + `CastKind::BoxDerefTransmute` (lines 40-75), `unique_def`/`nonnull_def` lookup (lines 82-98), 4-level `VarDebugInfo` expansion through `PatternKind::NotNull` (lines 112-150), `PassPolicy::Required` (lines 153-156).
- `compiler/rustc_mir_transform/src/check_mut_restriction.rs:1-161` — `CheckMutRestriction` `MirLint` + `tainted_by_errors` early exit (lines 11-19), `visit_const_operand` for `DefKind::Ctor` (lines 39-70), `visit_place` for `context.is_mutating_use()` + `ProjectionElem::Field` on `ty::Adt` (lines 72-118), `visit_rvalue` for `Rvalue::Aggregate(AggregateKind::Adt)` distinguishing union `active_field` vs. struct/enum fold (lines 120-160).
- `compiler/rustc_mir_transform/src/add_call_guards.rs:1-140` — `AddCallGuards::{AllCallEdges, CriticalCallEdges}` (lines 26-29), saturating `u8` `pred_count` (lines 34-39), `Call` splitting (lines 50-56), `InlineAsm` `has_outputs && (has_labels || generates_invoke(unwind))` splitting (lines 57-76), trampoline creation preserving `is_cleanup` (lines 89-121), `PassPolicy::Required` (lines 127-131), `generates_invoke` (lines 135-140).
- `compiler/rustc_mir_transform/src/remove_noop_landing_pads.rs:1-185` — `PassPolicy::optional(ctx.panic_strategy().unwinds())` (lines 15-19), `UnwindResume` early exit (lines 27-34), `MirPatch::resume_block()` and `Cleanup -> Continue` rewrite (lines 44-70), `is_nop_landing_pad` local-assignment vs. non-local distinction and post-monomorphization `DropGlue(_, None)` check (lines 75-153), `find_noop_landing_pads_for_instance` hook and `traversal::postorder` (lines 157-185).
- `compiler/rustc_mir_transform/src/lib.rs:395-838` — Exact phase ordering: `mir_built` (`CheckMutRestriction` at line 424, `trivial_const` skip at line 403), `run_analysis_cleanup_passes` (`CleanupPostBorrowck` line 645, `RemoveNoopLandingPads` line 646, `Derefer` line 648), `run_runtime_lowering_passes` (`AddCallGuards::CriticalCallEdges` line 662, `ElaborateBoxDerefs` line 676), `run_runtime_cleanup_passes` (`SimplifyCfg::PreOptimizations` line 688), `run_optimization_passes` (`o1(RemoveNoopLandingPads)` line 770, `o1(SimplifyCfg::Final)` line 771, final `AddCallGuards::CriticalCallEdges` line 782).
- `compiler/rustc_mir_transform/src/pass_manager.rs:88-107, 189-233` — `PassPolicy::{Required, Optional}`, `Lint<T>::policy`, and `WithMinOptLevel::policy`.
- `compiler/rustc_mir_transform/src/validate.rs:296-335, 479-498, 677-684, 1157-1162, 1314-1345, 1410-1445` — Post-pass MIR validator phase gates for administrative statements, false edges, `Box` dereferences, pointer coercions, and `BoxDerefTransmute`.
- `compiler/rustc_middle/src/mir/syntax.rs:1520-1529`, `coverage.rs:119-129`, `statement.rs:28-43`, `visit.rs:1336-1440`, `ty/mod.rs:285-342` — `CastKind::BoxDerefTransmute`, `CoverageKind::is_removed_after_analysis`, `Statement::make_nop`, `MutatingUseContext` / `PlaceContext::is_mutating_use`, and `RestrictionKind::{is_allowed_in, stricter_of}`.
- `compiler/rustc_const_eval/src/interpret/cast.rs:192-218` — Miri/CTFE `CastKind::BoxDerefTransmute` extra UB validation reconstructing `Box<T>` and calling `self.deref_pointer(&ptr)?`.
- `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:618-623`, `mod.rs:220`, `block.rs:278-315, 340-405, 1794-1796` — Codegen `BoxDerefTransmute` transmute lowering, post-monomorphization `find_noop_landing_pads_for_instance`, `invoke` post-return `switch_to_block` dominance requirement, `do_inlineasm` `callbr`/`invoke` handling, and `FalseEdge`/`FalseUnwind` ICE.
- `library/alloc/src/boxed.rs:238-241, 308-311` and `library/core/src/ptr/non_null.rs:75-80` — `Box(BoxRaw<T>, A)`, `BoxRaw { pointer: NonNull<T>, _marker }`, and `NonNull { pointer: pattern_type!(*const T is !null) }`.

#### `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, matching local `rustc 1.98.0-nightly`)
- `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:1-91` — Hardcoded `BlockMarker | SpanMarker`, `is_required() -> true`.
- `compiler/rustc_mir_transform/src/elaborate_box_derefs.rs:1-167` — 2-field `build_projection(unique_ty, nonnull_ty)` + `CastKind::Transmute` (lines 29-34, 65-83); 4-level `VarDebugInfo` expansion (lines 126-161).
- `compiler/rustc_mir_transform/src/check_mut_restriction.rs` — HTTP 404 (absent at this revision).
- `compiler/rustc_mir_transform/src/remove_noop_landing_pads.rs:1-143` and `pass_manager.rs:160-181` — `is_required() = true`, `is_enabled() = panic_strategy().unwinds()`, `WithMinOptLevel::is_enabled` ignoring inner `is_enabled`, no `find_noop_landing_pads_for_instance` hook.
- `compiler/rustc_mir_transform/src/add_call_guards.rs:1-136` — Same critical-edge splitting logic as `ce66487eb`.
- `library/alloc/src/boxed.rs:234-237` — `Box<T: ?Sized, A: Allocator = Global>(Unique<T>, A)`.

#### `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`)
- `src/type-coercions.md` (`r[coerce.types.mut-pointer]`, `r[coerce.types.ref-to-pointer]`, `r[coerce.types.unsize]`, `r[coerce.unsize.slice]`)
- `src/visibility-and-privacy.md` (`r[vis.name-hierarchy]`, `r[vis.access]`)
- `src/destructors.md` (`r[destructors.intro]`, `r[destructors.operation]`, `r[destructors.scope.intro]`)

#### `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)
- `trusted/lean/Trusted/MirAst.lean:53, 466-476, 608-663, 682-698, 773-795` — `Runtime(PostCleanup)` AST contract and `.unsupported` mappings.
- `trusted/lean/Trusted/MirSemantics.lean:61-77, 133-149, 174-181, 916-955` — `deinitMovedPlace = true` semantics and `noncomputable def` policy eliminating `._unsafe_rec`.
- `trusted/correspondence/Trusted/Correspondence.lean:1317` — `phase := .Runtime .PostCleanup`.
- `trusted/audit/TrustedBoundary.lean` — Kernel replay, axiom allowlist, and `isUnsafe`/`isPartial` rejection rules.

### 2. Package-Owned Support Artifacts and Exact Cryptographic Digests

All executable probes, recorded empirical outputs, and mechanized Lean proofs are preserved inside this report package under `support/`:

| Package Support File | Purpose | Size / LOC | SHA-256 Digest |
| :--- | :--- | ---: | :--- |
| `support/probe_cleanup_box_mut_and_call_guards.py` | Self-contained Python 3.10+ differential probe invoking live `rustc` and `cargo miri` inside `tempfile.TemporaryDirectory()` with path scrubbing. | `891` LOC / `29,509` B | `5fa1ce1ee1335a837a575bb4d51bf3e309466ac4f2c2fdd4a2b1aa310f9e0d50` |
| `support/probe_results.json` | Sanitized, reproducible JSON capture of the `2026-11-22` live execution on `rustc 1.98.0-nightly (14210df0e)` + `miri 0.1.0 (14210df0e)` (`0` leaked host paths). | `629` LOC / `51,960` B | `62b2d445cd695d3d754fb655372e6d37e704e8deca6a8147582cb11835f15dfa` |
| `support/CleanupBoxDerefsMutRestrictionAndCallGuardsSoundness.lean` | Standalone kernel-checked Lean `v4.34.1` formalization (`169` unique decls, `18` exported theorems, `0` `sorry`, `0` `Classical.choice`, `0` `omega`/`bv_decide`/`native_decide`, `0` `._unsafe_rec`). | `2,658` LOC / `120,697` B | `ce59c0c1b5df009238d2e2d61232585fa1303141b6f50727e41f4c3d1637fa17` |

### 3. Recorded Live Execution Transcript Summary (`2026-11-22`)

#### Probe Execution (`python3 support/probe_cleanup_box_mut_and_call_guards.py`, exit code `0`)
- Toolchain reported by `rustc -Vv`: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `host: x86_64-unknown-linux-gnu`, `LLVM version: 22.1.6`.
- Interpreter reported by `cargo miri --version`: `miri 0.1.0 (14210df0e 2026-05-31)`.
- `CleanupPostBorrowck`: `rc = 0`; `fake_read: 12->0`, `fake_borrow: 1->0`, `ascribe_user_type: 5->0`, `nop_stmts: 0->18`, `user_ty_decl: 10->0`, `false_edge: 2->0`, `false_unwind: 1->0`, `goto_terms: 6->9`, `coercion_array_to_ptr: 1->0`, `coercion_mut_to_const: 1->0`, `ptr_to_ptr: 0->2`, `coercion_unsize: 1->1`; `cov_branch`: `block_marker: 4->0`, `nop_stmts: 0->4`, `virtual_counter: 7->7`.
- `ElaborateBoxDerefs`: `rc = 0`; `uses_generic_transmute = true`, `uses_unique_nonnull_chain = true`, `uses_box_deref_transmute = false`, `var_debug_has_pattern_not_null = true` (`debug inner => (*((((_1.0: std::ptr::Unique<u32>).0: std::ptr::NonNull<u32>).0: (*const u32) is !null).0: *const u32));`).
- `Miri` differential `Box` suite: native binary `CHECKSUM=60` (`rc = 0`), Miri Stacked Borrows `CHECKSUM=60` (`rc = 0`), Miri Tree Borrows `CHECKSUM=60` (`rc = 0`), dangling `Box::from_raw` UB caught (`rc = 1`), unaligned `transmute` `Box<u32>` UB caught (`rc = 1`), `&raw const (*b)` unaligned-local-`Box` discriminator exited **`rc = 0` (`UNALIGNED_BOX_RAW_DEREF_MOD4=1`, `detected_ub = false`)**.
- `CheckMutRestriction`: `status = "syntax_accepted_lint_absent_fail_open"` (`7/7` test cases exited `rc = 0` with `#[warn(incomplete_features)]` only).
- `RemoveNoopLandingPads` + `AddCallGuards::CriticalCallEdges`: `rc_unwind = 0`, `rc_abort = 0`; `critical_real_drop_guard` final `3-2-032.AddCallGuards` split `bb1: may_unwind(const 1_u32) -> [return: bb7, unwind: bb5]` with fresh `bb7: { goto -> bb3; }` (`7 -> 8`, `+1`) under `unwind` and `5 -> 5` (`0`) under `abort`; `critical_noop_lp` did `4 -> 4` (`0`) under both at `3-2-032` (after transient `6 -> 7` at `2-2-001` under `abort`); `asm_label_with_output` split `4 -> 5` (`+1`) under both while `asm_label_no_output` did `4 -> 4` (`0`); `asm_may_unwind_with_output` split `6 -> 7` (`+1`) under both while `asm_may_unwind_no_output` did `7 -> 7` (`0`).

#### Lean `v4.34.1` Kernel Verification and Environment Audit (`2026-11-22`)
- Command: `LEAN_SYSROOT=~/.elan/toolchains/leanprover--lean4---v4.34.1 lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/CleanupBoxDerefsMutRestrictionAndCallGuardsSoundness.lean` -> **exit code `0`** (`0` errors, `0` warnings).
- `.olean` build + environment audit (`#print axioms` on all 18 exported theorems + `env.constants` scan over all `1,395` constants in module `CleanupBoxDerefsMutRestrictionAndCallGuardsSoundness`) -> **exit code `0`**: `UNSAFE_REC_COUNT=0`, `UNSAFE_CONST_COUNT=0`, `PARTIAL_CONST_COUNT=0`, `MODULE_AXIOMS_COUNT=0`; axioms across all 18 theorems are a strict subset of `{propext, Quot.sound}` (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`/`Lean.ofReduceNat`/`Lean.trustCompiler`).
- Syntactic forbidden-token check (comments stripped): `0` occurrences of `sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial def`, `deriving`, `_unsafe_rec`, `#eval`, and `axiom `.

---

## Revalidation

Use the following narrow, cheap checks to revalidate these findings against a newer `rustc` nightly, `Miri`, `joshlf/anneal` commit, or `Lean` release without repeating the full upstream source audit:

### 1. Re-run the Standalone `rustc` + `Miri` Differential Probe (Under 10 Seconds)

From the package directory, invoke:

```console
python3 support/probe_cleanup_box_mut_and_call_guards.py
```

Check these four discriminating assertion groups in the regenerated `support/probe_results.json`:

1. **`CleanupPostBorrowck` conservation:** `after_metrics` has `fake_read == 0`, `fake_borrow == 0`, `ascribe_user_type == 0`, `user_ty_decl == 0`, `false_edge == 0`, `false_unwind == 0`, `coercion_array_to_ptr == 0`, `coercion_mut_to_const == 0`, `coercion_unsize >= 1`, and `coverage_branch_probe.after.block_marker == 0` with `virtual_counter >= 1`.
2. **`ElaborateBoxDerefs` regime detection:**
   - On pre-`BoxDerefTransmute` toolchains (`14210df0e`): `uses_generic_transmute == true`, `uses_unique_nonnull_chain == true`, and `miri_box_transmute_raw_deref_discriminator.rc == 0` (`detected_ub == false`).
   - On `ce66487eb`-era and newer toolchains: `uses_box_deref_transmute == true`, `uses_box_raw == true`, AND `miri_box_transmute_raw_deref_discriminator.rc != 0` (`detected_ub == true` — confirming `CastKind::BoxDerefTransmute` closes the `&raw const (*b)` alignment UB hole in live Miri!).
   - On both toolchains: `var_debug_has_pattern_not_null == true`.
3. **`CheckMutRestriction` enforcement:**
   - On `ce66487eb`-era and newer toolchains: `status == "enforced"` and `all_expectations_matched == true` (all 5 restricted cases fail with `rc != 0`, while `whole_struct_overwrite_allowed` and `union_unrestricted_field_allowed` succeed with `rc == 0`).
   - Any regression to `"syntax_accepted_lint_absent_fail_open"` or `"partial_mismatch"` flags a compiler enforcement change.
4. **`RemoveNoopLandingPads` + `AddCallGuards::CriticalCallEdges` matrix:**
   - Final pre-codegen `AddCallGuards` yields `split_delta == 0` on `critical_noop_lp`, `non_critical_invoke_single_pred`, `asm_label_no_output`, and `asm_may_unwind_no_output`; and `split_delta == 1` on `critical_real_drop_guard` (under `unwind`), `asm_label_with_output` (under both `unwind` and `abort`), and `asm_may_unwind_with_output` (under both `unwind` and `abort`).
   - On `ce66487eb`-era toolchains, also verify `len(abort_remove_noop_lp) == 0` across all functions (confirming `WithMinOptLevel::policy` no longer runs `o1(RemoveNoopLandingPads)` under `-C panic=abort`).

### 2. Targeted Upstream Diff Check on `rust-lang/rust`

To detect drift between `ce66487ebbd7541212d22d01c39a808057d69f1f` and a newer `rust-lang/rust` commit `<NEW_SHA>`, diff only the eight load-bearing source files:

```console
git diff ce66487ebbd7541212d22d01c39a808057d69f1f..<NEW_SHA> -- \
  compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs \
  compiler/rustc_mir_transform/src/elaborate_box_derefs.rs \
  compiler/rustc_mir_transform/src/check_mut_restriction.rs \
  compiler/rustc_mir_transform/src/add_call_guards.rs \
  compiler/rustc_mir_transform/src/remove_noop_landing_pads.rs \
  compiler/rustc_mir_transform/src/lib.rs \
  compiler/rustc_const_eval/src/interpret/cast.rs \
  compiler/rustc_codegen_ssa/src/mir/block.rs
```

A zero diff on those eight paths establishes that all primary-source pass invariants in this report continue to hold verbatim (modulo changes to `library/alloc/src/boxed.rs` or `library/core/src/ptr/non_null.rs` layout).

### 3. Re-check the Lean `v4.34.1` Formalization and Axiom/Purity Audit (Under 15 Seconds)

Run strict kernel typechecking (disabling async elaboration and kernel-skipping, promoting all warnings to errors):

```console
LEAN_SYSROOT=~/.elan/toolchains/leanprover--lean4---v4.34.1 \
  ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/CleanupBoxDerefsMutRestrictionAndCallGuardsSoundness.lean
```

To re-verify `0` `Classical.choice`, `0` `sorryAx`, `0` `ofReduceBool`, and `0` `._unsafe_rec` constants, compile an `.olean` with `-R support -o /tmp/CleanupBoxDerefsMutRestrictionAndCallGuardsSoundness.olean`, import the module in a scratch `.lean` file running `#print axioms` on the 18 theorems listed in **Findings §7**, and iterate `env.constants.map₁` checking `ci.isUnsafe == false`, `ci.isPartial == false`, `ci.isAxiom == false`, and `"_unsafe_rec"` absent from every module constant name.

### 4. Revalidate Anneal TCB Seam Alignment

When `joshlf/anneal` advances past `c131b320eeeb26ef692e5afd5ec8db49ee518613`, inspect `trusted/lean/Trusted/MirAst.lean` (`Rvalue`, `StatementKind`, `TerminatorKind`) and `trusted/lean/Trusted/MirSemantics.lean`: if `Rvalue::Cast` (`PtrToPtr`, `Transmute`, or `BoxDerefTransmute`) is promoted out of `.unsupported`, verify that `BoxDerefTransmute` enforces full `Box<T>` non-null, liveness, and alignment validity preconditions (not bare raw-pointer transmutation) and that `CoverageKind::VirtualCounter` remains accounted for if instrumented MIR is ever captured.
