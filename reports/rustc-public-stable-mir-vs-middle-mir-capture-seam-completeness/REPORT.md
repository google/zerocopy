# `rustc_public` (StableMIR) vs. `rustc_middle::mir` Capture-Seam Completeness, UB-Preserving MIR Extraction, and Fail-Closed Verification Soundness

## Summary

`rustc_public` (formerly StableMIR) and its internal bridge `rustc_public_bridge` are structurally unsuitable as an unmodified capture seam for a UB-checking, fail-closed Rust verifier across all three audited `rust-lang/rust` revisions (`f8a08b688cbe` from 2026-05-30, `49d734536222` from 2026-09-11, and `342d74463af7` from 2026-11-22). Direct primary-source inspection, live `rustc 1.98.0-nightly` (`14210df0e27c`) MIR-dump execution across six flag configurations, and a kernel-checked Lean `v4.34.1` formalization (`support/StableMirCaptureSeamSoundness.lean`, axioms `[propext]` only, `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`) establish five independent soundness and completeness barriers:

1. **Post-optimization MIR extraction erases Rust UB before the verifier sees the body:** Both `BodyBuilder::build` (`compiler/rustc_public_bridge/src/builder.rs:31`) and `CompilerCtxt::mir_body` (`compiler/rustc_public_bridge/src/context/impls.rs:149` at `49d734536222`; `:143` at `342d74463af7`) unconditionally query `tcx.instance_mir(...)`, which dispatches non-const functions to `tcx.optimized_mir(def)` (`compiler/rustc_middle/src/ty/mod.rs:1854`) — i.e., `MirPhase::Runtime(RuntimePhase::Optimized)` rather than `MirPhase::Runtime(RuntimePhase::PostCleanup)` (`tcx.mir_drops_elaborated_and_const_checked`). Because `OptLevel::No.mir_opt_level()` defaults to `1` (`compiler/rustc_session/src/config.rs:118-123`), **even unoptimized `-C opt-level=0` builds** execute `RemoveStorageMarkers` and `RemoveZsts` inside `run_optimization_passes` (`compiler/rustc_mir_transform/src/lib.rs:716,718`). At `-C opt-level=2`, `GVN` (`lib.rs:743`, `gvn.rs:1508-1518`) folds `0 / x` to `const 0_u32` (erasing unchecked division-by-zero UB) and `UnreachablePropagation` (`lib.rs:723`, `unreachable_prop.rs:55-57`) clears statements and rewrites branches to `assume(...)`. Crucially, a subtle pipeline subtlety also affects `PostCleanup` itself: `RemovePlaceMention` runs inside `run_runtime_cleanup_passes` (`lib.rs:673`) *before* `MirPhase::Runtime(RuntimePhase::PostCleanup)` is stamped (`lib.rs:677`), gated solely on `!ctx.opts.unstable_opts.mir_preserve_ub` (`remove_place_mention.rs:13`). Consequently, a UB-preserving capture seam must hook `Runtime(PostCleanup)` **and** enable `-Zmir-preserve-ub`; passing `-Zmir-preserve-ub` alone to `rustc_public` does not disable `RemoveZsts`, `RemoveStorageMarkers`, `GVN`, or `UnreachablePropagation`.
2. **Fail-open constant-evaluation error swallowing and premature driver exit:** `BodyBuilder::visit_const_operand` (`builder.rs:55-71`) matches `Err(mir::interpret::ErrorHandled::Reported(..)) => return`, silently discarding the error, leaving `mir::Const::Unevaluated` intact, and returning `Some(body)` instead of failing closed. Its sibling arm `Err(ErrorHandled::TooGeneric(..))` panics via `unreachable!(...)` (`builder.rs:65`). Meanwhile, `rustc_public::run!` (`compiler/rustc_public/src/rustc_internal/mod.rs:231-249`) invokes user callbacks inside `after_analysis` and stops compilation (`Compilation::Stop`) on `ControlFlow::Break`, bypassing post-analysis post-monomorphization error (PME) and layout-overflow checks unless the caller forces `Compilation::Continue`.
3. **Silent erasure of semantically load-bearing MIR fields:** `rustc_public::mir::BasicBlock` retains only `{ statements, terminator }`, silently dropping `BasicBlockData::is_cleanup` (`compiler/rustc_middle/src/mir/mod.rs:1341`, required to distinguish normal unwind propagation from double-panic abort and explicitly consumed by `Trusted.MirAst.BasicBlock.cleanup` in `joshlf/anneal@c131b320eeeb`). Both `UnwindAction::Terminate(_)` (`mir.rs:507`) and `TerminatorKind::UnwindTerminate(_)` (`mir.rs:749`) drop `UnwindTerminateReason` (`Abi` vs. `InCleanup`). `rustc_public::mir::Body` retains `7` of `19` `rustc_middle::mir::Body` fields (`3` `pub`, `4` `pub(crate)`; `6` of `19` at `f8a08b688cbe`), dropping `12` fields including soundness-critical `required_consts` (`mod.rs:269-271`), `tainted_by_errors`, `phase`, `pass_count`, `source`, and `coroutine`. `TerminatorKind::InlineAsm` drops `asm_macro`, stringifies `template`/`options`/`line_spans` via `format!("{...?}")`, collapses all `7` `InlineAsmOperand` variants into `{ in_value, out_place, raw_rpr: String }`, and silently truncates `asm_goto` targets to `targets.first()` (`mir.rs:798`).
4. **Panic/ICE traps and `Opaque(String)` loss across conversion tables:** Across the `7` core conversion and bridge files, `49d734536222` contains **`11` `unimplemented!()`, `0` `todo!()`, `5` `bug!()`, `7` `unreachable!()`, `1` `panic!()`, and `11` `opaque(...)` lines (`12` call occurrences)**. Six months of upstream evolution from `f8a08b688cbe` to `342d74463af7` stabilized `abi.rs` (eliminating `5` `opaque` lines / `6` calls) and replaced the `ty.rs` `panic!`, yet **increased** total panic/ICE trap lines in `ty.rs` (`8 -> 9` `unimplemented!`, `5 -> 6` `unreachable!`, adding `ty::View => unimplemented!()` and `ClauseKind::CompressedTrait => unreachable!()`) while leaving every `mir.rs` trap (`3` `unimplemented!`, `4` `bug!`, `1` `unreachable!`, `5` `opaque`) and `builder.rs` (`1` `unreachable!` + `ErrorHandled::Reported => return`) unchanged.
5. **Direct contrast with `joshlf/anneal` (`trusted/rustc-capture`):** At `c131b320eeeb`, Anneal has `uses_rustc_public = false`, links directly against `rustc_driver`, `rustc_interface`, `rustc_middle`, and `rustc_session`, authenticates its pinned compiler string (`1.98.0-nightly (f8a08b688 2026-05-30)`), enforces `Compilation::Continue` + `tcx.dcx().has_errors().is_none()` before emitting callback success evidence, and models explicit fail-closed `.unsupported` variants plus `BasicBlock.cleanup` in `Trusted.MirAst`.

| Metric across 7 core bridge/stable files | `rust-lang/rust` `f8a08b688cbe` (2026-05-30) | `rust-lang/rust` `49d734536222` (2026-09-11) | `rust-lang/rust` `342d74463af7` (2026-11-22) | `joshlf/anneal` `c131b320eeeb` (`trusted/rustc-capture`) |
| :--- | ---: | ---: | ---: | :--- |
| Extraction query & target phase | `instance_mir` -> `Runtime(Optimized)` | `instance_mir` -> `Runtime(Optimized)` | `instance_mir` -> `Runtime(Optimized)` | Direct `rustc_middle` (targets `Runtime(PostCleanup)`) |
| `ErrorHandled::Reported` handling | Swallowed (`return`) | Swallowed (`return`) | Swallowed (`return`) | Fail-closed (`has_errors().is_none()` + `Continue`) |
| `unimplemented!()` / `todo!()` lines | `4` / `8` (`12` combined) | `11` / `0` | `12` / `0` | `0` (direct `rustc_middle` + `.unsupported` AST) |
| `bug!()` lines | `4` | `5` | `5` | `0` |
| `unreachable!()` lines | `7` | `7` | `8` | `0` |
| Explicit `panic!()` lines | `0` | `1` | `0` | `0` |
| `opaque(...)` lines (call occurrences) | `11` (`12`) | `11` (`12`) | `6` (`6`) | `0` |
| Dropped `rustc_middle::mir::Body` fields | `13` of `19` | `12` of `19` | `12` of `19` | N/A (direct `rustc_middle` access) |
| Preserves `BasicBlockData::is_cleanup` | No | No | No | Required (`Trusted.MirAst.BasicBlock.cleanup`) |
| Preserves `UnwindTerminateReason` | No | No | No | Direct `rustc_middle::mir::UnwindTerminateReason` |

**Model–system relation for the Lean mechanization:** `support/StableMirCaptureSeamSoundness.lean` proves its soundness, non-injectivity, phase-separation, and counterexample theorems for a standalone operational MIR capture model (`MiddleMir`, `TargetMir`, `CaptureBridge`) checked by the Lean `v4.34.1` kernel (`[propext]` only); it does not import `rustc` or `joshlf/anneal`'s `Trusted.MirSemantics`. The bridge from the formal theorems to real `rustc` behavior is `derived` from the primary-source citations and live `rustc` MIR dumps documented under **Findings** and **Evidence**.

## Applicability

### Subject Roles and Relationships

This report synthesizes evidence across six independently resolvable upstream subjects recorded in `REPORT.json`:

1. **`rust-lang/rust` @ `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`, 2026-05-30):** Source tree pinned by `joshlf/anneal`'s `trusted/rustc-capture/src/driver.rs:25`. Audited statically to establish the exact `rustc_public` state at Anneal's pinned toolchain.
2. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, 2026-05-31, `x86_64-unknown-linux-gnu`, LLVM `22.1.6`):** Installed nightly compiler executed live via `-Zdump-mir=all` on `support/mir_phase_ub_probes.rs` across six flag matrices to directly observe `Runtime(PostCleanup)` vs. `Runtime(Optimized)` MIR mutations. (Separated from `f8a08b688cbe` by one day.)
3. **`rust-lang/rust` @ `49d734536222bf28bb6d07d885b3a81d145981da` (2026-09-11):** Primary baseline revision for the line-by-line `rustc_public` / `rustc_public_bridge` / `rustc_middle` / `rustc_mir_transform` audit (`11` `unimplemented!`, `5` `bug!`, `7` `unreachable!`, `11` `opaque` lines).
4. **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (2026-11-22):** Current `main` tip cross-checked programmatically against both earlier commits to separate persistent architectural properties from transient defects.
5. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (2026-11-19):** Examined at `trusted/rustc-capture/` (compiler-session scaffold), `docs/architecture.md` (documented capture architecture), and `trusted/lean/Trusted/MirAst.lean` (target `Runtime(PostCleanup)` AST contract).
6. **`leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, 2026-09-24):** Kernel checker that verified `support/StableMirCaptureSeamSoundness.lean` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Shared Behavior vs. Cross-Version Drift (`f8a08b688cbe` -> `49d734536222` -> `342d74463af7`)

- **Shared across all three `rust-lang/rust` revisions (May–November 2026):**
  - `BodyBuilder::build` and `CompilerCtxt::mir_body` call `tcx.instance_mir(...)` -> `tcx.optimized_mir(...)` (`Runtime(Optimized)`).
  - `BodyBuilder::visit_const_operand` swallows `Err(ErrorHandled::Reported(..))` with an early `return` and panics on `Err(ErrorHandled::TooGeneric(..))` via `unreachable!`.
  - `OptLevel::No.mir_opt_level()` returns `1`, activating `RemoveZsts` and `RemoveStorageMarkers` even at `-C opt-level=0`.
  - `RemovePlaceMention` runs inside `run_runtime_cleanup_passes` before `Runtime(PostCleanup)` unless `-Zmir-preserve-ub` is set; `-Zmir-preserve-ub` does **not** disable `RemoveZsts`, `RemoveStorageMarkers`, `UnreachablePropagation`, or `GVN`.
  - `rustc_public::mir::BasicBlock` omits `is_cleanup`; `UnwindAction::Terminate` and `TerminatorKind::Abort` omit `UnwindTerminateReason`; `TerminatorKind::InlineAsm` omits `asm_macro`, stringifies `template`/`options`/`line_spans`, collapses `InlineAsmOperand`, and drops `targets[1..]`; `GlobalAlloc::VTable` keeps only `dyn_ty.principal()`; `TerminatorKind::Drop` drops `replace` and `drop`; `Body` omits `phase`, `pass_count`, `source`, `coroutine`, `required_consts`, `tainted_by_errors`, `mentioned_items`, `is_polymorphic`, `injection_phase`, `user_type_annotations`, and coverage metadata.
  - All `3` `unimplemented!()` (`todo!()` at `f8a08b688cbe`), `3` `*WithOverflow` `bug!()`, `1` `Yield|CoroutineDrop|FalseEdge|FalseUnwind => unreachable!()`, and `5` `opaque(...)` sites in `convert/stable/mir.rs` persist unchanged.
- **Changed across the three revisions:**
  - `f8a08b688cbe` -> `49d734536222`: `8` `todo!()` macros in `mir.rs`/`ty.rs` were converted to `unimplemented!()`; `ProjectionElem::PhantomDeref => bug!(...)` was added to `mir.rs:447`; `Body.source_scopes` (`SourceScopeInfo`) was added to `rustc_public::mir::Body` (reducing dropped `Body` fields from `13` to `12`); `TerminatorKind::Drop`'s `async_fut` field was removed upstream; a `panic!("non-defid alias consts...")` appeared temporarily at `ty.rs:561`.
  - `49d734536222` -> `342d74463af7`: `convert/stable/abi.rs` stabilized `PassMode` attributes and cast targets (`455 -> 577` lines), eliminating all `5` `opaque(...)` lines (`6` calls) in `abi.rs`; `ty.rs:561` replaced its `panic!` with an exhaustive match over `ty::AliasConstKind`; `ty.rs` gained two new trap sites (`ty::View(..) => unimplemented!()` at `:513` and `ClauseKind::CompressedTrait(_) => unreachable!()` at `:804`); `mir.rs:736` changed `Goto { target }` to `Goto { target, .. }` to ignore newly added `loop_hint_attrs`.

### Companion Corpus Relationship

The companion corpus report `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity` establishes general denotational capture-transfer characterizations (`OverApproxOnOk`, `ErasingSetPrecondition`, `FaithfulOnOk`, and flag-contract theorems) for abstract capture maps. This report supplies the concrete `rust-lang/rust` primary-source audit, longitudinal trap/field census, live `rustc` MIR-dump measurements, Anneal `trusted/rustc-capture` contrast, and an operational `MiddleMir`/`TargetMir` Lean mechanization targeting `rustc_public`'s exact defects (`RemoveZsts`, `GVN` `0/x`, `RemovePlaceMention`, `is_cleanup`, `UnwindTerminateReason`, and `ErrorHandled::Reported`).

## Findings

### 1. Extraction-Point and Error-Handling Mismatch in `rustc_public_bridge`

Basis: source (`rust-lang/rust` `f8a08b688cbe`, `49d734536222`, `342d74463af7`).

#### 1.1 Unconditional Extraction of `Runtime(Optimized)` MIR via `TyCtxt::instance_mir`

Every public MIR-body entry point in `rustc_public` routes through `TyCtxt::instance_mir`:

- **Monomorphized instances (`Instance::body`):** `CompilerCtxt::instance_body` (`compiler/rustc_public_bridge/src/context/impls.rs:620-622` at `49d734536222`) invokes `BodyBuilder::new(self.tcx, instance).build()`, whose first statement (`compiler/rustc_public_bridge/src/builder.rs:30-31`, identical across all three audited revisions) is:

```rust
// compiler/rustc_public_bridge/src/builder.rs:30-51 (49d734536222 and 342d74463af7)
pub(crate) fn build(mut self) -> mir::Body<'tcx> {
    let body = self.tcx.instance_mir(self.instance.def).clone();
    let mono_body = if !self.instance.args.is_empty()
        || self.tcx.def_kind(self.instance.def_id()) != DefKind::AnonConst
    {
        let mut mono_body = self.instance.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(self.tcx, body),
        );
        self.visit_body(&mut mono_body);
        mono_body
    } else {
        // Already monomorphic.
        body
    };

    mono_body
}
```

- **Generic/unmonomorphized items (`CrateItem::body` / `CrateItem::expect_body`):** `CompilerCtxt::mir_body` (`compiler/rustc_public_bridge/src/context/impls.rs:148-150` at `49d734536222`; `:142-144` at `342d74463af7`) likewise calls `self.tcx.instance_mir(InstanceKind::Item(item))`:

```rust
// compiler/rustc_public_bridge/src/context/impls.rs:148-150 (49d734536222)
pub fn mir_body(&self, item: DefId) -> &'tcx Body<'tcx> {
    self.tcx.instance_mir(InstanceKind::Item(item))
}
```

- **Query dispatch inside `rustc_middle`:** `TyCtxt::instance_mir` (`compiler/rustc_middle/src/ty/mod.rs:1832-1871` at `49d734536222`) routes every regular function and `const fn` (anything other than `Const`, `Static`, `AssocConst`, `Ctor`, `AnonConst`, or `Constness::Const { always: true }`) directly to `self.optimized_mir(def)` (`:1854`), and shims to `self.mir_shims(shim)` (`:1861`).
- **`optimized_mir` pipeline (`compiler/rustc_mir_transform/src/lib.rs:776-822` at `49d734536222`; `:792-838` at `342d74463af7`):** `inner_optimized_mir` steals `tcx.mir_drops_elaborated_and_const_checked(did)` (`Runtime(PostCleanup)`), calls `remap_mir_for_const_eval_select(tcx, body, hir::Constness::NotConst)` (`:799`), runs `MentionedItems` (`:808`), and executes `run_optimization_passes(tcx, &mut body)` (`:819`), stamping `MirPhase::Runtime(RuntimePhase::Optimized)` (`:771`).

`rustc_public` exposes **no public query** for `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`). Reaching `Runtime(PostCleanup)` requires escaping the public API via `#[cfg(feature = "rustc_internal")]` and linking `rustc_private`.

#### 1.2 Exact Placement and Activation Thresholds of UB-Erasing Passes

Inspecting `compiler/rustc_mir_transform/src/lib.rs` and the individual pass implementations exposes two distinct hazard zones — one **before** `Runtime(PostCleanup)` is stamped and one **between** `Runtime(PostCleanup)` and `Runtime(Optimized)`:

| Pass | Pipeline Function (`rustc_mir_transform/src/lib.rs`, `49d734536222` / `342d74463af7`) | Activation Policy (Source) | Active at `-O0`? | Active at `-O2`? | Disabled by `-Zmir-preserve-ub`? | Semantic / UB-Erasure Effect |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `RemovePlaceMention` | `run_runtime_cleanup_passes` (`L673` / `L687`, **pre-`PostCleanup`**) | `PassPolicy::optional(!ctx.opts.unstable_opts.mir_preserve_ub)` (`remove_place_mention.rs:13`) | **Yes** (default) | **Yes** (default) | **Yes** | Deletes `StatementKind::PlaceMention(..)` (e.g., `let _ = *p;`), erasing place-validity UB checks even before `PostCleanup`. |
| `CheckAlignment`, `CheckNull`, `CheckEnums` | `run_optimization_passes` (`L697-699` / `L711-713`) | Enabled when `tcx.sess.ub_checks()` is true (default at `-O0`) | **Yes** (even at `-Zmir-opt-level=0`) | No (default `-O2`) | No | Mutates CFG by inserting synthetic assert blocks and locals; `CheckNull` guards `SIZE != 0 && ptr == 0`, so null ZST derefs pass the check before `RemoveZsts` deletes them. |
| `ForceInline` | `run_optimization_passes` (`L709` / `L723`) | Always enabled for `#[rustc_force_inline]` callees | Yes (on annotated callees) | Yes | No | Alters CFG and call boundaries regardless of `-Zmir-opt-level=0`. |
| `RemoveStorageMarkers` | `run_optimization_passes` (`L716` / `L730`) | `PassPolicy::optional(ctx.mir_opt_level() >= 1 && !ctx.emit_lifetime_markers())` (`remove_storage_markers.rs:13`) | **Yes** (`mir_opt_level = 1`, `emit_lifetime_markers = false`) | No (`emit_lifetime_markers = true` at `-O2`) | No | Deletes all `StorageLive`/`StorageDead` statements, erasing dead-local access and double-`StorageLive` UB. |
| `RemoveZsts` | `run_optimization_passes` (`L718` / `L732`) | `PassPolicy::optional(ctx.mir_opt_level() >= 1)` (`remove_zsts.rs:13`) | **Yes** (`mir_opt_level = 1`) | **Yes** (`mir_opt_level = 2`) | No | Replaces ZST operands with `ConstValue::ZeroSized` (`remove_zsts.rs:114`) and turns ZST `Assign`/`PlaceMention`/`SetDiscriminant`/`Storage*` into `Nop` (`:137-141`), erasing `*p` read/write UB on dangling/null ZST pointers. |
| `UnreachablePropagation` | `run_optimization_passes` (`L723` / `L737`) | `PassPolicy::optional(ctx.mir_opt_level() >= 2)` (`unreachable_prop.rs:20`) | No (`mir_opt_level = 1`) | **Yes** (`mir_opt_level = 2`) | No | Clears statements in unreachable blocks (`unreachable_prop.rs:55-57`), propagates `Unreachable` to predecessors, and rewrites `SwitchInt` targets to `NonDivergingIntrinsic::Assume` (`:101-120`), deleting pre-`unreachable` dereferences and `PlaceMention`s. |
| `GVN` | `run_optimization_passes` (`L743` / `L757`) | `PassPolicy::optional(ctx.mir_opt_level() >= 2)` (`gvn.rs:132`) | No (`mir_opt_level = 1`) | **Yes** (`mir_opt_level = 2`) | No | Absorbing-element table (`gvn.rs:1508-1518`) folds `(BinOp::Div \| BinOp::Rem \| BinOp::Shl \| BinOp::Shr, Left(0), _)` to `Scalar::from_uint(0, size)`, silently erasing division/remainder-by-zero and shift-overflow UB. |

Two non-obvious primary-source facts control capture design:
1. **`-C opt-level=0` does NOT turn off MIR optimizations:** `OptLevel::mir_opt_level` (`compiler/rustc_session/src/config.rs:118-123`) returns `1` for `OptLevel::No` and `2` for all other levels. Thus, default debug builds still run `RemoveZsts` and `RemoveStorageMarkers` inside `optimized_mir`.
2. **`-Zmir-preserve-ub` is necessary for `Runtime(PostCleanup)` but insufficient for `Runtime(Optimized)`:** Across the audited transform files, `mir_preserve_ub` gates `RemovePlaceMention` (`remove_place_mention.rs:13`), which runs in `run_runtime_cleanup_passes` *prior* to stamping `Runtime(PostCleanup)`. Passing `-Zmir-preserve-ub` without hooking `Runtime(PostCleanup)` still allows `RemoveZsts`, `RemoveStorageMarkers`, `UnreachablePropagation`, and `GVN` to erase UB.

#### 1.3 Fail-Open Constant-Evaluation Error Swallowing and Premature Callback Exit

In `compiler/rustc_public_bridge/src/builder.rs:54-71` (identical across `f8a08b688cbe`, `49d734536222`, and `342d74463af7`):

```rust
// compiler/rustc_public_bridge/src/builder.rs:54-71
impl<'tcx> MutVisitor<'tcx> for BodyBuilder<'tcx> {
    fn visit_const_operand(
        &mut self,
        constant: &mut mir::ConstOperand<'tcx>,
        location: mir::Location,
    ) {
        let const_ = constant.const_;
        let val = match const_.eval(self.tcx, ty::TypingEnv::fully_monomorphized(), constant.span) {
            Ok(v) => v,
            Err(mir::interpret::ErrorHandled::Reported(..)) => return,
            Err(mir::interpret::ErrorHandled::TooGeneric(..)) => {
                unreachable!("Failed to evaluate instance constant: {:?}", const_)
            }
        };
        let ty = constant.ty();
        constant.const_ = mir::Const::Val(val, ty);
        self.super_const_operand(constant, location);
    }
```

Four separate capture-seam failures converge here:

1. **Swallowed `ErrorHandled::Reported` (`builder.rs:63`):** When a monomorphized constant fails evaluation (e.g., a post-monomorphization `const { panic!(...) }` or invalid layout assertion), `visit_const_operand` returns early without mutating `constant.const_`, without marking the `Body` failed, and without returning `Result::Err`. `Instance::body` returns `Some(body)` containing a raw `ConstantKind::Unevaluated(...)` (`mir.rs:894-902`) for an invalid constant whose evaluation already errored.
2. **Unhandled ICE on `ErrorHandled::TooGeneric` (`builder.rs:64-66`):** If a residual generic parameter escapes monomorphization, `BodyBuilder` aborts the process via `unreachable!(...)` instead of returning a typed `CaptureError`.
3. **Skipped evaluation on non-generic `AnonConst` (`builder.rs:32-48`):** When `self.instance.args.is_empty()` and `def_kind == DefKind::AnonConst`, `BodyBuilder::build` executes the `else` branch and returns `body` without calling `self.visit_body(&mut mono_body)`.
4. **Driver callback timing (`compiler/rustc_public/src/rustc_internal/mod.rs:231-249`):** `RustcPublic::after_analysis` executes the tool callback before codegen/monomorphization error checks. If the callback inspects `Instance::body()`, receives the swallowed broken constant, emits a verification certificate, and returns `ControlFlow::Break(...)`, `after_analysis` returns `Compilation::Stop` (`:244`) — preventing `rustc` from completing post-analysis PME and layout validation.

---

### 2. Live `rustc` Empirical MIR phase-separation probes (`rustc 1.98.0-nightly 14210df0e27c`)

Basis: execution (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `x86_64-unknown-linux-gnu`, LLVM `22.1.6`, via `support/audit_rustc_public_vs_middle_mir.py` on `support/mir_phase_ub_probes.rs`, full JSON receipts in `support/audit_results.json`).

Compiling the eight probe functions in `support/mir_phase_ub_probes.rs` with `-Zdump-mir=all` across six flag configurations and comparing `3-2-000.runtime-post-cleanup.after.mir` (`Runtime(PostCleanup)`) against `3-3-000.runtime-optimized.after.mir` (`Runtime(Optimized)`) directly reproduces every UB-erasure mechanism observed in source:

| Probe Function | `o0_default` (`-O0`) | `o2_default` (`-O2`) | `o0_preserve_ub` (`-O0 -Zmir-preserve-ub`) | `o2_preserve_ub` (`-O2 -Zmir-preserve-ub`) | `o0_mopt0_preserve_ub` (`-O0 -Zmir-opt-level=0 -Zmir-preserve-ub`) | `o2_mopt0_preserve_ub` (`-O2 -Zmir-opt-level=0 -Zmir-preserve-ub`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `probe_zst_deref` | **Mutated**: `*p` read/write **erased**; `1 -> 5` BBs (+4 UB asserts that skip `SIZE==0`); `Storage` `1/1 -> 0/0` | **Mutated**: `*p` read/write **erased** completely (`bb0: { return; }`); `Storage` `1/1 -> 0/0` | **Mutated**: `*p` read/write **erased** (`-Zmir-preserve-ub` does NOT stop `RemoveZsts`) | **Mutated**: `*p` read/write **erased** completely (`bb0: { return; }`) | **Mutated**: `*p` retained, but `1 -> 5` BBs (+4 `CheckAlignment`/`CheckNull` asserts) | Body-identical (`*p` read/write & `Storage` preserved) |
| `probe_div_zero_unchecked` | **Mutated**: `Div` retained, `Storage` `1/1 -> 0/0` | **Mutated**: `Div(0, x)` **erased** by `GVN` -> `_0 = const 0_u32; return;` | **Mutated**: `Storage` `1/1 -> 0/0` | **Mutated**: `Div(0, x)` **erased** (`-Zmir-preserve-ub` does NOT stop `GVN`) | Body-identical | Body-identical |
| `probe_div_zero_checked` | **Mutated**: `Storage` `1/1 -> 0/0` | **Mutated**: `Div(0, x)` folded to `const 0_u32` (guarded by `Assert`) | **Mutated**: `Storage` `1/1 -> 0/0` | **Mutated**: `Div(0, x)` folded to `const 0_u32` | Body-identical | Body-identical |
| `probe_place_mention` | `PlaceMention` **already erased pre-`PostCleanup`** (`_0 = ()` also folded in `Opt`) | `PlaceMention` **already erased pre-`PostCleanup`** | `PlaceMention((*_1))` **retained** in both (`_0 = ()` folded in `Opt`) | `PlaceMention((*_1))` **retained** in both (`_0 = ()` folded in `Opt`) | Body-identical (`PlaceMention` retained) | Body-identical (`PlaceMention` retained) |
| `probe_storage_markers` | **Mutated**: `StorageLive`/`Dead` `8/8 -> 0/0` (`RemoveStorageMarkers`) | **Mutated**: `4 -> 1` BBs, `Storage` `8/8 -> 3/3` (inlining/simplification) | **Mutated**: `Storage` `8/8 -> 0/0` | **Mutated**: `4 -> 1` BBs, `Storage` `8/8 -> 3/3` | Body-identical (`8/8`) | Body-identical (`8/8`) |
| `probe_unreachable_prop` | **Mutated**: `4 -> 6` BBs (+2 UB asserts), `Storage` `5/3 -> 0/0` | **Mutated**: `4 -> 1` BBs; `copy (*_1)` & `unreachable_unchecked` **erased** -> `assume(flag == false)` | **Mutated**: `4 -> 6` BBs (+2 UB asserts), `Storage` `5/3 -> 0/0` | **Mutated**: `4 -> 1` BBs; `copy (*_1)`, `PlaceMention`, & `unreachable_unchecked` **erased** -> `assume` | **Mutated**: `4 -> 6` BBs (+2 UB asserts) | Body-identical |
| `probe_unwind_cleanup` | **Mutated**: `Storage` `6/5 -> 0/0`; preserves `2` cleanup BBs + `terminate(cleanup)` in `rustc_middle` | **Mutated**: `7 -> 6` BBs, `Storage` `6/5 -> 11/10`; `2` cleanup BBs + `terminate(cleanup)` | **Mutated**: `Storage` `6/5 -> 0/0` | **Mutated**: `7 -> 6` BBs, `Storage` `6/5 -> 11/10` | Body-identical (`2` cleanup BBs, `terminate(cleanup)`) | Body-identical |
| `probe_unwind_abi_terminate` | **Mutated**: `Storage` `5/4 -> 0/0`; `terminate(abi)` present in `rustc_middle` | **Mutated**: `4 -> 3` BBs, `Storage` `5/4 -> 10/9`; `terminate(abi)` present | **Mutated**: `Storage` `5/4 -> 0/0` | **Mutated**: `4 -> 3` BBs, `Storage` `5/4 -> 10/9` | Body-identical (`terminate(abi)`) | Body-identical |

#### Concrete Verbatim MIR Excerpts Observed Live

1. **`probe_div_zero_unchecked` (`-C opt-level=2`, `GVN` UB erasure):**
   - `Runtime(PostCleanup)`:
     ```text
     bb0: {
         StorageLive(_2);
         _2 = copy _1;
         _0 = Div(const 0_u32, move _2);
         StorageDead(_2);
         return;
     }
     ```
   - `Runtime(Optimized)` (what `rustc_public` captures):
     ```text
     bb0: {
         _0 = const 0_u32;
         return;
     }
     ```
2. **`probe_zst_deref` (`-C opt-level=2`, `RemoveZsts` UB erasure):**
   - `Runtime(PostCleanup)`: `bb0` executes `_2 = copy (*_1); (*_1) = ();`.
   - `Runtime(Optimized)`: `bb0` reduces to a lone `return;` with zero pointer dereferences. Even at `-C opt-level=0`, `RemoveZsts` deletes both `*p` operations after `CheckNull` emits `_14 = Ne(const <() as SizedTypeProperties>::SIZE, const 0_usize); _15 = Eq(copy _13, const 0_usize); _16 = BitAnd(copy _15, copy _14);` — a runtime guard that evaluates to `false` for null `*mut ()` because `SIZE == 0`, so **neither** the inserted check **nor** the erased dereference rejects `probe_zst_deref(core::ptr::null_mut())`.
3. **`probe_place_mention` (`-C opt-level=0` vs. `-C opt-level=0 -Zmir-preserve-ub`):**
   - Without `-Zmir-preserve-ub`, `Runtime(PostCleanup)` already contains only `_0 = const (); return;` because `RemovePlaceMention` executed inside `run_runtime_cleanup_passes`.
   - With `-Zmir-preserve-ub`, `Runtime(PostCleanup)` retains `PlaceMention((*_1)); _0 = const (); return;`.
4. **`probe_unreachable_prop` (`-C opt-level=2`, `UnreachablePropagation`):**
   - `Runtime(PostCleanup)` has `4` blocks (`bb0` switches on `flag`; `bb1` dereferences `*_1`; `bb2` calls `unreachable_unchecked()`; `bb3` returns `42`).
   - `Runtime(Optimized)` collapses all `4` blocks into one: `_4 = Eq(copy _2, const false); assume(move _4); _0 = const 42_u32; return;`, erasing the dereference `copy (*_1)` and even deleting `PlaceMention` under `-C opt-level=2 -Zmir-preserve-ub`.
5. **`probe_unwind_cleanup` vs. `probe_unwind_abi_terminate` (`is_cleanup` and `UnwindTerminateReason`):**
   - `probe_unwind_cleanup` emits `bb5 (cleanup): { drop(_2) -> [return: bb6, unwind terminate(cleanup)]; }` and `bb6 (cleanup): { resume; }` (`is_cleanup = true`, `UnwindTerminateReason::InCleanup`).
   - `probe_unwind_abi_terminate` emits `_7 = panic_fmt(move _8) -> unwind terminate(abi);` (`UnwindTerminateReason::Abi`).
   - Under `rustc_public`, `bb5` and `bb6` lose `is_cleanup`, and both `unwind terminate(cleanup)` and `unwind terminate(abi)` collapse to the payload-less `UnwindAction::Terminate`.

---

### 3. Complete Catalog of Silent Field Erasures, AST Normalizations, and Terminator Lowering

Basis: source (`rust-lang/rust` `f8a08b688cbe`, `49d734536222`, `342d74463af7`, parsed programmatically in `support/audit_results.json`).

#### 3.1 `Body`, `BasicBlockData`, `LocalDecl`, `SourceScopeData`, and `InlineAsmOperand` Field Diffs

Inspecting the actual struct definitions (including `pub(crate)` fields exposed via methods on `rustc_public::mir::Body`, rather than only `pub` fields) yields exact counts:

- **`rustc_middle::mir::Body` (`19` fields, `compiler/rustc_middle/src/mir/mod.rs:206-330`) vs. `rustc_public::mir::Body` (`7` fields at `49d734536222` & `342d74463af7`, `compiler/rustc_public/src/mir/body.rs:15-45`; `6` fields at `f8a08b688cbe`):**
  - Preserved (`7` fields): `pub blocks` (`basic_blocks`), `pub(crate) locals` (`local_decls`, accessor `locals()`), `pub(crate) arg_count` (accessor `arg_locals()`), `pub var_debug_info`, `pub(crate) spread_arg` (accessor `spread_arg()`), `pub span`, and `pub(crate) source_scopes` (added after `f8a08b688cbe`, used only by `Body::caller_location()`).
  - **Dropped (`12` fields at `49d734536222` & `342d74463af7`; `13` at `f8a08b688cbe`):**

| Dropped `rustc_middle::mir::Body` Field | Source Line (`49d734536222` / `342d74463af7`) | Impact on UB-Checking / Fail-Closed Verification |
| :--- | :--- | :--- |
| `phase: MirPhase` | `L216` / `L215` | **High (soundness-critical):** Verifier cannot verify or assert that the captured MIR is `Runtime(PostCleanup)` rather than `Runtime(Optimized)`. |
| `tainted_by_errors: Option<ErrorGuaranteed>` | `L311` / `L310` | **High (soundness-critical):** Verifier cannot detect bodies tainted by borrowck, transmute, or well-formedness errors (`lib.rs:563-585`). |
| `required_consts: Option<Vec<ConstOperand>>` | `L271` / `L270` | **High (soundness-critical):** Upstream comment (`mod.rs:269-270`) explicitly states: *"This is soundness-critical, we make a guarantee that all consts syntactically mentioned in a function have successfully evaluated if the function ever gets executed at runtime."* |
| `coroutine: Option<Box<CoroutineInfo>>` | `L233` / `L232` | **High (for async/coroutines):** Drops coroutine yield/resume layout metadata, drop shim links, and movability info. |
| `source: MirSource` | `L221` / `L220` | **Medium:** Loses whether the body is a promoted const, generator drop shim, or primary item (`MirSource` instance kind). |
| `is_polymorphic: bool` | `L302` / `L301` | **Medium:** Loses whether body references generic parameters for `ConstEvaluatable` checks. |
| `mentioned_items` | `L285` / `L284` | **Medium:** Needed to check optimization-independent monomorphization reachability for `required_consts`. |
| `user_type_annotations` | `L243` / `L242` | **Low–Medium:** Referenced by `ConstOperand::user_ty` / `AscribeUserType` indices (`usize`), leaving dangling indices on `rustc_public`'s `ConstOperand.user_ty`. |
| `pass_count: usize` | `L219` / `L218` | **Low (diagnostics/audit):** Loses MIR pass execution provenance. |
| `injection_phase: Option<MirPhase>` | `L309` / `L308` | **Low (diagnostics/custom MIR):** Loses custom-MIR injection phase marker. |
| `coverage_early_info` / `coverage_mir_info` (`coverage_info_hi` / `function_coverage_info` at `f8a08b688cbe`) | `L320, L330` / `L319, L329` | **Low (coverage only):** Loses coverage instrumentation metadata. |

- **`BasicBlockData` (`4` fields, `mod.rs:1319-1342`) vs. `rustc_public::mir::BasicBlock` (`2` fields, `body.rs:184-187`):**
  - Preserved: `statements`, `terminator`.
  - **Dropped (`2` fields):** `is_cleanup: bool` (**soundness-critical** unwind-pad marker: `mod.rs:1337-1341` documents *"If true, this block lies on an unwind path... Unwind blocks must only branch to other unwind blocks"*; required by `Trusted.MirAst.BasicBlock.cleanup`), and `after_last_stmt_debuginfos` (debuginfo only).
- **`LocalDecl` (`5` fields, `mod.rs:967-1064`) vs. `rustc_public::mir::LocalDecl` (`3` fields, `body.rs:177-181`):**
  - Drops `local_info`, `user_ty`, and `source_info.scope` (keeping only `ty`, `span`, `mutability`).
- **`SourceScopeData` (`5` fields, `mod.rs:1478-1495`) vs. `SourceScopeInfo` (`2` fields, `body.rs:807-815`, absent at `f8a08b688cbe`):**
  - Drops `span`, `parent_scope`, `local_data`, and collapses `inlined: Option<(ty::Instance, Span)>` to `Option<(bool, Span)>` (`requires_caller_location` only, losing inlined callee identity).
- **`InlineAsmOperand` (`7` enum variants, `syntax.rs:1056-1085`) vs. `rustc_public::mir::InlineAsmOperand` (`3`-field struct, `body.rs:294-300`, `convert/stable/mir.rs:684-709`):**
  - Collapses `In { reg, value }`, `Out { reg, late, place }`, `InOut { reg, late, in_value, out_place }`, `Const { value }`, `SymFn { value }`, `SymStatic { def_id }`, and `Label { target_index }` into `{ in_value: Option<Operand>, out_place: Option<Place>, raw_rpr: format!("{self:?}") }`. Drops register classes, `late` flags, `Const` values, `SymFn`/`SymStatic` symbols, and `Label` target indices completely from the typed AST.
- **Additional field erasures across `convert/stable/mir.rs`:**
  - `UnwindAction::Terminate(_)` (`mir.rs:507`): drops `UnwindTerminateReason` (`Abi` vs. `InCleanup`).
  - `GlobalAlloc::VTable(ty, dyn_ty)` (`mir.rs:862-865`): emits `dyn_ty.principal()`, dropping auto-trait bounds (`// FIXME: Should we record the whole vtable?`).
  - `CastKind::PointerCoercion(c, _)` (`mir.rs:360`): drops `CoercionSource`.
  - `ProjectionElem::Downcast(_, idx)` (`mir.rs:467`): drops `Option<Symbol>` variant name (recoverable via ADT lookup).

#### 3.2 AST Normalizations in `convert/stable/mir.rs`

| `rustc_middle::mir` Construct | `rustc_public` Target (`convert/stable/mir.rs`, `49d734536222`) | Soundness / Audit Consequence |
| :--- | :--- | :--- |
| `Rvalue::BinaryOp(AddWithOverflow \| SubWithOverflow \| MulWithOverflow, ops)` | `Rvalue::CheckedBinaryOp(Add \| Sub \| Mul, ops.0, ops.1)` (`:242-256`) | Splits `Rvalue::BinaryOp` into two variants; calling `BinOp::stable` directly on `*WithOverflow` ICEs via `bug!("AddWithOverflow should have been translated already")` (`:599, 602, 605` — note copy-pasted `"AddWithOverflow"` string on `SubWithOverflow` and `MulWithOverflow`). |
| `StatementKind::BackwardIncompatibleDropHint { .. }` | `StatementKind::Nop` (`:196-198`) | Erases edition-migration drop-order hint statements (semantically a no-op at runtime per upstream comment, but non-invertible). |
| `Rvalue::RawPtr(mutability, place)` | `Rvalue::AddressOf(mutability, place)` (`:233-236`) | Legacy naming renormalization. |
| `CastKind::PointerExposeProvenance` | `CastKind::PointerExposeAddress` (`:358`) | Legacy naming renormalization. |

#### 3.3 Complete 12-Arm `TerminatorKind` Mapping (`impl Stable for mir::TerminatorKind`)

Extracted directly from `compiler/rustc_public/src/unstable/convert/stable/mir.rs` (`L734-805` at `49d734536222`; `L735-806` at `342d74463af7`; `L711-787` at `f8a08b688cbe`):

| # | `rustc_middle::mir::TerminatorKind` Arm | Line (`f8a08` / `49d73` / `342d7`) | `rustc_public` Output / Trap | Silently Dropped or Degraded Fields |
| ---: | :--- | :--- | :--- | :--- |
| 1 | `Goto { target, .. }` | `712` / `735` / `736` | `TerminatorKind::Goto { target }` | `loop_hint_attrs` dropped via `..` at `342d74463af7` (not yet present at `f8a08`/`49d73`). |
| 2 | `SwitchInt { discr, targets }` | `715` / `738` / `739` | `TerminatorKind::SwitchInt { discr, targets }` | None (exact branch + `otherwise` mapping). |
| 3 | `UnwindResume` | `725` / `748` / `749` | `TerminatorKind::Resume` | Valid only in `is_cleanup = true` blocks, which `BasicBlock` drops. |
| 4 | `UnwindTerminate(_)` | `726` / `749` / `750` | `TerminatorKind::Abort` | **`UnwindTerminateReason` (`Abi` vs. `InCleanup`) dropped** via `(_)`. |
| 5 | `Return` | `727` / `750` / `751` | `TerminatorKind::Return` | None (coroutine return semantics still require dropped `Body::coroutine`). |
| 6 | `Unreachable` | `728` / `751` / `752` | `TerminatorKind::Unreachable` | None. |
| 7 | `Drop { place, target, unwind, replace: _, drop: _ }` | `729` / `752` / `753` | `TerminatorKind::Drop { place, target, unwind }` | `replace: bool` (diagnostic-only, `syntax.rs:750-752`), `drop: Option<BasicBlock>` (async drop target), and `async_fut` (at `f8a08b688cbe`) dropped; `unwind` loses `UnwindTerminateReason`. |
| 8 | `Call { func, args, destination, target, unwind, call_source: _, fn_span: _ }` | `741` / `759` / `760` | `TerminatorKind::Call { func, args, destination, target, unwind }` | `call_source: CallSource`, `fn_span: Span`, and per-arg spans (`arg.node`) dropped; `unwind` loses `UnwindTerminateReason`. |
| 9 | `TailCall { func: _, args: _, fn_span: _ }` | `756` / `774` / `775` | **`unimplemented!()`** (`todo!()` at `f8a08`) | **Hard panic/ICE trap** on explicit `become` tail calls. |
| 10 | `Assert { cond, expected, msg, target, unwind }` | `757` / `775` / `776` | `TerminatorKind::Assert { cond, expected, msg, target, unwind }` | `unwind` loses `UnwindTerminateReason`. |
| 11 | `InlineAsm { asm_macro: _, template, operands, options, line_spans, targets, unwind }` | `766` / `784` / `785` | `TerminatorKind::InlineAsm { template: format!(..), operands, options: format!(..), line_spans: format!(..), destination: targets.first(), unwind }` | `asm_macro` dropped; `template`/`options`/`line_spans` Debug-stringified; `operands` lose registers/`late`/`Const`/`SymFn`/`SymStatic`/`Label`; **`targets[1..]` silently dropped** (`// FIXME: Figure out how to do labels in SMIR`); `unwind` loses `UnwindTerminateReason`. |
| 12 | `Yield { .. } \| CoroutineDrop \| FalseEdge { .. } \| FalseUnwind { .. }` | `783` / `801` / `802` | **`unreachable!()`** | **Hard panic/ICE trap** if invoked via `rustc_internal::stable` on pre-`StateTransform` / analysis MIR. |

---

### 4. Exhaustive Trap and `opaque(...)` Census Across Three Pinned `rust-lang/rust` Revisions

Basis: source (`support/audit_rustc_public_vs_middle_mir.py` programmatic scan of all `7` core files in `support/audit_results.json`).

#### 4.1 Definition of `opaque(...)`

In `compiler/rustc_public/src/lib.rs:324-340` (`49d734536222`):

```rust
pub struct Opaque(String);
pub fn opaque<T: Debug>(value: &T) -> Opaque {
    Opaque(format!("{value:?}"))
}
```

Every `opaque(...)` call discards the structured compiler AST/ABI value and replaces it with an unparsed Rust `Debug` string whose formatting is unstable and unsuitable as a formal semantics input.

#### 4.2 Per-File Breakdown (`49d734536222` Baseline vs. `f8a08b688cbe` and `342d74463af7`)

| File | `f8a08b688cbe` (`unimp/todo/bug/unr/panic/opaq`) | `49d734536222` (`unimp/todo/bug/unr/panic/opaq`) | `342d74463af7` (`unimp/todo/bug/unr/panic/opaq`) |
| :--- | :---: | :---: | :---: |
| `compiler/rustc_public/src/unstable/convert/stable/mir.rs` | `0 / 3 / 3 / 1 / 0 / 5` (`923L`) | `3 / 0 / 4 / 1 / 0 / 5` (`941L`) | `3 / 0 / 4 / 1 / 0 / 5` (`942L`) |
| `compiler/rustc_public/src/unstable/convert/stable/ty.rs` | `4 / 5 / 1 / 5 / 0 / 1` (`1189L`) | `8 / 0 / 1 / 5 / 1 / 1` (`1181L`) | `9 / 0 / 1 / 6 / 0 / 1` (`1197L`) |
| `compiler/rustc_public/src/unstable/convert/stable/abi.rs` | `0 / 0 / 0 / 0 / 0 / 5` (`6` calls, `437L`) | `0 / 0 / 0 / 0 / 0 / 5` (`6` calls, `455L`) | `0 / 0 / 0 / 0 / 0 / 0` (`577L`) |
| `compiler/rustc_public/src/unstable/convert/stable/mod.rs` | `0 / 0 / 0 / 0 / 0 / 0` (`127L`) | `0 / 0 / 0 / 0 / 0 / 0` (`127L`) | `0 / 0 / 0 / 0 / 0 / 0` (`127L`) |
| `compiler/rustc_public_bridge/src/builder.rs` | `0 / 0 / 0 / 1 / 0 / 0` (`76L`) | `0 / 0 / 0 / 1 / 0 / 0` (`76L`) | `0 / 0 / 0 / 1 / 0 / 0` (`76L`) |
| `compiler/rustc_public_bridge/src/alloc.rs` | `0 / 0 / 0 / 0 / 0 / 0` (`100L`) | `0 / 0 / 0 / 0 / 0 / 0` (`100L`) | `0 / 0 / 0 / 0 / 0 / 0` (`100L`) |
| `compiler/rustc_public_bridge/src/context/impls.rs` | `0 / 0 / 0 / 0 / 0 / 0` (`782L`) | `0 / 0 / 0 / 0 / 0 / 0` (`823L`) | `0 / 0 / 0 / 0 / 0 / 0` (`796L`) |
| **Total (line-hits; `opaque` occurrences in parens)** | **`4 / 8 / 4 / 7 / 0 / 11 (12)`** | **`11 / 0 / 5 / 7 / 1 / 11 (12)`** | **`12 / 0 / 5 / 8 / 0 / 6 (6)`** |

Note on `abi.rs:166` (`49d734536222`): `PassMode::Pair(opaque(first), opaque(second))` contains **two** `opaque(...)` invocations on a single source line, accounting for the `11` matched lines vs. `12` total `opaque(...)` call occurrences at `f8a08b688cbe` and `49d734536222`. Between `49d734536222` and `342d74463af7`, `abi.rs` stabilized `PassMode` (`ArgAttributes`, `CastTarget`, `IndirectMode`), eliminating all `5` `opaque` lines (`6` calls) in `abi.rs`.

#### 4.3 Complete Site-by-Site Inventory (`49d734536222` with `342d74463af7` Deltas)

- **`unimplemented!()` (`11` sites at `49d734536222`; `12` at `342d74463af7`):**
  1. `mir.rs:266` (`342d7:267`): `Rvalue::WrapUnsafeBinder(..) => unimplemented!("FIXME(unsafe_binders):")`
  2. `mir.rs:469` (`342d7:470`): `ProjectionElem::UnwrapUnsafeBinder(..) => unimplemented!("FIXME(unsafe_binders):")`
  3. `mir.rs:774` (`342d7:775`): `TerminatorKind::TailCall { .. } => unimplemented!()`
  4. `ty.rs:470` (`342d7:471`): `ty::UnsafeBinder(_) => unimplemented!()`
  5. `ty.rs:483` (`342d7:484`): `ty::CoroutineClosure(..) => unimplemented!("FIXME(async_closures): Lower these to SMIR")`
  6. `ty.rs:570` (`342d7:578`): `ty::ConstKind::Bound(_, _) => unimplemented!()`
  7. `ty.rs:571` (`342d7:579`): `ty::ConstKind::Placeholder(_) => unimplemented!()`
  8. `ty.rs:572` (`342d7:580`): `ty::ConstKind::Expr(_) => unimplemented!()`
  9. `ty.rs:754` (`342d7:762`): `PredicateKind::NormalizesTo(_pred) => unimplemented!()`
  10. `ty.rs:796` (`342d7:807`): `ClauseKind::HostEffect(..) => unimplemented!()`
  11. `ty.rs:799` (`342d7:810`): `ClauseKind::UnstableFeature(_) => unimplemented!()`
  12. *(Added by `342d74463af7`)* `ty.rs:513`: `ty::View(..) => unimplemented!()` (`// FIXME(scrabsha)`)
- **`bug!()` (`5` sites at `49d734536222` and `342d74463af7`):**
  1. `mir.rs:447` (`342d7:448`): `ProjectionElem::PhantomDeref => bug!("Hopefully we don't come here")` *(absent at `f8a08b688cbe`)*
  2. `mir.rs:599` (`342d7:600`): `BinOp::AddWithOverflow => bug!("AddWithOverflow should have been translated already")`
  3. `mir.rs:602` (`342d7:603`): `BinOp::SubWithOverflow => bug!("AddWithOverflow should have been translated already")`
  4. `mir.rs:605` (`342d7:606`): `BinOp::MulWithOverflow => bug!("AddWithOverflow should have been translated already")`
  5. `ty.rs:347` (`342d7:348`): `ty::BoundRegionKind::NamedForPrinting(_) => bug!("only used for pretty printing")`
- **`unreachable!()` (`7` sites at `49d734536222`; `8` at `342d74463af7`):**
  1. `mir.rs:804` (`342d7:805`): `Yield { .. } | CoroutineDrop | FalseEdge { .. } | FalseUnwind { .. } => unreachable!()`
  2. `ty.rs:498` (`342d7:499`): `ty::Bound(ty::BoundVarIndexKind::Canonical, _) => unreachable!()`
  3. `ty.rs:508` (`342d7:509`): `ty::Placeholder(..) | ty::Infer(_) | ty::Error(_) => unreachable!();`
  4. `ty.rs:568` (`342d7:576`): `ty::ConstKind::Error(_) => unreachable!()`
  5. `ty.rs:569` (`342d7:577`): `ty::ConstKind::Infer(_) => unreachable!()`
  6. `ty.rs:958` (`342d7:969`): `_ => unreachable!("{self:?}")` (inside `Stable for ty::AliasTyKind`)
  7. `builder.rs:65` (`342d7:65`): `Err(ErrorHandled::TooGeneric(..)) => unreachable!("Failed to evaluate instance constant: {:?}", const_)`
  8. *(Added by `342d74463af7`)* `ty.rs:804`: `ClauseKind::CompressedTrait(_) => unreachable!()`
- **Explicit `panic!()` (`1` site at `49d734536222`; `0` at `f8a08b688cbe` and `342d74463af7`):**
  1. `ty.rs:561` (`49d734536222` only): `panic!("non-defid alias consts are not supported by rustc_public at the moment")` (replaced by an exhaustive `AliasConstKind` match at `342d74463af7`).
- **`opaque(...)` (`11` lines / `12` calls at `49d734536222`; `6` lines / `6` calls at `342d74463af7`):**
  1. `mir.rs:189` (`342d7:190`): `StatementKind::Coverage(opaque(coverage))`
  2. `mir.rs:381` (`342d7:382`): `FakeReadCause::ForMatchedPlace(opaque(local_def_id))`
  3. `mir.rs:384` (`342d7:385`): `FakeReadCause::ForLet(opaque(local_def_id))`
  4. `mir.rs:478` (`342d7:479`): `UserTypeProjection { base: self.base.as_usize(), projection: opaque(&self.projs) }`
  5. `mir.rs:938` (`342d7:939`): `MonoItem::GlobalAsm(item_id) => StableMonoItem::GlobalAsm(opaque(item_id))`
  6. `ty.rs:645` (`342d7:653`): `FnSig` / `ExistentialProjection` arg/ident debug list `.map(|ident| opaque(ident))`
  7–11. *(Present at `f8a08b688cbe` and `49d734536222`, resolved by `342d74463af7`)* `abi.rs:164, 166 (2 calls), 169, 172, 173`: `PassMode::{Direct, Pair, Cast, Indirect}` attributes and cast targets.

Additionally, `compiler/rustc_public_bridge/src/context/impls.rs` contains `7` `.unwrap()` calls (including `layout_of(...).unwrap()` at `:510, :522` in `342d74463af7`, which panics on monomorphization layout overflows rather than returning `Result::Err`).

---

### 5. Direct Architectural Contrast With Anneal's `trusted/rustc-capture` Seam

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/rustc-capture/src/{driver.rs,main.rs}`, `trusted/rustc-capture/tests/compiler_session.rs`, `trusted/lean/Trusted/MirAst.lean`, `docs/architecture.md:533-635`) + derived synthesis.

#### 5.1 Observed Design of `trusted/rustc-capture` and `Trusted.MirAst` at `c131b320eeeb`

- **Zero dependency on `rustc_public`:** `trusted/rustc-capture/src/driver.rs:11-14` declares `extern crate rustc_driver; extern crate rustc_interface; extern crate rustc_middle; extern crate rustc_session;` (`uses_rustc_public = false`).
- **Compiler binary authentication:** `driver.rs:25,45-47` verifies `rustc_interface::util::rustc_version_str() == Some("1.98.0-nightly (f8a08b688 2026-05-30)")` and terminates via `early_dcx.early_fatal(...)` on any mismatch, guaranteeing alignment with the pinned MIR profile.
- **Fail-closed session lifecycle (`driver.rs:75-84, 137-151`):** `AnalysisCallbacks::after_analysis` records `self.analysis_reached = tcx.dcx().has_errors().is_none()` and unconditionally returns `Compilation::Continue`. `rustc_driver::run_compiler` then executes full codegen/monomorphization validation and `abort_if_errors()`, prohibiting callback evidence on parse errors, type errors, borrow errors, `-Dwarnings` promotions, missing files, invalid options, non-UTF-8 arguments/program names, `--print=sysroot` information requests, post-analysis linker failures, and ICEs (verified by `18` integration tests in `trusted/rustc-capture/tests/compiler_session.rs`).
- **Explicit fail-closed AST contract (`trusted/lean/Trusted/MirAst.lean`):**
  - Every syntax category with unmodeled `rustc_middle::mir` variants defines an explicit `.unsupported` constructor (`7` occurrences in `MirAst.lean`, including `Rvalue.unsupported`, `StatementKind.unsupported`, `AssertKind.unsupported`, `TerminatorKind.unsupported`, causing `Trusted.MirSemantics` to halt with `FaultKind.unsupported` rather than dropping or stringifying constructs).
  - `Trusted.MirAst.BasicBlock` (`:810-813`) explicitly carries `cleanup : Bool`, and `:931-932` mandates that any capture producer populate `BasicBlock.cleanup` directly from `BasicBlockData::is_cleanup`.
  - `Trusted.MirAst.Program` (`:937-942`) omits defaults on `pointerWidthBits` and `mirProfileVersion`, forcing explicit target-layout and MIR-profile attestation.

#### 5.2 Quantitative Seam Comparison and Minimal Upstream Requirements for `rustc_public`

| Capture Seam Requirement | `rustc_public` (`342d74463af7`) | Direct `rustc_middle::mir` (`Runtime(PostCleanup)` + `-Zmir-preserve-ub`) |
| :--- | :--- | :--- |
| Pre-optimization UB-preserving MIR phase | **Fails** (`instance_mir` -> `Runtime(Optimized)` after `RemoveZsts`, `RemoveStorageMarkers`, `GVN`, `UnreachablePropagation`) | **Satisfied** (`mir_drops_elaborated_and_const_checked` + `-Zmir-preserve-ub` disables `RemovePlaceMention`) |
| Error-taint & `required_consts` visibility | **Fails** (`tainted_by_errors` and `required_consts` dropped from `Body`) | **Satisfied** (direct field read on `rustc_middle::mir::Body`) |
| Const-eval PME error handling | **Fails** (`ErrorHandled::Reported => return` swallows error; `TooGeneric => unreachable!`) | **Satisfied** (`Result`-returning eval + `Compilation::Continue` + `tcx.dcx().has_errors()`) |
| Unwind metadata completeness | **Fails** (drops `BasicBlockData::is_cleanup` and `UnwindTerminateReason`) | **Satisfied** (both fields directly available and mapped 1:1) |
| Inline assembly CFG & operand fidelity | **Fails** (drops `targets[1..]`, `asm_macro`, `reg`/`late`/`Const`/`SymFn`/`SymStatic`/`Label`) | **Satisfied** (full `TerminatorKind::InlineAsm` & `InlineAsmOperand` enum access; fail-closed `.unsupported` until modeled) |
| Unmodeled-construct handling | **Fails** (`12 unimplemented!`, `5 bug!`, `8 unreachable!`, `6 opaque`) | **Satisfied** (total `match` mapping every unmodeled variant to `Err(CaptureError)` or `.unsupported`) |

**Derived conclusion (minimal `rustc_public` extension set):** For `rustc_public` to serve as a sound, fail-closed verifier capture seam without breaking out into `rustc_internal`, upstream `rust-lang/rust` would need all six of the following extensions simultaneously:
1. A pre-optimization MIR query exposing `mir_drops_elaborated_and_const_checked` (`MirPhase::Runtime(RuntimePhase::PostCleanup)`) with `-Zmir-preserve-ub` (or an explicit `MirPhase` parameter on `mir_body`/`instance_body`).
2. Preservation of `BasicBlock::is_cleanup: bool` and `UnwindTerminateReason::{Abi, InCleanup}` on both `UnwindAction::Terminate` and `TerminatorKind::Abort`.
3. Exposure of `Body::phase`, `Body::tainted_by_errors`, `Body::required_consts`, and `Body::coroutine` metadata.
4. Fallible `Result<Body, CaptureError>` conversion APIs eliminating `ErrorHandled::Reported => return` swallowing, `layout_of().unwrap()`, and all `25` remaining `unimplemented!`/`bug!`/`unreachable!` trap sites across `mir.rs`, `ty.rs`, and `builder.rs`.
5. Structured `InlineAsm` representation preserving full `targets: Vec<BasicBlockIdx>` and typed operands, plus replacing the `6` remaining `opaque(...)` calls in `mir.rs`/`ty.rs` with typed variants or explicit `Err(Unsupported)`.
6. A driver callback mode that guarantees `Compilation::Continue` and exposes final post-monomorphization `has_errors()` status before releasing verification artifacts.

---

### 6. Kernel-Checked Lean `v4.34.1` Soundness Formalization and Constructive Counterexamples

Basis: execution (Lean `v4.34.1` kernel check of `support/StableMirCaptureSeamSoundness.lean` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`; `0` errors, `0` warnings, `1,207` constants, `0` `._unsafe_rec`, `0` `partial`/`unsafe` constants, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`; every theorem depends strictly on `[propext]`).

#### 6.1 Core Types, Failure Taxonomy, and Two-Surface Completeness

`support/StableMirCaptureSeamSoundness.lean` defines:
- `CaptureBridge := MiddleMir → Except CaptureError TargetMir` (`L220`), mapping a `MiddleMir` body (carrying `phase : MirPhase`, `taintedByErrors : Bool`, and `blocks : List MiddleBlock` with `isCleanup : Bool`, `MiddleStmt`, `MiddleTerminator`, and `UnwindTerminateReason`) into `TargetMir` or a typed `CaptureError`.
- Total, fuel-indexed operational evaluators `evalMiddle` (`L323`, via `List.foldl` and `Nat.rec`) and `evalTarget` (`L418`, parameterized by `TargetSemConfig` for default interpretations when lossy bridges omit `isCleanup`, `UnwindTerminateReason`, `opaqueStub`, or `brokenUnevaluatedConst`).
- Explicit six-variant failure taxonomy `CaptureFailureClass` (`L60-67`): `ubErasingPhaseShift`, `lossyFieldErasure`, `opaqueLoss`, `panicOrIceTrap`, `swallowedConstEvalError`, and `soundFailClosedPostCleanup`.
- Two-surface completeness and phase-preservation predicates (`L756-775`):

```lean
-- support/StableMirCaptureSeamSoundness.lean:756-775
def no_silent_drop (bridge : CaptureBridge) : Prop :=
  ∀ m t, bridge m = .ok t →
    ∀ cfg fuel st, evalTarget cfg fuel t st = evalMiddle fuel m st

def fail_closed_on_unmodeled (bridge : CaptureBridge) : Prop :=
  ∀ m, isModeledPostCleanupBody m = false → ∃ e, bridge m = .error e

def phase_preserves_ub (optPass : MiddleMir → MiddleMir) : Prop :=
  ∀ fuel m st, evalMiddle fuel m st = .ub → evalMiddle fuel (optPass m) st = .ub
```

#### 6.2 Main Theorems (Verbatim Statements)

1. **Soundness of Fail-Closed 1:1 `PostCleanup` Capture (`L925-931`):**
   ```lean
   theorem failClosed_postCleanup_capture_preserves_ub_and_specs
       (m : MiddleMir) (t : TargetMir) (cfg : TargetSemConfig) (fuel : Nat) (st : ExecState)
       (hCap : failClosedPostCleanupBridge m = .ok t) :
       (evalTarget cfg fuel t st = evalMiddle fuel m st) ∧
       (evalMiddle fuel m st = .ub ↔ evalTarget cfg fuel t st = .ub) ∧
       (∀ spec : Outcome → Prop, spec (evalTarget cfg fuel t st) → spec (evalMiddle fuel m st))
   ```
   Paired with `failClosedPostCleanupBridge_twoSurfaceComplete` (`L1055-1058`, proving `no_silent_drop`, `fail_closed_on_unmodeled`, and `phase_preserves_ub id`) and parametric transfer `captureBridge_sound_of_twoSurfaceCompleteness` (`L1089-1094`, proving `SoundForUbChecking` and `SoundForSpecs` for any `(optPass, bridge)` meeting those obligations).

2. **Lossy-Erasure Non-Injectivity Theorem (`L1158-1174`):**
   ```lean
   theorem dropping_isCleanup_or_terminateReason_breaks_unwind_determinism :
       (∃ t,
         lossyDropCleanupBridge progNormalPanic = .ok t ∧
         lossyDropCleanupBridge progCleanupPanic = .ok t ∧
         evalMiddle 2 progNormalPanic validInitState ≠ evalMiddle 2 progCleanupPanic validInitState ∧
         ¬ ∃ semT : TargetMir → Outcome,
             semT t = evalMiddle 2 progNormalPanic validInitState ∧
             semT t = evalMiddle 2 progCleanupPanic validInitState) ∧
       (∃ t,
         lossyDropTerminateReasonBridge progTerminateAbi = .ok t ∧
         lossyDropTerminateReasonBridge progTerminateInCleanup = .ok t ∧
         evalMiddle 2 progTerminateAbi validInitState ≠ evalMiddle 2 progTerminateInCleanup validInitState ∧
         ¬ ∃ semT : TargetMir → Outcome,
             semT t = evalMiddle 2 progTerminateAbi validInitState ∧
             semT t = evalMiddle 2 progTerminateInCleanup validInitState)
   ```
   This proves that once `is_cleanup` or `UnwindTerminateReason` is erased by `rustc_public`, **no deterministic verifier semantics** over the resulting `TargetMir` can faithfully distinguish normal unwinding from double-panic cleanup abort, or ABI-boundary unwind abort from cleanup abort.

3. **Pre-Opt vs. Post-Opt MIR phase separation (`L1198-1209`):**
   ```lean
   theorem postOpt_capture_unsound_for_ub_checking_under_ub_erasing_pass
       (optPass : MiddleMir → MiddleMir) (bridge : CaptureBridge) (cfg : TargetSemConfig)
       (m : MiddleMir) (t : TargetMir) (fuel : Nat) (st : ExecState)
       (hNoDrop : no_silent_drop bridge)
       (hCap : bridge (optPass m) = .ok t)
       (hSourceUb : evalMiddle fuel m st = .ub)
       (hOptErasedUb : evalMiddle fuel (optPass m) st ≠ .ub) :
       postOptCapture optPass bridge m = .ok t ∧
       ubFree (evalTarget cfg fuel t st) ∧
       ¬ ubFree (evalMiddle fuel m st) ∧
       ¬ SoundForUbChecking cfg (postOptCapture optPass bridge)
   ```
   Even if the translation bridge itself is 100% lossless (`no_silent_drop`), hooking it *after* any UB-erasing pass breaks UB-checking soundness.

#### 6.3 Constructive Counterexamples (`L1240-1419`)

| Theorem Name (`StableMirCaptureSeamSoundness.lean`) | Modeled `rustc_public` Defect | Constructive Witness Result |
| :--- | :--- | :--- |
| `ce1_optimized_mir_capture_hides_remove_zsts_ub` (`L1240`) | `RemoveZsts` in `optimized_mir` (`remove_zsts.rs:118-145`) | `progZstDeref` has `evalMiddle = .ub` on `invalidPtrState`; post-opt capture produces `tOpt` with `evalTarget = .ret 0` (`ubFree`), whereas `failClosedPostCleanupBridge` preserves `.ub`. |
| `ce2_dropping_is_cleanup_confuses_normal_and_cleanup_unwind` (`L1262`) | `rustc_public::mir::BasicBlock` drops `is_cleanup` (`mir.rs:29-36`) | `lossyDropCleanupBridge` maps both `progNormalPanic` (`.unwind`) and `progCleanupPanic` (`.abort .inCleanup`) to the identical `TargetMir`, causing `noAbort` to verify falsely and refuting `SoundForSpecs`. |
| `ce3_swallowing_const_eval_error_passes_broken_const_to_verifier` (`L1299`) | `BodyBuilder::visit_const_operand` swallows `ErrorHandled::Reported` (`builder.rs:63`) | `swallowingConstErrorBridge` accepts `progBrokenConst` (`evalMiddle = .constEvalFailure`) as `.ok t` with `evalTarget = .ret 0` (`noConstEvalFailure`), whereas `failClosedPostCleanupBridge` fails closed with `.error .constEvalReportedError`. |
| `ce4_gvn_zero_div_hides_div_by_zero_ub` (`L1326`) | `GVN` `0 / x -> 0` folding (`gvn.rs:1508-1518`) | `runGvnZeroDiv` folds `progZeroDivByZero` (`.ub`) to `.ret 0` (`ubFree`). |
| `ce5_remove_place_mention_without_preserve_ub_hides_place_ub` (`L1354`) | `RemovePlaceMention` pre-`PostCleanup` without `-Zmir-preserve-ub` (`remove_place_mention.rs:13`) | `runRemovePlaceMention false` erases `progPlaceMention`'s `.ub` to `.ret 0`; `runRemovePlaceMention true` preserves `.ub`. |
| `ce6_opaque_inline_asm_under_noop_reading_hides_effect` (`L1379`) | `opaque(format!("{:?}"))` on `InlineAsm` (`mir.rs:707,793-796`) | `opaqueStringifyAsmBridge` hides `.asmSideEffect 7` as `.ret 0` under a no-op reading; `failClosedPostCleanupBridge` rejects with `.error .unmodeledInlineAsm`. |
| `failureClass_failClosed_separation` (`L1410`) | All six `CaptureFailureClass` constructors | Separates fail-closed rejection of `opaqueLoss`, `panicOrIceTrap`, and `swallowedConstEvalError` from exact `.ret 42` acceptance of `soundFailClosedPostCleanup`. |

## Boundaries

### Not Examined
- **Reverse conversion (`compiler/rustc_public/src/unstable/convert/internal/`):** Only the `rustc_middle -> rustc_public` (`convert/stable/`) capture direction and `rustc_public_bridge` were audited; converting `rustc_public` items back to `rustc_middle` was not examined.
- **Downstream `rustc_public` consumer workarounds:** How external verification tools (such as Kani or Charon) patch around `rustc_public` limitations (e.g., via `rustc_internal` escape hatches, custom `mir_opt_level` overrides, or crate-level lints) was not examined.
- **Non-`x86_64` host/target execution:** Live `rustc -Zdump-mir=all` execution ran only on `x86_64-unknown-linux-gnu`.
- **Live MIR-dump probes for `#[rustc_force_inline]` and `const_eval_select` under `-Zmir-opt-level=0`:** While source inspection (`compiler/rustc_mir_transform/src/lib.rs:709,799`) establishes that `remap_mir_for_const_eval_select` and `ForceInline` are not gated by `mir_opt_level >= 1`, `support/mir_phase_ub_probes.rs` did not include a dedicated `const_eval_select` or `#[rustc_force_inline]` probe function.
- **Other `rustc_public` submodules beyond the 7 core bridge/stable files:** Additional `.unwrap()` or `opaque(...)` sites in `compiler/rustc_public/src/{compiler_interface.rs,mir/pretty.rs,ty.rs}` were not added to the 7-file census totals.

### Unknown
- **Future upstream `rustc_public` roadmap:** Whether future `rust-lang/rust` PRs will add a pre-optimization `Runtime(PostCleanup)` body query, expose `is_cleanup`/`UnwindTerminateReason`/`tainted_by_errors`/`required_consts`, or replace `visit_const_operand` early returns with `Result` is unknown and cannot be extrapolated from the May–November 2026 trajectory (which eliminated `abi.rs` opaques while adding `2` new `ty.rs` trap sites).
- **Exhaustiveness of CLI flag mitigation across all future MIR passes:** Whether any combination of unstable `-Z` flags can permanently guarantee zero UB-erasing transformations inside `optimized_mir` across future compiler releases is unknown; `inner_optimized_mir` is designed for codegen optimization rather than UB preservation.

### Known Not to Apply
- **Lean model vs. real compiler:** `support/StableMirCaptureSeamSoundness.lean` proves theorems strictly about its standalone operational `MiddleMir`/`TargetMir` model. It does **not** prove soundness or unsoundness of `rustc`'s Rust source code or of `joshlf/anneal`'s `Trusted.MirSemantics` inside the Lean kernel; that connection is `derived` from source inspection and live MIR dumps.
- **`Drop::replace` is NOT an operational soundness defect:** `compiler/rustc_middle/src/mir/syntax.rs:750-752` explicitly documents that `Drop.replace` is for diagnostics only and has no operational meaning. Dropping `replace` does not break semantic injectivity (matching `toy-clearing-replace-flag-is-equivalence` in `fail-closed-ir-capture-soundness-erasing-pass-sets-and-metadata-injectivity`).
- **`abi.rs` `opaque(...)` counts at `49d734536222` do NOT apply to `342d74463af7`:** All `5` `opaque(...)` lines (`6` calls) in `compiler/rustc_public/src/unstable/convert/stable/abi.rs` were eliminated by `342d74463af7`, reducing the 7-file `opaque` total from `11` lines (`12` calls) to `6` lines (`6` calls).
- **Body equality under `-C opt-level=2 -Zmir-opt-level=0 -Zmir-preserve-ub` does NOT generalize to arbitrary crates or solve `rustc_public`'s structural defects:** Although all `8` probe functions in `support/mir_phase_ub_probes.rs` yielded body-identical `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR dumps under `-C opt-level=2 -Zmir-opt-level=0 -Zmir-preserve-ub`, that flag combination fails on `-C opt-level=0` (where `CheckAlignment`/`CheckNull` still mutate `2/8` probes), does not stop `remap_mir_for_const_eval_select` or `ForceInline`, and does not fix `is_cleanup`/`UnwindTerminateReason`/`required_consts`/`tainted_by_errors` erasure, `ErrorHandled::Reported` swallowing, or the `25` trap sites in `rustc_public`.
- **Current implementation boundary of `joshlf/anneal`'s `trusted/rustc-capture` at `c131b320eeeb`:** At `c131b320eeeb`, `trusted/rustc-capture/src/driver.rs` implements the compiler-session boundary and fail-closed `after_analysis` / late-error verification scaffold (`verification not performed`), not yet the full `Runtime(PostCleanup)` MIR-to-`Trusted.MirAst` serializer; the serializer requirements are documented in `docs/architecture.md` and `trusted/lean/Trusted/MirAst.lean`.

### Unsupported
- **`rustc_public` (all three audited revisions):** Does not support querying `MirPhase::Runtime(RuntimePhase::PostCleanup)` MIR, inspecting `BasicBlockData::is_cleanup`, `UnwindTerminateReason`, `Body::phase`, `Body::tainted_by_errors`, or `Body::required_consts`, translating `TerminatorKind::TailCall`, `WrapUnsafeBinder`, `UnwrapUnsafeBinder`, `ty::View`, or multi-label `InlineAsm` targets (`targets[1..]`), or failing closed with typed `Result` errors on `ErrorHandled::Reported` / `ErrorHandled::TooGeneric` constant-evaluation failures.

## Evidence

### Primary Upstream Git Sources (All 40-Hex SHAs Resolved Live on 2026-11-22)

1. **`rust-lang/rust` @ `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (2026-05-30):**
   - `compiler/rustc_public_bridge/src/builder.rs:30-71` (`BodyBuilder::build`, `visit_const_operand`)
   - `compiler/rustc_public_bridge/src/context/impls.rs:148-150` (`mir_body`), `:619-622` (`instance_body`)
   - `compiler/rustc_public/src/unstable/convert/stable/{mir.rs,ty.rs,abi.rs,mod.rs}` (`4` `unimplemented!`, `8` `todo!`, `4` `bug!`, `7` `unreachable!`, `11` `opaque` lines / `12` calls)
   - `compiler/rustc_public/src/mir/body.rs:15-45,184-187` (`Body` `6` fields, `BasicBlock` `2` fields)
2. **`rust-lang/rust` @ `49d734536222bf28bb6d07d885b3a81d145981da` (2026-09-11):**
   - `compiler/rustc_public_bridge/src/builder.rs:30-71` (`tcx.instance_mir`, `ErrorHandled::Reported => return`, `ErrorHandled::TooGeneric => unreachable!`)
   - `compiler/rustc_public_bridge/src/context/impls.rs:148-150,620-622`
   - `compiler/rustc_public/src/lib.rs:324-340` (`Opaque(String)` / `opaque`)
   - `compiler/rustc_public/src/mir/body.rs:15-45,177-187,294-300,807-815`
   - `compiler/rustc_public/src/rustc_internal/mod.rs:231-249` (`after_analysis` + `Compilation::Stop`)
   - `compiler/rustc_public/src/unstable/convert/stable/{mir.rs,ty.rs,abi.rs,mod.rs}` (`11` `unimplemented!`, `0` `todo!`, `5` `bug!`, `7` `unreachable!`, `1` `panic!`, `11` `opaque` lines / `12` calls)
   - `compiler/rustc_middle/src/mir/mod.rs:206-330,967-1064,1319-1342,1478-1495` (`Body`, `LocalDecl`, `BasicBlockData`, `SourceScopeData`)
   - `compiler/rustc_middle/src/mir/syntax.rs:750-773,1028-1034,1056-1085` (`Drop`, `UnwindTerminateReason`, `InlineAsmOperand`)
   - `compiler/rustc_middle/src/ty/mod.rs:1832-1871` (`TyCtxt::instance_mir`)
   - `compiler/rustc_mir_transform/src/lib.rs:536-822` (`mir_drops_elaborated_and_const_checked`, `run_runtime_cleanup_passes`, `run_optimization_passes`, `optimized_mir`, `inner_optimized_mir`)
   - `compiler/rustc_mir_transform/src/{remove_place_mention.rs:11-24,remove_storage_markers.rs:11-26,remove_zsts.rs:11-145,unreachable_prop.rs:17-120,gvn.rs:128-133,1508-1518}`
   - `compiler/rustc_session/src/config.rs:118-123` (`OptLevel::mir_opt_level`)
3. **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (2026-11-22):**
   - `compiler/rustc_public_bridge/src/builder.rs:30-71` (unchanged)
   - `compiler/rustc_public_bridge/src/context/impls.rs:142-144` (`mir_body` -> `instance_mir`)
   - `compiler/rustc_public/src/unstable/convert/stable/{mir.rs,ty.rs,abi.rs,mod.rs}` (`12` `unimplemented!`, `0` `todo!`, `5` `bug!`, `8` `unreachable!`, `0` `panic!`, `6` `opaque` lines / `6` calls)
   - `compiler/rustc_mir_transform/src/lib.rs:546-838` (same pass placement: `RemovePlaceMention` at `:687`, `RemoveStorageMarkers` at `:730`, `RemoveZsts` at `:732`, `UnreachablePropagation` at `:737`, `GVN` at `:757`)
4. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (2026-11-19):**
   - `trusted/rustc-capture/src/driver.rs:11-152` (no `rustc_public`, `COMPILER_VERSION` pin, `after_analysis` `has_errors().is_none()`, `Compilation::Continue`)
   - `trusted/rustc-capture/src/main.rs:1-41`
   - `trusted/rustc-capture/tests/compiler_session.rs:1-542`
   - `trusted/lean/Trusted/MirAst.lean:47-57,620-868,906-944`
   - `docs/architecture.md:533-635`
5. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (2026-05-31, executed binary):**
   - `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `host: x86_64-unknown-linux-gnu`, `LLVM version: 22.1.6`.
6. **`leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, 2026-09-24):**
   - Kernel-checked `support/StableMirCaptureSeamSoundness.lean` (exit code `0`, `0` warnings, `1,207` constants, `UNSAFE_REC=0`, `UNSAFE_OR_PARTIAL=0`, every main theorem axiom set `[propext]`).

### Preserved Package Support Artifacts

| Relative Path | Bytes | Lines | SHA-256 | Purpose |
| :--- | ---: | ---: | :--- | :--- |
| `support/audit_rustc_public_vs_middle_mir.py` | `27,215` | `658` | `db12e4b52d2a28eb37ad644144826726de923bf842a39857d0caa77a78cc3944` | Standalone Python 3.10+ stdlib audit harness (source trap/opaque census, struct/terminator diffs, Anneal contrast, live `rustc` MIR dump probe runner). |
| `support/mir_phase_ub_probes.rs` | `1,659` | `77` | `f473e56760d7dc8b0b32e9074e7d6cd734803766192eea418aea2d7b3f61c23d` | Eight-function Rust fixture exercising `RemoveZsts`, `GVN` `0/x`, `RemovePlaceMention`, `RemoveStorageMarkers`, `UnreachablePropagation`, `is_cleanup`, and `UnwindTerminateReason`. |
| `support/audit_results.json` | `147,653` | `4,135` | `629a984e76179f5c6a8411f40e943a752e6fd1551802a68490cb89940b5c8409` | Path-scrubbed machine output of `audit_rustc_public_vs_middle_mir.py` across all three pinned `rust-lang/rust` snapshots, `joshlf/anneal@c131b320eeeb`, and all six live `rustc 1.98.0-nightly` flag matrices. |
| `support/StableMirCaptureSeamSoundness.lean` | `59,429` | `1,421` | `4402eb4d2fdddb72606827b2918d9a084c91a07247b28add0d9599154852fa29` | Core-Lean `v4.34.1` formalization proving capture-bridge soundness, two-surface completeness, unwind-metadata non-injectivity, pre-opt vs. post-opt phase separation, and six constructive counterexamples (`[propext]` only, `0` `._unsafe_rec`). |

## Revalidation

Each finding can be revalidated cheaply on any newer `rust-lang/rust`, `joshlf/anneal`, or `leanprover/lean4` revision without repeating the full investigation:

1. **Re-run the programmatic upstream diff and census against a new `rust-lang/rust` revision:**
   ```bash
   NEW_SHA="$(gh api repos/rust-lang/rust/commits/main --jq .sha)"
   python3 support/audit_rustc_public_vs_middle_mir.py \
     --fetch-github \
     --output /tmp/reval_audit.json
   ```
   To include a local checkout at `NEW_SHA`, pass `--rust-tree "new:$NEW_SHA:/path/to/rust"` (and optionally `--anneal-dir /path/to/anneal --anneal-sha <40hex>` and `--rustc rustc`). Check `cross_version_summary` and `builder_and_pipeline_audit` in the JSON output for:
   - Whether `BodyBuilder::build` and `CompilerCtxt::mir_body` still call `tcx.instance_mir(...)` rather than `mir_drops_elaborated_and_const_checked`.
   - Whether `visit_const_operand` still matches `Err(ErrorHandled::Reported(..)) => return`.
   - Whether `BasicBlock` still drops `is_cleanup` and `UnwindTerminate` still drops `UnwindTerminateReason`.
   - Whether trap counts (`unimplemented!`, `bug!`, `unreachable!`, `opaque`) changed.

2. **Narrow five-file upstream diff check (cheapest source-only check):**
   ```bash
   git -C /path/to/rust diff 342d74463af7dd3018ef6aa04dd5500c2deb5bd1..HEAD -- \
     compiler/rustc_public_bridge/src/builder.rs \
     compiler/rustc_public_bridge/src/context/impls.rs \
     compiler/rustc_public/src/unstable/convert/stable/mir.rs \
     compiler/rustc_public/src/mir/body.rs \
     compiler/rustc_mir_transform/src/lib.rs
   ```
   If this diff is empty, every `rustc_public` phase, error-swallowing, field-erasure, and MIR-pass-placement finding in this report continues to hold identically.

3. **Re-run live MIR phase-separation probes on any newer nightly `rustc`:**
   ```bash
   rustc +nightly support/mir_phase_ub_probes.rs --edition=2024 --crate-name=probes \
     -C opt-level=2 -Zdump-mir=all -Zdump-mir-dir=/tmp/mir_reval -o /tmp/mir_reval/libprobes.rlib
   diff -u /tmp/mir_reval/probes.probe_zst_deref.*runtime-post-cleanup.after.mir \
           /tmp/mir_reval/probes.probe_zst_deref.*runtime-optimized.after.mir
   diff -u /tmp/mir_reval/probes.probe_div_zero_unchecked.*runtime-post-cleanup.after.mir \
           /tmp/mir_reval/probes.probe_div_zero_unchecked.*runtime-optimized.after.mir
   ```
   Confirm whether `copy (*_1)` / `(*_1) = ()` and `Div(const 0_u32, move _2)` remain erased in `runtime-optimized`.

4. **Re-verify the Lean `v4.34.1` formalization and axiom hygiene (~3 seconds):**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/StableMirCaptureSeamSoundness.lean
   ```
   Confirm exit code `0` with zero warnings, and append `#print axioms` for the main theorems in a temporary scratch copy to verify strictly `[propext]` (zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`).
