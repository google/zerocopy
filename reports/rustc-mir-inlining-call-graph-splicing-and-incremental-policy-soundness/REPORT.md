# MIR Inlining, Call-Site CFG Splicing, and Incremental Policy Suppression in `rustc` and `Anneal`

## Summary

`rustc` implements MIR-level function inlining as two separate `MirPass` implementations inside `compiler/rustc_mir_transform/src/inline.rs`:

1. **`ForceInline`** (`PassPolicy::Required`, `inline.rs:75-97`): Runs unconditionally at every optimization level—including `-C opt-level=0` and incremental builds—to splice callees annotated with the internal `#[rustc_force_inline]` attribute, emitting hard compile-time diagnostics via `CheckForceInline` (`check_inline.rs:13-85`) and `ForceInliner::on_inline_failure` (`inline.rs:239-260`) whenever an annotated definition or call site cannot be inlined.
2. **`Inline`** (`PassPolicy::optional(...)`, `inline.rs:44-73`): Runs general heuristic MIR inlining (`NormalInliner`, `inline.rs:263-485`) over the `optimized_mir` pass pipeline, silently leaving `TerminatorKind::Call` edges intact whenever policy, exportability, target-feature, cycle, or cost gates reject a call site.

Four high-consequence invariants govern how `Inline` behaves in practice and how downstream intra-procedural MIR verifiers such as `Anneal` (`joshlf/anneal`) must consume `optimized_mir`:

- **Two-Layer Incremental and Opt-Level Suppression**: `OptLevel::mir_opt_level` (`compiler/rustc_session/src/config.rs:123-128`) maps `-C opt-level=0` to `1` and maps **every** nonzero optimization level (`1`, `2`, `3`, `s`, `z`) to `mir_opt_level = 2`. Inside `Inline::policy` (`inline.rs:47-63`), level `2` enables `Inline` **only** when `(optimize == OptLevel::More || optimize == OptLevel::Aggressive) && incremental.is_none()`. Consequently, `-C opt-level=1`, `-C opt-level=s`, and `-C opt-level=z` disable `Inline` even in non-incremental builds, and enabling incremental compilation (`CARGO_INCREMENTAL=1` / `-C incremental=<dir>`, Cargo's default for `dev` and `test` profiles) silently disables `Inline` even at `-C opt-level=2` and `-C opt-level=3`. Furthermore, overriding Layer 1 with `-Z inline-mir=yes` under `-C incremental=<dir>` exposes a **second incremental gate**: `check_codegen_attributes` (`inline.rs:831-834`) rejects even **same-crate** non-generic functions unless `tcx.cross_crate_inlinable(def_id)` holds, and `cross_crate_inlinable` (`cross_crate_inline.rs:84-90`) returns `false` for unmarked (`InlineAttr::None`) functions whenever `tcx.sess.opts.incremental.is_some()` unless `-Z cross-crate-inline-threshold=always` is also supplied.
- **Strict Target-Feature Equality and Hard Exclusions**: Unlike LLVM IR's `TargetTransformInfo::areInlineCompatible` (which permits inlining a target-feature subset into a superset caller after call ABIs are lowered), `rustc` MIR `check_codegen_attributes` (`inline.rs:850-859`) enforces **exact equality** `callee_feature_names == caller_feature_names`, rejecting both baseline-to-`avx2` and `avx512f`-superset-to-`avx2` inlining because moving an inner `TerminatorKind::Call` into a caller with strictly more target features can silently alter the ABI of that inner call. MIR inlining also unconditionally rejects unsized call arguments (`inline.rs:626-632`), C-variadic functions (`check_inline.rs:49-51`, `inline.rs:346`), bodies containing `TerminatorKind::TailCall` (`check_inline.rs:79-83`, `inline.rs:347`), coroutine/async-drop glue (`inline.rs:748-755, 1362-1370`), potential call-graph cycles (`mir_callgraph_cyclic`, `inline/cycle.rs:152-190`), and `#[inline(always)]` callees whose `CostChecker` score exceeds `inline_mir_hint_threshold` (`100` by default, `inline.rs:372, 438-443`).
- **Disjoint Call-Site CFG Splicing and Return-Place Pointer Lowering**: `inline_call` and `Integrator` (`inline.rs:864-1355`) splice a cloned, monomorphized callee body into the caller by allocating a fresh return block (when `target.is_some()`), binding arguments to fresh or moved temporaries (`make_call_args`), shifting non-parameter callee locals (`+ caller_locals`), `SourceScope`s (`+ caller_scopes`, parenting the root callee scope under `callsite.source_info.scope` with `inlined = Some((callee, span))`), and `BasicBlock`s (`+ caller_blocks`), wrapping `UsedInStmtLocals` lacking explicit storage markers in `StorageLive`/`StorageDead`, rewriting `Return` to `Goto(return_block)` (or `Unreachable` for diverging calls), and splicing `UnwindResume` / `UnwindAction::Continue` onto the caller's `cleanup_block` to preserve strict LIFO drop ordering. Critically, in `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `inline.rs:900-927`), projected return destinations (`*ptr` or `slice[idx]`) were pre-borrowed via `Rvalue::Ref(..., BorrowKind::Mut, destination)` *before* entering the callee, injecting immediate Undefined Behavior under Miri Tree Borrows when `destination` points to an uninhabited type (`*mut Infallible`) and the callee unwinds; upstream `rust-lang/rust` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, `inline.rs:898-913`) resolved this soundness defect by testing `!destination.is_stable_offset()` and emitting `Rvalue::RawPtr(RawPtrKind::Mut, destination)`.
- **Whole-Crate Verification Impact and Mechanized Bisimulation**: In `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `Trusted/MirSemantics.lean:1553-1563` is purely intra-procedural and steps every `TerminatorKind.call` to `.fault .unsupported`. Across `google/zerocopy` `v0.8.64` (`907b9175fee081872ec883ca4709e6ad922f8ed0`), enabling `Inline` at non-incremental `-C opt-level=2` eliminates `44.52%` of all `Call` terminators (`5,779 -> 3,206`) and unlocks `+676` newly `100%` call-free bodies (`2,594 -> 3,270` of `4,586`, `56.56% -> 71.30%`) on `rustc 1.98.0-nightly` (`45.74%` / `+624` bodies on `rustc 1.102.0-nightly`), vs. **`0`** under `-C incremental`. Our 5,046-line constructive Lean v4.34.1 mechanization (`support/MirInliningAndCleanupSplicing.lean`, kernel-checked with `[propext, Quot.sound]` only) proves exact interprocedural-to-spliced outcome and LIFO drop-trace bisimulation (`inlineCallSite_bisimulation`), multi-step reduction of acyclic call hierarchies to call-free intra-procedural semantics (`inlineChain_intra_reduction`), and four constructive counterexamples establishing the necessity of each splicing guard.

---

## Applicability

The findings in this package govern six pinned upstream subjects and their interactions:

| Subject | Repository | Immutable Revision | Version / Role |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` (`main` source reference) | `rust-lang/rust` | `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` | Primary compiler source reference for `Inline`, `ForceInline`, `Integrator`, `CheckForceInline`, `CostChecker`, `mir_callgraph_cyclic`, `cross_crate_inlinable`, and `rmeta` `should_encode_mir` (includes the `Rvalue::RawPtr` return-destination fix) |
| `rustc` + `Miri` host execution toolchain | `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `1.98.0-nightly (2026-05-31)`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`; used for live `rustc` MIR dumps, native execution, Miri Tree Borrows (`-Zmiri-tree-borrows`) execution, and `zerocopy` whole-crate census |
| `rustc` comparison baseline toolchain | `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `1.102.0-nightly (2026-11-11)`, LLVM `23.1.5`; comparison point for whole-crate `zerocopy` MIR `Call`-terminator elimination |
| `google/zerocopy` crate | `google/zerocopy` | `907b9175fee081872ec883ca4709e6ad922f8ed0` | `v0.8.64`, compiled with `--features alloc,simd` (`--cfg=no_zerocopy_allocator_api_1_100_0` on `1.98.0-nightly`) for whole-crate MIR body and `Call`-terminator census |
| `joshlf/anneal` verifier & capture driver | `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` and `trusted/rustc-capture/src/driver.rs`; consumer of `tcx.optimized_mir(def_id)` |
| `leanprover/lean4` kernel | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | `v4.34.1`; kernel verifier for `support/MirInliningAndCleanupSplicing.lean` |

### Shared vs. Revision-Specific Behavior

1. **Shared across `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`), `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`), and `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (`main`)**:
   - The split between `ForceInline` (`PassPolicy::Required`) and `Inline` (`PassPolicy::optional(...)`).
   - `OptLevel::mir_opt_level` mapping `OptLevel::No -> 1` and all other optimization levels (`Less`, `More`, `Aggressive`, `Size`, `SizeMin`) to `2`, combined with `Inline::policy`'s `(More || Aggressive) && incremental.is_none()` filter at `mir_opt_level == 2`.
   - `cross_crate_inlinable`'s `incremental.is_some()` rejection of unmarked (`InlineAttr::None`) functions and `check_codegen_attributes`'s reuse of `cross_crate_inlinable` on same-crate non-generic callees.
   - `HISTORY_DEPTH_LIMIT = 20`, `TOP_DOWN_DEPTH_LIMIT = 5`, `inline_mir_threshold = 50`, `inline_mir_hint_threshold = 100`, `cross_crate_inline_threshold = Sometimes(100)`, `CostChecker` penalty constants (`5 / 25 / 50 / 45 / 20`), strict `callee_feature_names == caller_feature_names` equality, and `Integrator` local/scope/block/cleanup splicing.
2. **Revision-specific differences explicitly distinguished**:
   - **Projected return-destination lowering (`inline_call`)**: At `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`inline.rs:900-927`), `dest_needs_borrow(destination)` creates a mutable reference `Rvalue::Ref(..., BorrowKind::Mut { kind: MutBorrowKind::Default }, destination)` whenever `destination.projection` contains `Deref` or `Index(_)`. At `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (`inline.rs:898-913`), `!destination.is_stable_offset()` creates a raw pointer `Rvalue::RawPtr(RawPtrKind::Mut, destination)`, avoiding eager reference validity assertions on uninhabited return types and avoiding Tree Borrows / Stacked Borrows aliasing invalidation during subsequent argument evaluation.
   - **Async-drop shim representation**: At `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`inline.rs:751, 1376`), async-drop shims are variants directly on `ty::InstanceKind` (`AsyncDropGlue`, `AsyncDropGlueCtorShim`); at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (`inline.rs:748-749, 1362-1363`), they are nested under `InstanceKind::Shim(ShimKind::AsyncDropGlue(..) | ShimKind::AsyncDropGlueCtor(..))`.
   - **Whole-crate body count on `zerocopy v0.8.64`**: `1.98.0-nightly` (`--cfg=no_zerocopy_allocator_api_1_100_0`) emits `4,586` bodies to `Inline` (`+676` newly call-free, `-44.52%` calls), whereas `1.102.0-nightly` (with `core` / `alloc` library drift across five months of nightly evolution) emits `4,302` bodies (`+624` newly call-free, `-45.74%` calls).

### Scope Conditions

All host measurements were acquired on `x86_64-unknown-linux-gnu` (`target_arch = "x86_64"`, unwinding `panic = "unwind"`). Target-feature interaction checks (`avx2` vs. `avx512f`) apply to `x86`/`x86_64` feature hierarchies, though `check_codegen_attributes`'s iterator equality check (`callee_feature_names.ne(this_feature_names)`) is architecture-independent across all `rustc` targets.

---

## Findings

### 1. Pass Architecture, Pipeline Placement, and Two-Layer Incremental Suppression

Basis: source + execution + derived

In `compiler/rustc_mir_transform/src/lib.rs`, MIR inlining participates at three distinct points in the `rustc` query pipeline (line ranges shown for `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, with `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` in parentheses):

1. **Pre-optimization `MirLint` validation (`lib.rs:420` / `:406`)**: During `mir_drops_elaborated_and_const_checked`, `&Lint(check_inline::CheckForceInline)` inspects every item annotated with `#[rustc_force_inline]` and emits definition-site errors if the function signature or pre-optimization MIR body violates mandatory inlining preconditions (`check_inline.rs:13-85`).
2. **Mandatory semantic pass `ForceInline` (`lib.rs:723` / `:707`)**: Inside `run_optimization_passes` (which produces `optimized_mir`, `lib.rs:700-804` / `:675-788`), `&inline::ForceInline` runs immediately after `InstSimplify::BeforeInline` and `SimplifyCfg::MakeShim`. Its policy (`inline.rs:83-87`) is unconditional:
   ```rust
   impl<'tcx> crate::MirPass<'tcx> for ForceInline {
       fn policy(&self, _ctx: &crate::PassCtx<'_>) -> PassPolicy {
           // Forced inlining is part of MIR semantics.
           PassPolicy::Required
       }
   ```
   Even when `-Z mir-opt-level=0` disables optional optimization passes, `lib.rs:556-565` (`:526-535`) explicitly runs `ForceInline` if any mentioned item carries `InlineAttr::Force`.
3. **Optional heuristic pass `Inline` (`lib.rs:744` / `:728`)**: Later in `run_optimization_passes`—after `ScalarReplacementOfAggregates`, `MatchBranchSimplification`, `InstCombine`, and `ConstProp` have simplified candidate callees—`&inline::Inline` runs `inline::<NormalInliner<'tcx>>(tcx, body)` followed by `simplify_cfg(tcx, body)` (`inline.rs:65-72`).

#### Layer 1 Suppression: `OptLevel::mir_opt_level` and `Inline::policy`

`PassCtx::mir_opt_level` delegates to `Session::mir_opt_level` (`compiler/rustc_session/src/session.rs`) and `OptLevel::mir_opt_level` (`compiler/rustc_session/src/config.rs:123-128`):

```rust
pub fn mir_opt_level(&self) -> usize {
    match *self {
        OptLevel::No => 1,
        _ => 2,
    }
}
```

When `-Z mir-opt-level` is not explicitly overridden on the command line, **every** nonzero `-C opt-level` (`1`, `2`, `3`, `s`, `z`) produces `ctx.mir_opt_level() == 2`. `Inline::policy` (`inline.rs:47-63`) then evaluates:

```rust
fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
    match ctx.opts.unstable_opts.inline_mir {
        Some(enabled) => PassPolicy::optional(enabled),
        None => PassPolicy::optional(match ctx.mir_opt_level() {
            0 | 1 => false,
            2 => {
                (ctx.opts.optimize == OptLevel::More
                    || ctx.opts.optimize == OptLevel::Aggressive)
                    && ctx.opts.incremental.is_none()
            }
            _ => true,
        }),
    }
}
```

Three non-obvious consequences follow directly from these 17 lines:

1. **`-C opt-level=1`, `-C opt-level=s`, and `-C opt-level=z` disable `Inline`**: Although they set `mir_opt_level() == 2`, `ctx.opts.optimize` is `OptLevel::Less`, `OptLevel::Size`, or `OptLevel::SizeMin`, failing the `More || Aggressive` check unless `-Z mir-opt-level=3` (or `>= 3`) or `-Z inline-mir=yes` is passed.
2. **`CARGO_INCREMENTAL=1` (`-C incremental=<dir>`) disables `Inline` at `-C opt-level=2` and `-C opt-level=3`**: Cargo enables incremental compilation by default for `dev` and `test` profiles (and whenever `CARGO_INCREMENTAL=1` is set in the environment). Setting `profile.dev.opt-level = 2` or `3` in `Cargo.toml` therefore **still leaves `Inline` completely disabled** because `ctx.opts.incremental.is_some()` evaluates `ctx.opts.incremental.is_none()` to `false` (unless `-Z mir-opt-level=3` or `-Z inline-mir=yes` is also passed).
3. **`FnOnce::call_once` and `FnMut::call_mut` shim exclusion in `NormalInliner`**: Even when `Inline` runs, `NormalInliner::check_caller_mir_body` (`inline.rs:345-351`) rejects caller bodies that are `InstanceKind::Shim` (`FnMut::call_mut` and `FnOnce::call_once` closure adapter shims) or C-variadic/tail-calling bodies, whereas `ForceInliner::check_caller_mir_body` (`inline.rs:193-196`) returns `true` for all caller bodies.

#### Layer 2 Suppression: `cross_crate_inlinable` Applied to Same-Crate Callees

Overriding Layer 1 under incremental compilation via `-Z inline-mir=yes` (or `-Z mir-opt-level=3`) uncovers a second, independent incremental suppression mechanism. Inside `check_codegen_attributes` (`inline.rs:831-834`):

```rust
let is_generic = callsite.callee.args.non_erasable_generics().next().is_some();
if !is_generic && !tcx.cross_crate_inlinable(callsite.callee.def_id()) {
    return Err("not exported");
}
```

Notice that `check_codegen_attributes` does **not** check `callsite.callee.def_id().is_local()` before querying `tcx.cross_crate_inlinable`: a non-generic function in the **same crate** (`LocalDefId`) is rejected with `Err("not exported")` unless `cross_crate_inlinable` returns `true`! Turning to `compiler/rustc_mir_transform/src/cross_crate_inline.rs:18-92`:

- If `-Z cross-crate-inline-threshold=always`, `cross_crate_inlinable` returns `true` unconditionally (`cross_crate_inline.rs:34-36`, provided the item has no `#[inline(never)]`).
- If the callee carries `#[inline]`, `#[inline(always)]`, or `#[rustc_force_inline]`, `cross_crate_inlinable` returns `true` (`cross_crate_inline.rs:56`).
- Otherwise (`InlineAttr::None`), lines `85-87` execute:
  ```rust
  if tcx.sess.opts.incremental.is_some() {
      return false;
  }
  ```
  before even consulting the syntactic HIR body budget!

Live execution of `support/probe_mir_inlining.py` (`part1_policy_and_incremental_matrix` in `support/probe_results.json`, `rustc 1.98.0-nightly` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) confirms all seven configurations across four same-crate callees (`#[rustc_force_inline] fn force_callee`, `#[inline] fn hinted_callee`, `fn generic_callee<T: Copy>`, and unmarked `fn unmarked_leaf_callee`):

| Configuration | `rustc` Flags | `ForceInline` Ran | `Inline` Ran | `force_callee` | `hinted_callee` | `generic_callee<u32>` | `unmarked_leaf_callee` | Remaining `Call` Terminators in `probe_entry` |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| `o0_non_incremental` | `-C opt-level=0` | Yes | No | **Inlined** | Kept | Kept | Kept | `wrapping_add`, `generic_callee::<u32>`, `unmarked_leaf_callee`, `hinted_callee` |
| `o1_non_incremental` | `-C opt-level=1` | Yes | No | **Inlined** | Kept | Kept | Kept | `wrapping_add`, `generic_callee::<u32>`, `unmarked_leaf_callee`, `hinted_callee` |
| `os_non_incremental` | `-C opt-level=s` | Yes | No | **Inlined** | Kept | Kept | Kept | `wrapping_add`, `generic_callee::<u32>`, `unmarked_leaf_callee`, `hinted_callee` |
| `o2_incremental_default` | `-C opt-level=2 -C incremental=<DIR>` | Yes | **No** | **Inlined** | Kept | Kept | Kept | `wrapping_add`, `generic_callee::<u32>`, `unmarked_leaf_callee`, `hinted_callee` |
| `o2_incremental_plus_z_inline_mir` | `-C opt-level=2 -Z inline-mir=yes -C incremental=<DIR>` | Yes | Yes | **Inlined** | **Inlined** | **Inlined** | **Kept** | `unmarked_leaf_callee` (blocked by Layer 2 `cross_crate_inlinable`) |
| `o2_incremental_plus_z_inline_mir_and_xcrate_always` | `-C opt-level=2 -Z inline-mir=yes -Z cross-crate-inline-threshold=always -C incremental=<DIR>` | Yes | Yes | **Inlined** | **Inlined** | **Inlined** | **Inlined** | *(none — 0 `Call` terminators)* |
| `o2_non_incremental` | `-C opt-level=2` | Yes | Yes | **Inlined** | **Inlined** | **Inlined** | **Inlined** | *(none — 0 `Call` terminators)* |

---

### 2. Eligibility Gates, Hard Soundness Exclusions, Cost Model, and Recursion Bounds

Basis: source + execution + derived

Every candidate `TerminatorKind::Call` in a caller block is filtered through a deterministic sequence of checks across `resolve_callsite` (`inline.rs:547-605`), `try_inlining` (`inline.rs:610-708`), `check_mir_is_available` (`inline.rs:710-809`), `check_inline` (`check_inline.rs:39-85`), `check_codegen_attributes` (`inline.rs:813-862`), and `Inliner::check_callee_mir_body` (`inline.rs:198-237, 353-445`).

#### Complete Rejection & Soundness Gate Matrix

| Gate / Condition | Source Location (`c7d5ba59d8`) | Rejection String (`Err(...)`) / Outcome | `NormalInliner` (`Inline`) | `ForceInliner` (`ForceInline`) | Semantic / Architectural Reason |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Indirect call (fn pointer / `dyn Fn`) | `inline.rs:556` | `None` (skipped before `try_inlining`) | Skipped | Skipped | Callee `ty::FnDef` is statically unknown |
| Intrinsic without fallback body or `#[rustc_Intrinsic_must_be_overridden]` | `check_inline.rs:57-66` | `"intrinsic without fallback body"` | Rejected | Hard compile error | Backend must lower intrinsic directly |
| `#[rustc_no_mir_inline]` | `check_inline.rs:53-55`, `inline.rs:341` | `"#[rustc_no_mir_inline]"` | Rejected | Hard compile error | Explicit compiler opt-out (e.g., `exchange_malloc`, panic hooks) |
| `#[inline(never)]` | `inline.rs:819-821` | `"never inline attribute"` | Rejected | Unreachable (`InlineAttr::Force` is mutually exclusive) | Explicit user opt-out |
| `#[cold]` callee | `check_inline.rs:45-47`, `inline.rs:338-340` | `"cold"` / `"has cold attribute"` | Rejected | Hard compile error | Preserves cold-path outlining and branch prediction |
| `#[optimize(none)]` on callee | `inline.rs:823-825` | `"has DoNotOptimize attribute"` | Rejected | Hard compile error | Splicing into optimized caller would optimize `DoNotOptimize` code |
| C-variadic signature (`c_variadic`) | `check_inline.rs:49-51`, `inline.rs:346` | `"C variadic"` | Caller & callee rejected | Hard compile error | `VaList` ABI state is tied to physical call frame |
| `TerminatorKind::TailCall` (`become`) | `check_inline.rs:79-83`, `inline.rs:347` | `"can't inline functions with tail calls"` | Caller & callee rejected | Hard compile error | Splicing tail call into non-tail call site would break guaranteed tail recursion |
| Unsized argument (`!arg_ty.is_sized(...)`) | `inline.rs:626-632` | `"call has unsized argument"` | Rejected | Hard compile error | Creating unsized `Local` temporaries in caller MIR is unsound |
| Coroutine state machine / `AsyncDropGlue` | `inline.rs:748-755, 773-775, 1362-1370` | `"coroutine"` / `"async drop glue"` | Rejected | Hard compile error | State-machine `Yield` / `CoroutineDrop` terminators (`bug!()` in `Integrator`) |
| Direct self-recursion or active `history` | `inline.rs:582-584, 725-727` | `"self-recursion"` / `None` | Rejected | Hard compile error (via cycle check) | Prevents unbounded self-expansion |
| Potential mutual recursion (`mir_callgraph_cyclic`) | `inline.rs:786-798`, `cycle.rs:152-190` | `"caller might be reachable from callee"` | Rejected | Hard compile error | Avoids query-system cycle on `optimized_mir` and exponential blowup |
| Sanitizer set mismatch | `inline.rs:837-839` | `"incompatible sanitizer set"` | Rejected | Hard compile error | Prevents mixing `#[sanitize(address = "off")]` into sanitized caller |
| Instruction-set mismatch (`#[instruction_set]`) | `inline.rs:844-848` | `"incompatible instruction set"` | Rejected | Hard compile error | ARM/Thumb ISA mode switches require real branch-and-exchange calls |
| Target-feature inequality (`callee != caller`) | `inline.rs:850-859` | `"incompatible target features"` | Rejected | Hard compile error | Strict equality required before ABI lowering (see analysis below) |
| Non-generic & `!cross_crate_inlinable` | `inline.rs:831-834` | `"not exported"` | Rejected | Bypassed (`Force` sets `cross_crate_inlinable = true`) | Callee might reference unexported private symbols or lack `.rmeta` MIR |
| `CostChecker` exceeds threshold | `inline.rs:367-443`, `cost_checker.rs:15-182` | `"cost above threshold"` | Rejected (even for `#[inline(always)]`!) | **Bypassed** (`ForceInliner` returns `Ok(())`) | Bounds MIR bloat and compile time |

#### Why MIR Inlining Enforces `callee_features == caller_features` (Rejecting Even Supersets)

In LLVM's backend inliner, a function compiled with `+avx2` can generally be inlined into a caller compiled with `+avx2,+avx512f` because call ABIs have already been lowered to concrete LLVM register/stack conventions. At the `rustc` MIR layer, however, `check_codegen_attributes` (`inline.rs:850-859`) enforces **exact iterator equality**:

```rust
let callee_feature_names = callee_attrs.target_features.iter().map(|f| f.name);
let this_feature_names = codegen_fn_attrs.target_features.iter().map(|f| f.name);
if callee_feature_names.ne(this_feature_names) {
    return Err("incompatible target features");
}
```

Both directions are unsound at MIR level without ABI/codegen guards:
1. **Callee has MORE features than caller** (e.g., `#[target_feature(enable = "avx2")]` callee into baseline caller): splicing SIMD intrinsics or instructions into a baseline MIR body causes LLVM to lower vector operations without `+avx2` enabled on the caller function, either failing backend instruction selection or emitting scalarized/invalid code paths that violate the target-feature contract (mechanized as `ce3_cross_feature_mir_inline_violates_feature_gate` in `support/MirInliningAndCleanupSplicing.lean:4929`).
2. **Caller has STRICTLY MORE features than callee** (e.g., `#[target_feature(enable = "avx2")]` callee into `#[target_feature(enable = "avx512f")]` caller, where `avx512f` implies `avx2` on `x86_64`): as documented in `inline.rs:853-857`, the callee MIR body may contain a `TerminatorKind::Call` using the Rust/vector ABI whose register-passing convention depends on the **surrounding function's** enabled target features. Splicing that `Call` terminator into an `+avx512f` caller changes the surrounding function's feature set and can silently alter the ABI used to call a third function!

`support/probe_mir_inlining.py` (`part4_rejections_and_depth_limits.force_inline_diagnostics`) empirically verifies all three target-feature pairings using `#[rustc_force_inline]`:
- Baseline caller -> `#[target_feature(enable = "avx2")]` callee: **compile error** (`rc = 1`, `note: could not be inlined due to: incompatible target features`).
- `#[target_feature(enable = "avx512f")]` superset caller -> `#[target_feature(enable = "avx2")]` callee: **compile error** (`rc = 1`, `note: could not be inlined due to: incompatible target features`).
- `#[target_feature(enable = "avx2")]` caller -> `#[target_feature(enable = "avx2")]` callee: **succeeds** (`rc = 0`, inlined cleanly).

#### `CostChecker` Mechanics and the `#[inline(always)]` Cost Cap

`CostChecker` (`compiler/rustc_mir_transform/src/cost_checker.rs:6-182`) computes `penalty.saturating_sub(bonus)` over the uninstantiated callee `Body`:

- `INSTR_COST = 5` (`Assign`, `NonDivergingIntrinsic::Assume`, binary/unary statements, multi-target `SwitchInt` base).
- `CALL_PENALTY = 25` (`TerminatorKind::Call` to non-intrinsics, `CopyNonOverlapping`, `Drop` of types needing drop). Each argument passed as a `Scalar` or `ScalarPair` constant receives a `bonus` of `INSTR_COST` (`5`), and a constant function/closure argument receives `CALL_PENALTY` (`25`, `cost_checker.rs:36-48`).
- `LANDINGPAD_PENALTY = 50` added whenever a `Call`, `Drop`, `Assert`, or `InlineAsm` carries `UnwindAction::Cleanup(_)` (`cost_checker.rs:105-161`).
- `RESUME_PENALTY = 45` added for `TerminatorKind::UnwindResume` (`cost_checker.rs:161` / `:156`).
- `LARGE_SWITCH_PENALTY = 20` added when `SwitchInt` has more than `4` targets (`cost_checker.rs:137-139`).

Crucially, `NormalInliner::check_callee_mir_body` (`inline.rs:367-443`) treats `#[inline(always)]` identically to `#[inline]` (`InlineAttr::Hint`), assigning both `inline_mir_hint_threshold` (`100` by default, vs. `inline_mir_threshold = 50` for unmarked functions):

```rust
let threshold = if self.top_down_counter > 1 {
    tcx.sess.opts.unstable_opts.inline_mir_hint_threshold.unwrap_or(100)
} else if matches!(callee_attrs.inline, InlineAttr::Hint | InlineAttr::Always) {
    tcx.sess.opts.unstable_opts.inline_mir_hint_threshold.unwrap_or(100)
} else if tcx.cross_crate_inlinable(callsite.callee.def_id()) {
    tcx.sess.opts.unstable_opts.inline_mir_threshold.unwrap_or(50)
} else {
    return Err("not exported");
};
```

Because a single unwinding cleanup pad (`UnwindAction::Cleanup` + `UnwindResume`) already costs `50 + 45 = 95` points before counting any `Assign` or `Drop` statements, **any `#[inline(always)]` function containing a `Drop` guard and a call or panic path exceeds `100` and is refused by `NormalInliner` under default flags**! In `part3_splicing_lifo_cleanup_and_dest_bug`, `inner_callee` (`#[inline(always)]`) inlines into `middle_callee` (`#[inline(always)]`), pushing `middle_callee`'s cost well past `100` so `outer_caller` retains a `Call` to `middle_callee` at default `-O2`, whereas passing `-Z inline-mir-hint-threshold=500` splices the entire 3-frame hierarchy into `outer_caller`.

#### Top-Down Trait Specialization and Exact Depth Limits (`20` and `5`)

Ordinarily, `rustc` optimizes callees bottom-up via on-demand `tcx.optimized_mir(callee)` queries. However, when a generic callee `f::<Impl>` calls an associated trait method `<T as Step>::run`, `f`'s unmonomorphized `optimized_mir` could not inline `<T as Step>::run` before `T = Impl` was instantiated. When `f::<Impl>` is spliced into its monomorphized caller, `process_blocks` (`inline.rs:456-545`) recursively rescans the newly integrated callee blocks **top-down** with `history` extended by `callee.def_id()` and `top_down_counter` incremented whenever a generic callee's newly exposed calls were not already simplified bottom-up (`inline.rs:460-466`). `NormalInliner::changed_arg_types` (`inline.rs:286-288`) halts top-down recursion when:

```rust
self.history.len() > HISTORY_DEPTH_LIMIT || self.top_down_counter > TOP_DOWN_DEPTH_LIMIT
```

with `HISTORY_DEPTH_LIMIT = 20` (`inline.rs:31`) and `TOP_DOWN_DEPTH_LIMIT = 5` (`inline.rs:32`). In `part4_rejections_and_depth_limits` (`support/probe_results.json`):
- A linear 24-level trait-specialized chain (`chain_entry_24 -> step_24::<Impl> -> ... -> step_1::<Impl>`) inlines `21` nested generic frames (`history.len()` growing from `1` through `21`) and stops cleanly at `<Impl as Step20>::run` (`history.len() == 21 > 20`).
- A binary-branching 7-level generic tree (`top_down_entry_7 -> td_7::<TdImpl> -> 2x td_6::<TdImpl> -> ...`) where each level's cost exceeds `inline_mir_threshold` until `top_down_counter` activates `inline_mir_hint_threshold` stops at `4` remaining calls to `td_5::<TdImpl>`.

---

### 3. Call-Site CFG Splicing (`inline_call` and `Integrator`), LIFO Cleanup Pads, and Return-Place Retag Soundness

Basis: source + execution + derived

When `try_inlining` succeeds on a call site `bb_call: destination = callee(args...) -> [return: target, unwind: unwind]`, `inline_call` (`inline.rs:864-1037`) and `Integrator` (`inline.rs:1172-1355`) mutate `caller_body` in eight exact steps:

1. **Fresh Return Trampoline Block (`inline.rs:880-893`)**: If `target = Some(ret_bb)`, `inline_call` does **not** jump from callee `Return` sites directly to `ret_bb` (which may have other CFG predecessors where callee-scoped temporaries were never `StorageLive`). Instead, it pushes a fresh `return_block` initialized with `Goto { target: ret_bb }` and `is_cleanup = caller_body[ret_bb].is_cleanup`.
2. **Projected Return-Destination Stabilization (`inline.rs:895-924`)**:
   - If `destination` involves a dereference or dynamic index (e.g., `a[*i] = f(i)` where `f` mutates `*i`), evaluating `destination` after `f` returns could write to the wrong address.
   - If the resulting `dest` is still not a bare `Local` (e.g., `*_tmp` or `_struct.field`), `remap_destination = true` allocates a fresh `destination_local` via `new_call_temp`, maps callee `RETURN_PLACE` (`_0`) to `destination_local`, and inserts `dest = Move(destination_local)` at the start of `return_block` (`inline.rs:917-924, 962-971`).
3. **Argument Binding & `rust-call` Closure Tuple Unpacking (`make_call_args`, `inline.rs:1039-1141`)**:
   - For `ExternAbi::RustCall` closures when `callee_body.spread_arg.is_none()`, the caller's 2-argument `(closure_env, arg_tuple)` call is unpacked into `[self_temp, field_0_temp, ..., field_{k-1}_temp]` via `Operand::Move(Place::field(tuple, i))`.
   - For standard Rust calls, `create_temp_if_necessary` (`inline.rs:1117-1141`) reuses `local` directly **only** when the argument is `Operand::Move(Place::from(local))` and `caller_body.local_kind(local) == LocalKind::Temp`; otherwise (`Operand::Copy`, constants, user variables, or projected places), it allocates a fresh `new_call_temp` (`StorageLive(tmp)` in `bb_call`, `tmp = Use(arg)`, and `StorageDead(tmp)` prepended to `return_block`).
4. **Disjoint Index Bijection (`Integrator::map_local`, `map_scope`, `map_block`, `inline.rs:1188-1213`)**:
   - `RETURN_PLACE` (`_0`) $\mapsto$ `destination_local`.
   - Callee parameter `_i` ($1 \le i \le \text{args.len()}$) $\mapsto$ `args[i - 1]`.
   - Callee local `_k` ($k > \text{args.len()}$) $\mapsto$ `caller_locals_next + (k - 1 - args.len())`.
   - Callee `SourceScope(s)` $\mapsto$ `caller_scopes_next + s`, with `OUTERMOST_SOURCE_SCOPE`'s `parent_scope` attached to `callsite.source_info.scope` and `inlined = Some((callsite.callee, callsite.source_info.span))` (`inline.rs:1243-1263`). This `inlined` scope chain is how `#[track_caller]` (`ImplicitCallerLocation`) and debug backtraces recover the original call-site `Span` even after arbitrary inlining depth.
   - Callee `BasicBlock(b)` $\mapsto$ `caller_blocks_next + b`.
5. **Synthesizing `StorageLive` / `StorageDead` for `always_live_locals` (`inline.rs:941, 948-983, 1275-1280`)**: Before visiting the callee, `UsedInStmtLocals::new(&callee_body).locals` collects all callee locals referenced in statements; `Integrator::visit_statement` removes any local that already has an explicit `StorageLive` or `StorageDead` inside `callee_body`. For all remaining `always_live_locals` (such as compiler-synthesized temporaries that were implicitly live across the entire callee frame), `inline_call` emits `StorageLive(mapped_local)` in `bb_call` before jumping to the callee and prepends `StorageDead(mapped_local)` in reverse order to `return_block`, preventing unbounded stack-slot accumulation when callees are inlined inside caller loops!
6. **Return Rewriting (`inline.rs:1285-1291, 1321-1327`)**: `TerminatorKind::Return` skips `super_terminator` (preventing a spurious visit to implicit `_0`) and becomes `TerminatorKind::Goto { target: return_block }` when `return_block = Some(tgt)` or `TerminatorKind::Unreachable` when `target = None` (diverging call site).
7. **Unwind & Cleanup-Pad Splicing (`inline.rs:1215-1231, 1328-1335`)**:
   - On every non-cleanup block terminator (`Drop`, `Call`, `Assert`, `InlineAsm`), `map_unwind` maps `UnwindAction::Cleanup(c)` to `UnwindAction::Cleanup(map_block(c))`, preserves `Unreachable` and `Terminate(r)`, and splices `UnwindAction::Continue` (unwinding out of the callee without a local cleanup pad) directly onto the caller's `self.cleanup_block`!
   - Inside callee cleanup blocks (`data.is_cleanup == true`), `TerminatorKind::UnwindResume` is rewritten according to the caller's `self.cleanup_block`:
     - `UnwindAction::Cleanup(caller_cbb)` $\mapsto$ `TerminatorKind::Goto { target: caller_cbb }`
     - `UnwindAction::Continue` $\mapsto$ `TerminatorKind::UnwindResume`
     - `UnwindAction::Unreachable` $\mapsto$ `TerminatorKind::Unreachable`
     - `UnwindAction::Terminate(reason)` $\mapsto$ `TerminatorKind::UnwindTerminate(reason)`
8. **Call-Block Entry Patch & Monomorphization `mentioned_items` Transfer (`inline.rs:1006-1036`)**: `callee_body`'s mapped locals, scopes, debuginfo, and basic blocks are appended to `caller_body`; `bb_call`'s `Call` terminator is replaced with `Goto { target: map_block(START_BLOCK) }`; and `callee`'s `required_consts` and `mentioned_items` replace `MentionedItem::Fn(func_ty)` in `caller_body`.

#### Empirical Verification of 3-Frame LIFO Cleanup Splicing

In `support/probe_mir_inlining.py` (`part3_splicing_lifo_cleanup_and_dest_bug.lifo_cleanup_drop_ordering`), `outer_caller` constructs `Guard(1)` (`_4`) and calls `middle_callee` (`Guard(2)`, `_11`), which calls `inner_callee` (`Guard(3)`, `_12`) and conditionally panics (`panic!("boom")`). After `Inline` with `-Z inline-mir-hint-threshold=500`, `outer_caller`'s MIR (`support/probe_results.json:273`) exhibits the exact spliced cleanup chain:

- **Normal path (`should_panic == false`)**: `bb0 -> bb7 (drop(_12) [Guard(3)] -> bb8, unwind: bb5) -> bb8 (drop(_11) [Guard(2)] -> bb4, unwind: bb2) -> bb4 (drop(_4) [Guard(1)] -> bb1, unwind: bb3) -> bb1 (return)`.
- **Unwind path (`should_panic == true`)**: `bb0 -> bb6 (std::rt::panic_fmt -> bb9) -> bb9 (cleanup: drop(_12) [Guard(3)] -> bb5) -> bb5 (cleanup: drop(_11) [Guard(2)] -> bb2) -> bb2 (cleanup: drop(_4) [Guard(1)] -> bb3) -> bb3 (cleanup: resume)`.

Both native execution (`-O0` un-inlined and `-O2` fully inlined) and Miri under Tree Borrows (`-Zmiri-tree-borrows`, `-Zmir-enable-passes=-Inline` and `-Zmir-enable-passes=+Inline`) exit `0` and record `VAL=42 OK_LIFO=321 CAUGHT_ERR=true PANIC_LIFO=321`.

#### Live Reproduction of the `1.98.0-nightly` `Rvalue::Ref` Return-Destination Soundness Bug

Comparing `inline_call` between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`) and `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (`main`) isolates a real MIR-inlining soundness bug and its fix:

```rust
// 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65), inline.rs:911-925:
let dest = if dest_needs_borrow(destination) {
    let dest = Rvalue::Ref(
        tcx.lifetimes.re_erased,
        BorrowKind::Mut { kind: MutBorrowKind::Default },
        destination,
    );
    ...
    tcx.mk_place_deref(temp)
} else { destination };

// main (c7d5ba59d8e11ee2e2204b173458eec4cb41c973), inline.rs:901-911:
let dest = if !destination.is_stable_offset() {
    let dest = Rvalue::RawPtr(RawPtrKind::Mut, destination);
    ...
    tcx.mk_place_deref(temp)
} else { destination };
```

In custom runtime MIR (`#![feature(custom_mir)]` in `support/probe_mir_inlining.py`), `Call(*p = diverge_unwind(), ReturnTo(bb1), UnwindContinue())` with `p = core::ptr::dangling_mut::<core::convert::Infallible>()` is well-defined prior to `Inline` because `diverge_unwind()` unwinds via `miri_start_unwind` without ever writing to or dereferencing `*p`. When `1.98.0-nightly` runs `+Inline`, `dest_needs_borrow(*_1)` returns `true` and inserts `_2 = &mut (*_1)` **before** entering `diverge_unwind`:

```text
bb0: {
    StorageLive(_2);
    _2 = &mut (*_1);
    ...
    _4 = miri_start_unwind(move _5) -> unwind continue;
}
```

Running `miri -Zmiri-tree-borrows` on `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`support/probe_results.json:275-280`):
- **With `-Zmir-enable-passes=-Inline`**: Miri exits **`0`** (sound unwind caught cleanly by `catch_unwind`).
- **With `-Zmir-enable-passes=+Inline`**: Miri aborts with **`rc = 1`**:
  `error: Undefined Behavior: constructing invalid value of type &mut core::convert::Infallible: encountered a reference pointing to uninhabited type core::convert::Infallible`.

Replacing `Rvalue::Ref` with `Rvalue::RawPtr(RawPtrKind::Mut, destination)` in `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` avoids creating a Rust reference, eliminating both uninhabited-type validity UB and Tree Borrows mutable-retag conflicts with subsequent argument reads.

---

### 4. Cross-Crate `.rmeta` MIR Availability (`should_encode_mir` vs. `cross_crate_inlinable`)

Basis: source + execution + derived

For a downstream crate to inline an upstream crate's function `f`, **two separate `.rmeta` metadata conditions** must hold simultaneously when the upstream crate is compiled (`compiler/rustc_metadata/src/rmeta/encoder.rs` at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, lines `1175-1206` and `1935-1962`; `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, lines `1102-1132` and `1812-1838`):

1. **Serialized `optimized_mir` presence (`should_encode_mir`, `encoder.rs:1175-1206`)**: For an ordinary `DefKind::Fn` or `DefKind::AssocFn`, `encode_opt` is `true` if and only if:
   ```rust
   tcx.sess.opts.unstable_opts.always_encode_mir
       || generics.requires_monomorphization(tcx)
       || tcx.cross_crate_inlinable(def_id)
   ```
   (Additionally, `AssocFn` items in traits with default bodies or specialization children encode MIR via `generics_of` / `impl_defaultness`.)
2. **Serialized `cross_crate_inlinable` bit (`encode_mir`, `encoder.rs:1958`)**: Independently of `should_encode_mir`, `encode_mir` records:
   ```rust
   self.tables.cross_crate_inlinable(def_id, tcx.cross_crate_inlinable(def_id));
   ```
   When the downstream crate runs `Inline`, `check_codegen_attributes` (`inline.rs:832`) checks `!is_generic && !tcx.cross_crate_inlinable(callee_def_id)`—reading that exact serialized boolean from upstream `.rmeta`!

This dual gate produces a critical trap for cross-crate verification and build tooling: **passing `-Z always-encode-mir` when compiling an upstream crate at `-C opt-level=0` (or with `-C incremental`) serializes `optimized_mir` into `.rmeta`, yet downstream `-C opt-level=2` STILL refuses to inline unmarked non-generic upstream functions (`Err("not exported")`) because upstream recorded `cross_crate_inlinable = false`!** Furthermore, in `cross_crate_inline.rs:95-145`, an unmarked non-generic function at non-incremental `-C opt-level=2` only sets `cross_crate_inlinable = true` if its HIR syntactic cost walker stays below `cross_crate_inline_threshold` (`Sometimes(100)`) **and** it contains **zero** HIR calls (`visit_expr` rejects unmarked functions containing calls unless `-Z cross-crate-inline-threshold=always` is set!).

`support/probe_mir_inlining.py` (`part5_cross_crate_rmeta_availability`) verifies all five upstream `.rmeta` compilation modes against a downstream crate compiled at non-incremental `-C opt-level=2`:

| Upstream `libupstream_provider.rmeta` Flags | `pub_generic<u32>` | `#[inline] pub_inline` | `pub_unmarked_small_leaf` | `pub_unmarked_with_call` (calls private `opaque_leaf`) | `#[inline(never)] pub_inline_never_generic<u32>` |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `-C opt-level=2` (non-incremental) | **Inlined** | **Inlined** | **Inlined** | Kept | Kept (MIR encoded for monomorphization, blocked by `InlineAttr::Never`) |
| `-C opt-level=2 -C incremental=<DIR>` | **Inlined** | **Inlined** | **Kept** | Kept | Kept |
| `-C opt-level=0` | **Inlined** | **Inlined** | **Kept** | Kept | Kept |
| `-C opt-level=0 -Z always-encode-mir` | **Inlined** | **Inlined** | **Kept** (`cross_crate_inlinable == false` in `.rmeta`!) | Kept | Kept |
| `-C opt-level=0 -Z always-encode-mir -Z cross-crate-inline-threshold=always` | **Inlined** | **Inlined** | **Inlined** | **Inlined** (exposes call to exported `opaque_leaf`) | Kept |

---

### 5. Whole-Crate `Call`-Terminator Elimination on `google/zerocopy` and Intra-Procedural Verification Unlocking for `Anneal`

Basis: source + execution + derived

In `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), the Lean trusted operational semantics (`trusted/lean/Trusted/MirAst.lean:785-795` and `trusted/lean/Trusted/MirSemantics.lean:1535-1565`) models single-frame intra-procedural execution without an interprocedural call stack:

- `TerminatorKind.call` (`MirSemantics.lean:1559`) steps unconditionally to `.fault .unsupported`.
- `TerminatorKind.unwindResume` (`MirSemantics.lean:1557`) and `TerminatorKind.tailCall` (`MirSemantics.lean:1560`) likewise step to `.fault .unsupported`.

Meanwhile, `anneal-rustc-capture` (`trusted/rustc-capture/src/driver.rs:187-313`) invokes `tcx.optimized_mir(def_id)` after `rustc`'s MIR transformation pipeline completes. Consequently, whether an unannotated or `#[inline]` helper call (`core::mem::size_of`, slice/pointer conversions, wrapper constructors, trait projections) is spliced away by `Inline` **directly determines** whether the function is verifiable intra-procedurally in `Anneal` without manual companion `#[spec]` contracts!

`support/probe_mir_inlining.py` (`part2_zerocopy_crate_census` in `support/probe_results.json`) measures the exact per-pass MIR census across the entire `google/zerocopy` `v0.8.64` crate (`907b9175fee081872ec883ca4709e6ad922f8ed0`, `--features alloc,simd`):

| Toolchain & Mode | Pass Snapshot | Total MIR Bodies | `100%` Call-Free Bodies | Call-Free Share | Total `Call` Terminators | Net Newly Call-Free Bodies | Net Eliminated `Call` Terminators |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `rustc 1.98.0-nightly` (`14210df0e`) `-C opt-level=2` (non-incremental) | Before `ForceInline` | `4,588` | `2,594` | `56.54%` | `5,781` | — | — |
| `rustc 1.98.0-nightly` (`14210df0e`) `-C opt-level=2` (non-incremental) | Before `Inline` | `4,586` | `2,594` | `56.56%` | `5,779` | — | — |
| `rustc 1.98.0-nightly` (`14210df0e`) `-C opt-level=2` (non-incremental) | **After `Inline`** | **`4,586`** | **`3,270`** | **`71.30%`** | **`3,206`** | **`+676`** | **`-2,573` (`-44.52%`)** |
| `rustc 1.98.0-nightly` (`14210df0e`) `-C opt-level=2 -C incremental=<DIR>` | Before/After `ForceInline` | `4,465` | `2,533` | `56.73%` | `5,719` | `0` | `0` |
| `rustc 1.98.0-nightly` (`14210df0e`) `-C opt-level=2 -C incremental=<DIR>` | **`Inline` pass** | **`0` (disabled)** | **`0`** | — | **`0`** | **`0`** | **`0` (`0.00%`)** |
| `rustc 1.102.0-nightly` (`3ef0c22cd`) `-C opt-level=2` (non-incremental) | Before `Inline` | `4,302` | `2,440` | `56.72%` | `5,446` | — | — |
| `rustc 1.102.0-nightly` (`3ef0c22cd`) `-C opt-level=2` (non-incremental) | **After `Inline`** | **`4,302`** | **`3,064`** | **`71.22%`** | **`2,955`** | **`+624`** | **`-2,491` (`-45.74%`)** |

Three quantitative conclusions emerge directly from this whole-crate census:
1. **Nearly half of all `Call` terminators vanish at MIR level**: `Inline` eliminates `44.52%` (`1.98.0-nightly`) to `45.74%` (`1.102.0-nightly`) of all MIR `Call` terminators across `zerocopy` and raises completely call-free MIR bodies from `~56.6%` to `~71.3%` (`+676` / `+624` newly self-contained functions unlocked for intra-procedural verification).
2. **`ForceInline` vs. `Inline` 2-body delta**: On `1.98.0-nightly`, `ForceInline` visits `4,588` bodies while `Inline` visits `4,586`—the exact `2` skipped bodies are `ops::function::FnMut::call_mut` and `ops::function::FnOnce::call_once` (`InstanceKind::Shim`, filtered out by `NormalInliner::check_caller_mir_body` at `inline.rs:350`).
3. **Incremental mode silently suppresses both `Inline` and `123` `optimized_mir` queries**: Under `-C opt-level=2 -C incremental=<DIR>`, not only does `Inline` eliminate `0` calls, `123` unmarked non-generic `zerocopy` helper bodies (`4,588 -> 4,465`, such as `only_derive_is_allowed_to_implement_this_trait` helpers) no longer have `optimized_mir` driven during metadata encoding because `cross_crate_inlinable` flips to `false`. Any MIR extraction driver (`anneal-rustc-capture`) invoked via Cargo **must** enforce `CARGO_INCREMENTAL=0` (or pass `-Z inline-mir=yes -Z cross-crate-inline-threshold=always`) to obtain reproducible, inlined MIR.

---

### 6. Constructive Lean v4.34.1 Mechanization (`support/MirInliningAndCleanupSplicing.lean`)

Basis: source + execution + derived

`support/MirInliningAndCleanupSplicing.lean` (5,046 lines, verified under Lean `v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) mechanizes the operational semantics and soundness boundary of MIR call-site splicing constructively (`[propext, Quot.sound]` only).

#### Semantic Model & Splicer Specification

- **Move-Deinitializing Frame State (`L21-49, L268-416`)**: Each local slot takes values in `LocalSlot := dead | liveUninit | liveVal Val`. `Operand.copy loc` requires `liveVal v` and preserves the slot; `Operand.move loc` requires `liveVal v` and transitions slot `loc` to `liveUninit` (preventing double-reads of moved temporaries); `Stmt.storageLive` sets `liveUninit`; `Stmt.storageDead` sets `dead`; `Stmt.dropGuard loc tag` validates `liveVal _` and appends `tag` to the ordered drop trace `drops : List DropTag`; `Rvalue.featureAdd req` requires `req` in **both** `body.features` and runtime `cpu`; and `Stmt.validateDestRef inhabited` faults with `.undefined` when `inhabited = false`.
- **Dual Semantics (`L419-949`)**:
  - **Interprocedural Semantics (`evalBodyInterproc` / `ExecBody`, `L465-820`)**: Evaluates `Terminator.call calleeId argOps dst target unwind` by checking `!bb.isCleanup`, resolving `callee` in `prog`, checking `allFeaturesPresent callee.features cpu`, evaluating `argOps` left-to-right (including `Operand.move` deinitializations in the caller), initializing a fresh callee frame `[liveUninit] ++ argVals.map liveVal ++ replicate dead`, executing `callee` from block `0` while threading the accumulated drop trace `drops₁`, and routing `.returned retVal drops₂` to `writeLocal locals₂ dst retVal` + `retBb` (or `.fault .undefined` if `target = none`), `.unwound drops₂` to `unwind` (`.cleanup cbb`, `.continue_`, `.terminate`, `.unreachable`), and `.aborted` / `.fault` directly outward.
  - **Intra-Procedural Semantics (`evalBodyIntra` / `ExecBodyIntra`, `L419-465, L821-949`)**: Identical on all intra-procedural statements and terminators, while every `Terminator.call` fails closed with `.fault .unsupported` (mirroring `Anneal` `Trusted/MirSemantics.lean:1559`).
- **Splicer (`inlineCallSite`, `L953-1154`)**: Validates `bodyWellFormed caller false`, `!bb.isCleanup`, `bodyWellFormed callee true` (`stmtValidForCallee` ensuring callee statements do not `StorageDead` `_0`), `isCallFree callee`, `eqNatList callee.features caller.features`, and `argOps.length == callee.argCount`. It appends `buildCallPrelude N callee.argCount callee.numLocals argOps` to `callBb`, redirects `callBb` to `Goto B`, appends `callee.blocks.map (integrateBlock N B (B + C) target unwind)` (shifting all callee local indices by `+ N` and block indices by `+ B`, rewriting `Return -> Goto(B + C)` or `Unreachable`, and rewriting cleanup `UnwindResume -> Goto(cbb)` / `UnwindResume` / `UnwindTerminate` / `Unreachable` and `UnwindAction.continue_ -> unwind`), and appends `mkReturnTrampoline N dst target` (`[Stmt.assign dst (.use (.move N))]` + `Goto retBb`) at block `B + C`.

#### Principal Kernel-Checked Theorems & Sharpness Counterexamples

| Declaration (`MirInliningAndCleanupSplicing.*`) | Lines | Statement Summary | `#print axioms` Footprint |
| :--- | ---: | :--- | :--- |
| `buildCallPrelude_correct` | `1831–1913` | Executing `buildCallPrelude` on `callerSlots ++ extraSlots` agrees identically with `evalArgs` + `initFrameLocals`, producing `callerSlots' ++ calleeLocals₀` without disturbing caller locals `< N` | `[propext, Quot.sound]` |
| `callFree_evalBody_eq` / `callFree_execBody_iff` | `1976–2062` | For any body with `isCallFree body = true`, `ExecBody prog body cpu args out ↔ ExecBodyIntra body cpu args out` (and fuel-bounded evaluators are definitionally equal) | `[propext, Quot.sound]` |
| `inlineCallSite_sound` | `3330–3416` | Forward simulation: `inlineCallSite prog caller callBb = some spliced → ExecBody prog caller cpu args out → ExecBody prog spliced cpu args out` | `[propext, Quot.sound]` |
| `inlineCallSite_complete` | `4251–4413` | Backward completeness proved via 3-region `SplicedInv` (`idx < B`, `B ≤ idx < B + C`, and trampoline `B + C`) over `execBlock_induct_spliced` | `[propext, Quot.sound]` |
| **`inlineCallSite_bisimulation`** | `4415–4421` | **Exact Outcome & LIFO Drop-Trace Bisimulation**: `ExecBody prog caller cpu args out ↔ ExecBody prog spliced cpu args out` across all returns, unwinds, aborts, and faults | `[propext, Quot.sound]` |
| **`inlineChain_intra_reduction`** | `4450–4458` | **Intra-Procedural Reduction**: `ValidInlineChain prog entry finalBody → isCallFree finalBody = true → (ExecBody prog entry cpu args out ↔ ExecBodyIntra finalBody cpu args out)` | `[propext, Quot.sound]` |
| `three_frame_lifo_cleanup_verified` | `4535–4550` | 2-step splicing of `outerCaller -> middleCallee -> innerCallee` produces a call-free body agreeing with interprocedural semantics on `.returned (.int 42) [3, 2, 1]` and `.unwound [3, 2, 1]` | `[propext]` |
| `ce1_unshifted_local_collision_corrupts_caller_frame` | `4686–4727` | Omitting `+ caller.numLocals` causes callee scratch `_1 = 99` to clobber caller local `_1 = 100`, returning `106` instead of `107` (`¬ ExecBody ... (.returned 107 [])`) | `[propext]` |
| `ce2_missing_unwind_resume_to_cleanup_splice_skips_caller_drop` | `4820–4857` | Omitting `UnwindResume -> Goto(callerCleanup)` exits the outer frame early with drop trace `[20]`, skipping the caller's live `Guard(10)` destructor (`[20, 10]`) | `[propext]` |
| `ce3_cross_feature_mir_inline_violates_feature_gate` | `4929–4959` | Omitting `callee.features == caller.features` splices an `avx2`-gated op into a baseline caller (`features = []`), turning a valid runtime call (`.returned 42 []` on `cpu = [1]`) into `.fault .illegalInstruction` | `[propext]` |
| `ce4_unstable_offset_dest_ref_ub_vs_rawptr_sound` | `5014–5036` | Modeling `1.98.0-nightly`'s eager `_2 = &mut (*_1)` (`validateDestRef false`) vs. `main`'s `Rvalue::RawPtr`: eager `&mut Infallible` injects `.fault .undefined` before a diverging callee unwinds (`.unwound [77]`) | `[propext]` |

---

## Boundaries

To prevent over-generalization by downstream compiler or verification tooling, the following negative-space boundaries apply:

- **Known not to apply — `#[inline(always)]` does NOT guarantee MIR inlining in `rustc`**: Evidence in `inline.rs:371-376, 438-443` and `support/probe_results.json` (`part3_splicing_lifo_cleanup_and_dest_bug.lifo_cleanup_drop_ordering.default_threshold_100_inline_always_cost_cap`) establishes that `NormalInliner` still subjects `#[inline(always)]` callees to `CostChecker` against `inline_mir_hint_threshold` (`100`), cycle checks, target-feature equality, and `Incremental` policy suppression. Only the internal `#[rustc_force_inline]` attribute (`ForceInline`) bypasses `CostChecker` and `Inline::policy`.
- **Known not to apply — `-Z always-encode-mir` alone does NOT enable cross-crate MIR inlining of unmarked functions**: As shown in `encoder.rs:1958`, `inline.rs:832`, and `part5_cross_crate_rmeta_availability`, downstream `Inline` checks `tcx.cross_crate_inlinable(callee)` in addition to MIR availability. Unless upstream was compiled with non-incremental `-O2`/`-O3` (for small call-free leaves) or `-Z cross-crate-inline-threshold=always`, unmarked upstream functions remain un-inlined (`Err("not exported")`).
- **Known not to apply — LLVM-style target-feature subset inlining does NOT hold at MIR level**: `check_codegen_attributes` (`inline.rs:850-859`) rejects inlining an `+avx2` callee into an `+avx512f` caller even though `avx512f` implies `avx2` on `x86_64`.
- **Unsupported — Recursive, indirect, C-variadic, tail-calling, unsized-argument, and coroutine callees in `Anneal` without companion contracts**: `rustc` MIR inlining explicitly rejects indirect calls (`fn` pointers / `dyn Trait`), mutually recursive SCCs (`mir_callgraph_cyclic`), `c_variadic` functions, `TailCall` bodies, unsized arguments, and coroutine/async-drop shims. In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, residual `TerminatorKind.call` sites remain **unsupported** in intra-procedural `Trusted/MirSemantics.lean` unless discharged via `#[anneal::spec]` companion contracts or future interprocedural semantics.
- **Not examined — Polymorphization, PGO-guided MIR inlining, and LLVM IR backend inliner interaction**: MIR-level `ForceInline` and `Inline` (`optimized_mir`) are covered here; how LLVM's subsequent CGSCC `InlinerPass` or Link-Time Optimization (`-C lto`) inlines residual `Call` terminators during machine-code generation, as well as `-Z polymorphize` interactions, were **not examined**.
- **Not examined — Multi-callsite iterative splicing of callees that themselves retain residual `Call` terminators in Lean**: In `support/MirInliningAndCleanupSplicing.lean`, `inlineCallSite` requires `isCallFree callee = true` (modeling bottom-up leaf-first splicing, which suffices to inline any finite acyclic call DAG from leaves to root via `ValidInlineChain`, as demonstrated in `three_frame_lifo_cleanup_verified`). Direct top-down splicing of a callee that still contains unspliced `Terminator.call` nodes (followed by `process_blocks` rescanning) is **not examined** in the Lean model, though empirically tested in `part4_rejections_and_depth_limits`.
- **Unknown — Exact upstream commit introducing the `Rvalue::RawPtr` `!is_stable_offset()` fix between `14210df0e` and `c7d5ba59d`**: We establish via direct source and Miri execution that `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`) exhibits the `Rvalue::Ref` uninhabited-destination UB and `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (`2026-11-21` `main`) contains the `Rvalue::RawPtr` fix; the exact intermediate merge commit SHA between those two pins remains **unknown** (not bisected) because both endpoints are directly pinned and verified.

---

## Evidence

All claims in this package trace to immutable upstream Git revisions and reproducible package-local artifacts acquired on `2026-11-21`.

### 1. Primary-Source Code Coordinates

- **`rust-lang/rust` at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` comparison)**:
  - `compiler/rustc_mir_transform/src/inline.rs`:
    - `L31-32` (`:30-31` in `14210df0e`): `HISTORY_DEPTH_LIMIT = 20`, `TOP_DOWN_DEPTH_LIMIT = 5`.
    - `L46-73` (`:45-72`): `impl MirPass for Inline` (`policy` incremental & `OptLevel` check, `run_pass` + `simplify_cfg`).
    - `L83-97` (`:83-96`): `impl MirPass for ForceInline` (`PassPolicy::Required`).
    - `L141-261` (`:148-268`): `ForceInliner` (`on_inline_failure` diagnostic emission).
    - `L263-485` (`:270-501`): `NormalInliner` (`changed_arg_types` depth check at `L287`, `check_codegen_attributes_extra` at `L334-343`, `check_caller_mir_body` shim exclusion at `L345-351`, `check_callee_mir_body` threshold & `CostChecker` invocation at `L353-445`).
    - `L498-605` (`:514-610`): `process_blocks` top-down rescanning and `resolve_callsite`.
    - `L610-708` (`:615-713`): `try_inlining` (unsized argument check at `L626-632`, `try_instantiate_mir_and_normalize_erasing_regions` at `L638-645`, `validate_types` at `L649-652`).
    - `L710-809` (`:715-812`): `check_mir_is_available` (self-recursion, `AsyncDropGlue`, `mir_callgraph_cyclic` at `L791-798`).
    - `L813-862` (`:816-865`): `check_codegen_attributes` (`InlineAttr::Never`, `DoNotOptimize`, `!is_generic && !tcx.cross_crate_inlinable` at `L831-834`, `sanitizers`, `instruction_set`, strict `target_features` equality at `L850-859`).
    - `L864-1037` (`:867-1051`): `inline_call` (`return_block` creation, `!destination.is_stable_offset()` + `Rvalue::RawPtr` at `L901-913` vs. `dest_needs_borrow` + `Rvalue::Ref` at `:900-927` in `14210df0e`, `UsedInStmtLocals` `StorageLive`/`StorageDead` framing at `L941, L948-983`, `mentioned_items` update at `L1026-1036`).
    - `L1039-1163` (`:1053-1177`): `make_call_args` (`ExternAbi::RustCall` tuple unpacking), `create_temp_if_necessary`, `new_call_temp`.
    - `L1172-1355` (`:1186-1369`): `struct Integrator` (`map_local`, `map_scope`, `map_block`, `map_unwind`, `visit_source_scope_data`, `TerminatorKind::Return` at `L1321-1327`, `TerminatorKind::UnwindResume` at `L1328-1335`).
  - `compiler/rustc_mir_transform/src/inline/cycle.rs`: `L65-190` (`:62-188` in `14210df0e`), `process` DFS reachability over generic/inlinable callees and `mir_callgraph_cyclic` query provider.
  - `compiler/rustc_mir_transform/src/check_inline.rs`: `L13-85` (`:14-86` in `14210df0e`), `CheckForceInline`, `is_inline_valid_on_fn`, `is_inline_valid_on_body` (`TailCall` rejection).
  - `compiler/rustc_mir_transform/src/cost_checker.rs`: `L6-182` (`:6-177` in `14210df0e`), `INSTR_COST = 5`, `CALL_PENALTY = 25`, `LANDINGPAD_PENALTY = 50`, `RESUME_PENALTY = 45`, `LARGE_SWITCH_PENALTY = 20`, `CostChecker`.
  - `compiler/rustc_mir_transform/src/cross_crate_inline.rs`: `L18-145` (`c7d5ba59d`), `cross_crate_inlinable` (`cross_crate_inline_threshold == Always` at `L34`, `InlineAttr` dispatch at `L54-58`, `incremental.is_some()` rejection at `L85-87`, HIR call rejection and cost budget at `L95-145`).
  - `compiler/rustc_mir_transform/src/lib.rs`: `L420, L561, L700-804` (`:406, :531, :675-788` in `14210df0e`), `CheckForceInline` lint registration and `run_optimization_passes` ordering.
  - `compiler/rustc_metadata/src/rmeta/encoder.rs`: `L1175-1206, L1935-1962` (`:1102-1132, :1812-1838` in `14210df0e`), `should_encode_mir` and `encode_mir` `cross_crate_inlinable` table serialization.
  - `compiler/rustc_session/src/config.rs`: `L123-128`, `OptLevel::mir_opt_level`.
  - `compiler/rustc_session/src/options.rs`: `L2478, L2543, L2682-2693`, `-Z always-encode-mir`, `-Z cross-crate-inline-threshold`, `-Z inline-mir`, `-Z inline-mir-hint-threshold`, `-Z inline-mir-threshold`.
- **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`**:
  - `trusted/lean/Trusted/MirAst.lean`: `L785-795` (`TerminatorKind`), `L862-867` (`Body`), `L906-943` (`Program`).
  - `trusted/lean/Trusted/MirSemantics.lean`: `L1325-1365` (`evalStatement`), `L1535-1565` (`evalTerminator` failing closed with `.fault .unsupported` on `.call`, `.tailCall`, and `.unwindResume`).
  - `trusted/rustc-capture/src/driver.rs`: `L187-313` (`tcx.optimized_mir(def_id)` extraction).
- **`google/zerocopy` at `907b9175fee081872ec883ca4709e6ad922f8ed0`** (`v0.8.64`): Whole-crate input subject (`src/lib.rs` with `--features alloc,simd`).

### 2. Preserved Package Support Artifacts

1. **`support/probe_mir_inlining.py`**: Self-contained, deterministic Python 3 empirical harness executing all five experimental suites (`part1_policy_and_incremental_matrix`, `part2_zerocopy_crate_census`, `part3_splicing_lifo_cleanup_and_dest_bug`, `part4_rejections_and_depth_limits`, `part5_cross_crate_rmeta_availability`), building a minimal offline Miri `core` + `compiler_builtins` sysroot when needed, scrubbing temporary workspace paths (`<TMP_WORK>`), and emitting JSON.
2. **`support/probe_results.json`**: Complete scrubbed empirical output (`25,082` bytes) captured on `2026-11-21` under `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and Miri `1.98.0-nightly`, alongside the recorded `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` comparison baseline.
3. **`support/MirInliningAndCleanupSplicing.lean`**: Standalone 5,046-line Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) mechanization containing zero external library imports, zero `sorry` axioms, zero `Classical.choice`, and `#print axioms` verification lines at `L5040-5046`.

---

## Revalidation

To revalidate any finding in this report against a newer `rustc` nightly, a newer `google/zerocopy` release, or an updated `leanprover/lean4` toolchain without repeating open-ended exploration:

### 1. Re-verify the Lean 4 Formalization (~15 seconds)

Run the standalone Lean `v4.34.1` kernel checker with asynchronous elaboration disabled, kernel type-checking forced on, and warnings promoted to errors:

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/MirInliningAndCleanupSplicing.lean
```

Expected stdout (exit code `0`, zero warnings):

```text
'MirInliningAndCleanupSplicing.inlineCallSite_bisimulation' depends on axioms: [propext, Quot.sound]
'MirInliningAndCleanupSplicing.inlineChain_intra_reduction' depends on axioms: [propext, Quot.sound]
'MirInliningAndCleanupSplicing.three_frame_lifo_cleanup_verified' depends on axioms: [propext]
'MirInliningAndCleanupSplicing.ce1_unshifted_local_collision_corrupts_caller_frame' depends on axioms: [propext]
'MirInliningAndCleanupSplicing.ce2_missing_unwind_resume_to_cleanup_splice_skips_caller_drop' depends on axioms: [propext]
'MirInliningAndCleanupSplicing.ce3_cross_feature_mir_inline_violates_feature_gate' depends on axioms: [propext]
'MirInliningAndCleanupSplicing.ce4_unstable_offset_dest_ref_ub_vs_rawptr_sound' depends on axioms: [propext]
```

### 2. Re-run the `rustc` + `Miri` Empirical Probe (~45 seconds)

Pass a checkout or extracted archive of `google/zerocopy` (optional `--zerocopy-dir`) and an output path to `support/probe_mir_inlining.py`:

```bash
python3 support/probe_mir_inlining.py \
  --zerocopy-dir /tmp/zerocopy-checkout \
  --out /tmp/revalidated_probe_results.json
```

Check four narrow discriminants in `/tmp/revalidated_probe_results.json`:

1. **Incremental suppression (`part1_policy_and_incremental_matrix`)**: Verify whether `o2_incremental_default.normal_inline_pass_ran` is still `false` and whether `o2_incremental_plus_z_inline_mir.inlined_callees.unmarked_leaf_callee` is still `false`. If either flips to `true`, inspect `Inline::policy` in `compiler/rustc_mir_transform/src/inline.rs` and `cross_crate_inlinable` in `compiler/rustc_mir_transform/src/cross_crate_inline.rs`.
2. **Projected uninhabited return destination under Miri (`part3_splicing_lifo_cleanup_and_dest_bug.unstable_offset_destination_retag_bug_1_98_0_nightly`)**: On toolchains at or before `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `miri_with_inline_rc` is `1` (`&mut core::convert::Infallible` UB); on toolchains incorporating the `Rvalue::RawPtr(RawPtrKind::Mut, destination)` fix (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973` and later), `miri_with_inline_rc` will flip to `0` (`_2 = &raw mut (*_1)` in `spliced_mir_after_inline`), confirming the fix is live in the tested binary.
3. **Target-feature equality & depth limits (`part4_rejections_and_depth_limits`)**: Confirm `callsite_target_feature_avx512f_superset_caller.returncode == 1` (`incompatible target features`), `history_depth_limit_20_probe.remaining_calls_after_inline == ["<Impl as Step20>::run"]`, and `top_down_depth_limit_5_probe.remaining_calls_count == 4`.
4. **Cross-crate `.rmeta` gate (`part5_cross_crate_rmeta_availability`)**: Confirm `upstream_o0_always_encode_mir` still leaves `pub_unmarked_small_leaf` un-inlined (`false`) while `upstream_o0_always_encode_mir_and_xcrate_always` inlines both `pub_unmarked_small_leaf` and `pub_unmarked_with_call` (`true`).

### 3. Narrow Upstream Source Diffs

When rebasing `Anneal`'s `rustc-capture` toolchain pin, diff only these five upstream files in `rust-lang/rust`:
- `compiler/rustc_mir_transform/src/inline.rs` (`Inline::policy`, `check_codegen_attributes`, `inline_call`, `Integrator`)
- `compiler/rustc_mir_transform/src/cross_crate_inline.rs` (`cross_crate_inlinable`)
- `compiler/rustc_mir_transform/src/check_inline.rs` (`CheckForceInline`)
- `compiler/rustc_mir_transform/src/cost_checker.rs` (`CostChecker`)
- `compiler/rustc_metadata/src/rmeta/encoder.rs` (`should_encode_mir`, `encode_mir`)
