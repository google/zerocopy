# `RemoveStorageMarkers` Paradoxical `Miri` Stack UB Erasure and `SsaRangePropagation` / `SimplifyComparisonIntegral` / `EarlyOtherwiseBranch` / `Subtyper` MIR Pass Semantics

## Summary

Five `rustc` MIR transformation passes govern stack lifetime visibility, constant/range folding, integral switch simplification, duplicate-discriminant hoisting, and post-erasure subtyping casts across `Runtime(Initial)` and `Runtime(Optimized)`:

1. **`RemoveStorageMarkers` (`remove_storage_markers.rs`) and `Session::emit_lifetime_markers` (`session.rs`) create a non-monotone `Miri` UB detection paradox across `-Copt-level`:**
   - `RemoveStorageMarkers` runs when `mir_opt_level >= 1 && !ctx.emit_lifetime_markers()` **without consulting `-Zmir-preserve-ub`** (in both `rust-lang/rust` `1.98.0-nightly` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, where `is_required()` returns `true`, and `1.102.0-nightly` `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, where `policy()` returns `PassPolicy::optional(...)`).
   - Because `MIRI_DEFAULT_ARGS` enables `-Zmir-preserve-ub` and `-Zalways-encode-mir` while leaving `-Copt-level=0` (`OptLevel::No`), `Session::emit_lifetime_markers()` returns `false` unless sanitizers or `-Zcodegen-emit-retag` are active. Consequently, overriding `Miri`'s `-Zmir-opt-level=0` default with `-Zmir-opt-level=1` or `-Zmir-opt-level=2` at `-Copt-level=0`—even with explicit `-Zmir-preserve-ub=yes`—strips **100%** of `StorageLive`/`StorageDead` statements (`-26,913` markers across `4,355` `zerocopy` bodies on `1.98.0`; `-25,716` across `4,302` bodies on `1.102.0`).
   - Under Miri's `always_storage_live_locals(body)` initialization rule (`rustc_const_eval/src/interpret/stack.rs`), markerless non-argument locals become frame-lifetime allocations. On a stack use-after-scope bug, `-Zmir-opt-level=2 -Copt-level=0` silently turns an allocation-freed UB failure (`rc = 1`, `alloc151 has been freed`) into a silent pass (`rc = 0`); adding `-Copt-level=1` flips `emit_lifetime_markers()` back to `true`, skips `RemoveStorageMarkers`, and restores UB detection (`rc = 1`), as does `-Zmir-enable-passes=-RemoveStorageMarkers`.

2. **`SsaRangePropagation` (`ssa_range_prop.rs`) is strictly a singleton equality propagator and contradicts its own module docstring:**
   - Lines `1-10` of `ssa_range_prop.rs` illustrate `let b = a < 9; if b { let c = b; let d = a < 8; // d is true }`, which is both arithmetically false at `a = 8` (`(true, false)` natively) and unimplemented.
   - The `212`-line pass (`1.102.0`) only substitutes operands via `try_as_constant`, which requires `range.start == range.end` on a singleton `WrappingRange` inferred from `Intrinsic(Assume(x))`, strictly dominating non-optional `TerminatorKind::Assert` (`1.102.0` adds `&& !msg.is_optional_overflow_check()`, absent in `1.98.0`), unique-predecessor `SwitchInt` arms strictly below `16` total targets (`targets.all_targets().len() < 16`), or single-arm `bool` `SwitchInt` `otherwise` targets. Multi-range tracking uses first-match lookup rather than intersection (`FIXME`).

3. **`SimplifyComparisonIntegral` (`simplify_comparison_integral.rs`) rewrites `Move` to `Copy` on retained comparisons and shifted dead-marker handling between `1.98.0` and `1.102.0`:**
   - Given `_b = Eq/Ne(arg, const K)` paired with `SwitchInt(copy/move _b) -> [0/1: bbA, otherwise: bbB]` over SSA locals and scalar integral/char constants (`Scalar::Ptr(..)` is skipped), the pass replaces `SwitchInt` to branch directly on `to_switch_on` against `K`, swaps targets when needed, and downgrades `Operand::Move(to_switch_on)` inside the comparison statement to `Operand::Copy(to_switch_on)` so no double move or premature move-deinitialization occurs. Under move-deinitializing semantics (`deinitMovedPlace = true`, matching Anneal's MIR semantics), retaining `Move` without downgrading to `Copy` introduces spurious `uninitRead` UB. In `1.98.0`, dead moved comparisons were replaced with `nop;` and `StorageDead` was relocated into successor blocks (`-8` assigns across `7` `zerocopy` bodies); in `1.102.0`, both statement deletion and `StorageDead` relocation were removed, and blocks with intervening `StorageLive`/`StorageDead` on `to_switch_on.local` are skipped instead.

4. **`EarlyOtherwiseBranch` (`early_otherwise_branch.rs`) no longer fires on 2-variant enums after `UnreachableEnumBranching` (`unreachable_enum_branching.rs`):**
   - For exhaustively matched `N`-variant enums after `UnreachableEnumBranching`, `EarlyOtherwiseBranch` fires **if and only if** every enum arm matches exhaustively (`matched == N`) and **`N >= 3`** (plus primitive integer switches without hoisted discriminants). For `Option<()>` (`N = 2`, the docstring's own example), `UnreachableEnumBranching` converts each child inner switch (`1` missed variant, `allowed_variants.len() <= 1`) into `2` explicit targets plus `unreachable`, failing `EarlyOtherwiseBranch`'s single-explicit-target check (`iter.next(), iter.next()` must be `(Some(_), None)`). Disabling `UnreachableEnumBranching` leaves `otherwise` as a live non-empty block (`bb1`), causing the `#95162` guard (`!otherwise_is_empty_unreachable && need_hoist_discriminant`) to reject hoisting.

5. **`Subtyper` (`add_subtyping_projections.rs`) is mandatory in `MirPhase::Runtime(RuntimePhase::Initial)` and emits `Rvalue::Cast(CastKind::Subtype, ...)` strictly on post-erasure type mismatches:**
   - Running `erase_and_anonymize_regions` on both LHS place type and RHS rvalue type collapses ordinary lifetime subtyping (`&'static u8` vs `&'a u8` both erase to `&u8`, emitting zero casts), while preserving bound-region binder differences such as `for<'a> fn(&'a u8)` coerced to `fn(&'static u8)` (`_2 = copy _1; _0 = move _2 as fn(&u8) (Subtype);`). Across `zerocopy` (`4,715` / `4,663` bodies at `Runtime(Initial)`), `Subtyper` emits `0` `(Subtype)` casts, avoiding Anneal's fail-closed `Rvalue::Cast -> .unsupported` rejection.

6. **Kernel-checked Lean 4 mechanization (`support/StorageMarkersParadoxAndRangeSwitchSoundness.lean`):**
   - `5,620` lines, `0` external imports, compiled cleanly with Lean `v4.34.1` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`0` errors, `0` warnings, `0` forbidden tokens, `0` `_unsafe_rec` or audit violations across `1,323` constants and `592` theorems; all `19` audited theorems use strictly `[]`, `[propext]`, or `[propext, Quot.sound]`), establishing forward-only refinement and reverse UB erasure for `RemoveStorageMarkers`, bidirectional equivalence for `SimplifyComparisonIntegral` (`↔`), singleton soundness and docstring/multi-pred/overflow counterexamples for `SsaRangePropagation`, the `k = N >= 3` characterization and `#95162` counterexample for `EarlyOtherwiseBranch`, and operational equivalence for `Subtyper`.

---

## Applicability

This report characterizes upstream compiler source, live compiler/interpreter execution, `zerocopy` crate MIR dumps, Anneal trusted-boundary constraints, and a standalone Lean 4 mechanization for the seven immutable subjects recorded in `REPORT.json`:

| Role | Subject | Revision / Version |
| :--- | :--- | :--- |
| Primary compiler/Miri source audit | `rust-lang/rust` (`1.102.0-nightly`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`) |
| Live execution toolchain & host probes | `rust-lang/rust` (`1.98.0-nightly`, `miri 0.1.0`, LLVM `22.1.6`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`) |
| Anneal vendored `lean-miri` semantics baseline | `rust-lang/rust` | `8144389c895da997dbdecaa635e41d6a50be6ffd` (`2026-10-20`) |
| Anneal `trusted/rustc-capture` `rustc_private` baseline | `rust-lang/rust` | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`2026-05-30`) |
| Verification capture, MIR AST & semantics | `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`) |
| Real-crate MIR census target | `google/zerocopy` (`v0.8.64`) | `907b9175fee081872ec883ca4709e6ad922f8ed0` (`2026-11-21`) |
| Kernel proof assistant | `leanprover/lean4` (`v4.34.1`) | `5045d0056413266e57c625dcd7c365b10e377c52` (`2026-09-24`) |

Version distinctions matter for consumers pinned to specific nightlies:
- **`1.98.0-nightly` (`14210df0e2`) vs. `1.102.0-nightly` (`3ef0c22cdb`) shared behaviors:** Both define identical `RemoveStorageMarkers::run_pass` statement retention (`StorageLive`/`StorageDead`/`Nop` stripped), both omit `-Zmir-preserve-ub` from `RemoveStorageMarkers` gating, both ship `-Zmir-opt-level=0` and `-Zmir-preserve-ub` in `MIRI_DEFAULT_ARGS`, both restrict `SsaRangePropagation` to singleton `WrappingRange` propagation (`try_as_constant`), both run `EarlyOtherwiseBranch` after `UnreachableEnumBranching` with the `#95162` `!otherwise_is_empty_unreachable && need_hoist_discriminant` rejection, and both run mandatory `Subtyper` at `MirPhase::Runtime(RuntimePhase::Initial)`.
- **Version-specific differences verified by direct inspection:**
  1. `RemoveStorageMarkers` migrated from `MirPass::is_enabled` + `is_required() -> true` (`1.98.0`) to `MirPass::policy` returning `PassPolicy::optional(ctx.mir_opt_level() >= 1 && !ctx.emit_lifetime_markers())` (`1.102.0`), while adding `|| self.opts.unstable_opts.codegen_emit_retag.is_some()` to `Session::emit_lifetime_markers` (`1.102.0`).
  2. `SsaRangePropagation` added `&& !msg.is_optional_overflow_check()` on `Assert` terminators in `1.102.0` (`ssa_range_prop.rs:162`); `1.98.0` (`ssa_range_prop.rs:158-171`) propagated from optional overflow assertions too.
  3. `SimplifyComparisonIntegral` in `1.98.0` replaced single-use moved comparison statements with `nop;` (`can_remove_bin_op_stmt = discr.is_move()`, removing `8` assignments in `zerocopy`) and relocated `StorageDead(to_switch_on.local)` to successor block starts (`lines 81-147`); `1.102.0` removed statement deletion and `StorageDead` relocation, skipping candidates when `StorageLive`/`StorageDead` on `to_switch_on.local` follows `stmt_idx` (`lines 142-151`).
  4. `EarlyOtherwiseBranch` in `1.102.0` added the `!place.is_stable_offset()` check for issue `#159591` when `!otherwise_is_empty_unreachable` (`lines 364-382`), absent in `1.98.0`.

Anneal's trusted capture (`joshlf/anneal` `c131b320`, capturing `Runtime(PostCleanup)` MIR per `trusted/correspondence/Trusted/Correspondence.lean:1317` and `trusted/lean/Trusted/MirAst.lean:53`) invokes `rustc` at the host compiler's default MIR optimization settings unless flags override `-Zmir-opt-level`; findings apply wherever Anneal, `Miri`, or downstream MIR tools inspect `Runtime(Initial)`/`Runtime(PostCleanup)`/`Runtime(Optimized)` MIR or evaluate stack-marker preservation.

---

## Findings

### 1. `RemoveStorageMarkers` × `Session::emit_lifetime_markers` × `MIRI_DEFAULT_ARGS`: Non-Monotone Stack UB Erasure Paradox

**Basis: source + execution + derived (Lean 4 kernel proof)**

In `compiler/rustc_mir_transform/src/remove_storage_markers.rs` (`1.102.0`, lines `11-26`), `RemoveStorageMarkers` removes every `StorageLive`, `StorageDead`, and `Nop` statement across all basic blocks whenever:

```rust
fn policy(&self, ctx: &crate::PassCtx<'_>) -> PassPolicy {
    PassPolicy::optional(ctx.mir_opt_level() >= 1 && !ctx.emit_lifetime_markers())
}
```

In `1.98.0` (`remove_storage_markers.rs:10-28`), `is_enabled` used `sess.mir_opt_level() > 0 && !sess.emit_lifetime_markers()` with `is_required() -> true`, which had the same effect on `mir_preserve_ub` bypass: even after migrating to `PassPolicy::optional(...)` in `1.102.0`, `RemoveStorageMarkers::policy` **never checks `ctx.opts.unstable_opts.mir_preserve_ub`** (unlike UB-sensitive passes).

Simultaneously, `Session::emit_lifetime_markers` (`compiler/rustc_session/src/session.rs`, `1.102.0` lines `883-894`, `1.98.0` lines `547-556`) controls whether lifetime markers are considered needed for backend codegen:

```rust
pub fn emit_lifetime_markers(&self) -> bool {
    self.opts.optimize != config::OptLevel::No
    || self.sanitizers().intersects(SanitizerSet::ADDRESS | SanitizerSet::KERNELADDRESS | SanitizerSet::MEMORY | SanitizerSet::HWADDRESS | SanitizerSet::KERNELHWADDRESS)
    // `1.102.0` also includes:
    || self.opts.unstable_opts.codegen_emit_retag.is_some()
}
```

Meanwhile, `Miri`'s `MIRI_DEFAULT_ARGS` (`src/tools/miri/src/lib.rs`, `1.102.0` lines `200-218`, `1.98.0` lines `183-200`) sets `-Zalways-encode-mir`, `-Zmir-preserve-ub`, `-Zmir-opt-level=0`, and disables `CheckAlignment`/`CheckNull`/`CheckEnums`/`ReferencePropagation`/`GVN`, **without setting `-Copt-level` or any sanitizer**. Because `-Copt-level=0` (`OptLevel::No`) is `rustc`'s default, `emit_lifetime_markers()` evaluates to `false` under `Miri`.

When `RemoveStorageMarkers` runs at `-Zmir-opt-level >= 1` (`rustc_mir_transform/src/lib.rs:728` in `1.102.0`, `714` in `1.98.0`, placed right after `Inline`), `100%` of `StorageLive`/`StorageDead` statements disappear. Under Miri's frame initialization (`compiler/rustc_const_eval/src/interpret/stack.rs`, `1.102.0` lines `498-503`; `1.98.0` lines `476-481`), `let always_live = always_storage_live_locals(body);` calls `self.storage_live(local)` at function entry for every local with zero `StorageLive`/`StorageDead` markers anywhere in the body (`MirSemantics.lean:671-690` models this identically via `hasStorageAnnotation`). Thus:
- **Forward soundness holds, reverse soundness fails:** Stripping markers makes locals live from function entry until return, so valid executions that previously read an already-live stack slot still succeed (`StorageMarkersRangeSwitch.forwardRefines_removeStorageMarkers`), whereas programs that take `&raw const x` inside an inner lexical block, let `StorageDead(x)` free `AllocId`, and dereference `*ptr` afterwards transition from `.ub .danglingStackPtr` (`Dead` stack slot / freed `AllocId`) to `.returned (.int 42)` (`ce1_remove_storage_markers_erases_dangling_stack_ptr_ub`).
- **Loop reallocation collapses distinct allocations:** If a loop takes `p = &raw const x` in iteration `0`, drops `x` at scope exit, and enters iteration `1` where `x` is reallocated on the same frame slot, marker preservation (`mir0/opt0` or `mir2/opt1`) assigns a fresh allocation in iteration `1` and detects `alloc has been freed` when reading `*p`; stripping markers (`mir2/opt0`) keeps iteration `0`'s single frame allocation alive across iterations! Without overwriting `x` in iteration `1`, `mir2/opt0` silently returns `observed=10` (`rc = 0`); if iteration `1` writes `x = 11`, Stacked Borrows catches tag invalidation (`attempting a read access using <1579> at alloc776[0x0]`), whereas `-Zmiri-disable-stacked-borrows` silently observes `observed=11` (`rc = 0`) (`ce1b_loop_reallocation_merges_distinct_alloc_ids`).
- **Non-monotone `-Copt-level=0 -> -Copt-level=1` paradox:** Raising optimization flags from `-Zmir-opt-level=2 -Copt-level=0` to `-Zmir-opt-level=2 -Copt-level=1` emits Miri's warning `"warning: Miri does not support optimizations: the opt-level is ignored..."`, **yet actually alters `Session::emit_lifetime_markers()` from `false` to `true`**, suppressing `RemoveStorageMarkers`, leaving all `StorageLive`/`StorageDead` markers intact, and **restoring stack use-after-scope UB detection (`rc = 1`)** (`miri_paradox_non_monotone_in_opt_level`).

Measured on `cargo miri run` (`1.98.0-nightly`) for `single_scope.rs`:

```rust
#[inline(never)]
fn use_after_scope_value() -> i32 {
    let ptr: *const i32;
    {
        let x: i32 = 42;
        ptr = &raw const x;
    }
    unsafe { *ptr }
}
```

| Configuration Flags (`MIRIFLAGS`) | `emit_lifetime_markers()` | `RemoveStorageMarkers` runs? | `use_after_scope_value` MIR markers (before -> after) | Miri `rc` | Observed Output / Diagnostic |
| :--- | :---: | :---: | :---: | :---: | :--- |
| `-Zmir-opt-level=0 -Copt-level=0` | `false` | No (`mir_opt_level < 1`) | pass skipped | `1` | `Undefined Behavior: memory access failed: alloc151 has been freed` |
| `-Zmir-opt-level=1 -Copt-level=0` | `false` | **Yes** | `8` -> `0` (`-Zmir-opt-level=1/2` strips all) | **`0`** | **UB silently erased** (only mir-opt warning) |
| `-Zmir-opt-level=2 -Copt-level=0` | `false` | **Yes** | `4 SL + 4 SD = 8` -> `0` | **`0`** | **UB silently erased** |
| `-Zmir-opt-level=2 -Copt-level=0 -Zmir-preserve-ub=yes` | `false` | **Yes** (ignores flag!) | `4 SL + 4 SD = 8` -> `0` | **`0`** | **UB silently erased even with explicit `-Zmir-preserve-ub=yes`** |
| `-Zmir-opt-level=2 -Copt-level=1` | **`true`** | **No** | pass skipped (markers retained) | **`1`** | **Paradoxically restored:** `alloc151 has been freed` + Miri opt-level warning |
| `-Zmir-opt-level=1 -Copt-level=0 -Zmir-enable-passes=-RemoveStorageMarkers` | `false` | Disabled | skipped | **`1`** | **UB restored:** `alloc151 has been freed` |
| `-Zmir-opt-level=2 -Copt-level=0 -Zmir-enable-passes=-RemoveStorageMarkers` | `false` | Disabled | skipped | **`1`** | **UB restored:** `alloc151 has been freed` |

---

### 2. `SsaRangePropagation` (`ssa_range_prop.rs`): Singleton-Only Reality vs. Aspirational Docstring

**Basis: documentation + source + execution + derived (Lean 4 kernel proof)**

`compiler/rustc_mir_transform/src/ssa_range_prop.rs` (`1.102.0` lines `1-212`, `1.98.0` lines `1-215`) runs at `-Zmir-opt-level >= 2` right after `GVN` / `SimplifyLocals::AfterGVN` (`rustc_mir_transform/src/lib.rs:759` in `1.102.0`, `745` in `1.98.0`). Its module docstring (`lines 1-10`) claims:

```rust
//! A pass that propagates the known ranges of SSA locals.
//! We can know the ranges of SSA locals in certain locations for the following code:
//! ```
//! fn foo(a: u32) {
//!   let b = a < 9; // the integer representation of b is within the full range [0, 2).
//!   if b {
//!     let c = b; // c is true since b is within the range [1, 2).
//!     let d = a < 8; // d is true since a is within the range [0, 9).
//!   }
//! }
//! ```
```

Direct source and execution inspection refutes both parts of line `8`:
1. **Arithmetic falsity (`a = 8`):** When `a == 8`, `a < 9` is `true`, so `a ∈ [0, 9)` (integer values `0..=8`), yet `a < 8` evaluates to `false`. Running the native `rustc -O` specimen at `a = 8` prints `a=8 -> c=true, d=false`, matching Lean theorem `ssaRangeProp_docstring_counterexample_at_8`.
2. **Actual MIR pass implementation (`lines 48-212`):** `SsaRangePropagation` never derives relational bounds from `Lt(a, 9)` and **never uses range intervals at use sites** except to test `range.start == range.end` in `try_as_constant` (`lines 100-115`). On `ssa_docstring_example`, `SsaRangePropagation` folds ONLY `_3 = copy _2 -> const true` and `_0 = (const true, copy _4)` because `switchInt(copy _2) -> [0: bb2, otherwise: bb1]` gives the boolean `otherwise` arm singleton `[1, 1]`, leaving `_4 = Lt(copy _1, const 8_u32)` completely untouched (`probe_results.json:301-308`).

Exact conditions implemented by `RangeSet` (`ssa_range_prop.rs:48-212`, `1.102.0`):
- **Single-assignment SSA filter (`is_ssa`):** `self.ssa.is_ssa(place.local) && place.is_stable_offset()` (`lines 117-119`), relying on `SsaLocals` (`ssa.rs:1-85`), which requires single assignment dominating all uses and forbids raw/mutable address-taking or non-`Freeze` immutable borrows.
- **Range insertion sources (strictly singleton `[1, 1]`, `[val, val]`, or `[0, 0]`):**
  1. `Intrinsic(NonDivergingIntrinsic::Assume(operand))`: inserts `WrappingRange { start: 1, end: 1 }` at `location.successor_within_block()` (`lines 139-145`).
  2. `TerminatorKind::Assert { cond, expected, target, msg, .. }`: inserts `WrappingRange { start: *expected as u128, end: *expected as u128 }` at `target.start_location()` ONLY if `location.strictly_dominates(successor, &self.dominators)` AND (added in `1.102.0`, `line 162`) `!msg.is_optional_overflow_check()` (`1.98.0` lacked this check, risking propagating assumptions from checks elided in release / `-Coverflow-checks=off`; `ssaRangeProp_optional_overflow_assert_unsound_if_propagated` mechanizes why propagating from an unexecuted optional assert returns `.bool true` instead of `.bool false` at `stFalse`).
  3. `TerminatorKind::SwitchInt { discr, targets }`: gated on `targets.all_targets().len() < 16` (`line 173` — empirically verified: `14` arms + `otherwise` = `15 < 16` folds all arms in `ssa_switch_14_arms_lt16`, whereas `15` arms + `otherwise` = `16` skips the entire switch in `ssa_switch_15_arms_eq16`). For each `(val, target)`:
     - Skips any `target` appearing more than once (`distinct_targets[&target] != 1`, `lines 181-184`).
     - Requires `self.has_unique_predecessor(successor.block)` (`predecessors[bb].len() == 1`, `lines 79-81, 186`; empirically verified by `ssa_multi_pred_join` where `bb0` branches `[7: bb2, otherwise: bb1]` and `bb1 -> goto bb2`, giving `bb2` two predecessors and `changed: false`; formalized in `ce3_ssa_range_multi_predecessor_join_unsound_without_intersection` showing joining without unique-predecessor / intersection turns `9` into `7`).
     - Additionally, if `place` is `bool` and `targets.all_values()` has a single value `[val]` (`lines 196-207`) and `otherwise` has a unique predecessor, inserts `[1, 1]` when `val.get() == 0` else `[0, 0]` at `otherwise.start_location()`.
- **Lookup hazard (`get_range`, `lines 90-98`):** Iterates `ranges` and returns the **first** dominating entry (`// FIXME: This should use the intersection of all valid ranges`), relying on `try_as_constant` (`range.start == range.end`) rather than intersecting multiple singletons (note contradictory singletons would indicate dead/unreachable code rather than widening).
- **Lean operational refinement (`ssaRangeProp_singleton_copy_exact_iff`, `ssaRangeProp_singleton_move_forward_refines`):** Replacing `Copy(x)` uses of a singleton constant `x` is an exact equality (`runBody` identical on `.returned`, `.panicked`, and `.ub`); replacing `Move(x)` uses is `ForwardRefines` whenever `x` is not written again (`ssaBodyNoWriteX x`).

---

### 3. `SimplifyComparisonIntegral` (`simplify_comparison_integral.rs`) and `Move -> Copy` Safety

**Basis: source + execution + derived (Lean 4 kernel proof + Anneal semantics)**

`SimplifyComparisonIntegral` (`compiler/rustc_mir_transform/src/simplify_comparison_integral.rs`, `-Zmir-opt-level >= 2`) fuses an integer/char equality test followed by a `SwitchInt` on the boolean result:

```text
_2 = Eq(move _3, const 43_u32);          ==>    _2 = Eq(copy _3, const 43_u32);
switchInt(copy _2) -> [0: bb3, otherwise: bb2];  switchInt(copy _3) -> [43: bb2, otherwise: bb3];
```

Key invariants and `1.98.0 -> 1.102.0` differences observed directly in source and probe dumps:
1. **SSA, stable offset, integral/char, and `Scalar::Ptr(..)` filter (`1.102.0` lines `46-54, 182-199`):** Both the comparison destination (`place_switched_on`) and compared operand (`to_switch_on`) must satisfy `ssa.is_ssa(local)` and `.is_stable_offset()`. The constant must have integral or `char` type (`!ty.is_integral() && !ty.is_char() => return None`) and evaluate via `try_to_scalar()`, then `match opt.branch_value_scalar` skips `Scalar::Ptr(..)` (`line 53`), preventing invalid integer-switch conversion on pointer provenance constants (`simplifyCmp_rejects_ptr_const`).
2. **Arm-swap table (`lines 57-74`):** Switches in MIR either test `0: false_bb, otherwise: true_bb` (standard lowered `if`) or `1: true_bb, otherwise: false_bb` (e.g., negated/reordered CFG):
   - For `BinOp::Eq`: ensures the `true` target is placed in slot `0` (so `[K: bb_true, otherwise: bb_false]`), swapping `(0, 1)` when `first_value == 0`.
   - For `BinOp::Ne`: ensures the `false` target is placed in slot `0` (so `[K: bb_false, otherwise: bb_true]`), swapping `(0, 1)` when `first_value != 0`. (Confirmed in `sci_ne_swap`: `_2 = Ne(move _3, const 43_u32); switchInt(copy _2) -> [0: bb3, otherwise: bb2]` rewrites to `switchInt(copy _3) -> [43: bb3, otherwise: bb2]`.)
3. **Why `Move(to_switch_on)` MUST downgrade to `Copy(to_switch_on)` (`lines 85-94`):** When `_2` stays live (`sci_move_retained_assign`, or unconditionally in `1.102.0`), the comparison statement `_2 = Eq(move _3, const 43_u32)` stays in `bb1` before `switchInt(copy _3)`. Leaving `move _3` in place while reading `copy _3` at the terminator creates a double use after move—which under any move-deinitializing operational semantics (specifically Anneal's `Trusted.MirSemantics`, where `Operand.move` deinitializes non-ZST local slots in `deinitMovedPlace = true` mode, lines `67-70, 921-947`) triggers `.uninitRead` UB on `switchInt(copy _3)`! Downgrading `Move(_3) -> Copy(_3)` eliminates that UB and yields exact bidirectional semantic equivalence (`simplifyCmp_bidirectional_iff`, `runBody` equality under both `deinitMovedPlace = false` and `true`; contrast `ce2_simplify_cmp_retaining_move_operand_deinits_switch_scrutinee_ub` where skipping the downgrade yields `.ub .uninitRead`).
4. **Evolution between `1.98.0` and `1.102.0` (`StorageDead` & dead-statement removal):**
   - `1.98.0` (`lines 81-83, 107-147, 187`): when `discr.is_move()` (`can_remove_bin_op_stmt = true`), `SimplifyComparisonIntegral` replaced `Eq`/`Ne` with `nop;` (`sci_move_dead_stmt_opt0/1`, `-8` assignments across `7` `zerocopy` bodies), and removed intervening `StorageDead(to_switch_on.local)` statements while inserting `StorageDead` at the top of each switch target block.
   - `1.102.0` (`lines 139-151`): deleted both `can_remove_bin_op_stmt` (`nop` replacement) and `StorageDead` relocation; instead, `OptimizationFinder` returns `None` if **any** `StorageLive(local) | StorageDead(local)` for `local == to_switch_on.local` follows `stmt_idx` in `bb.statements[stmt_idx + 1..]`, leaving dead `_2 = Eq(copy _3, const K)` statements to downstream DCE / `DestinationPropagation`.

---

### 4. `EarlyOtherwiseBranch` (`early_otherwise_branch.rs`) × `UnreachableEnumBranching` (`unreachable_enum_branching.rs`)

**Basis: documentation + source + execution + derived (Lean 4 kernel proof)**

`EarlyOtherwiseBranch` (`1.102.0` lines `1-421`, `1.98.0` lines `1-401`, `-Zmir-opt-level >= 2`) hoists an inner `SwitchInt` discriminant read and replaces chained `(x, y)` matches converging to a shared `otherwise` block with a single `Ne(discr_x, discr_y)` early branch. Like `SsaRangePropagation`, its docstring (`lines 11-35`) illustrates `x: Option<()>`, `y: Option<()>` (`N = 2`), which **no longer triggers** under the normal MIR pipeline:

- **Why `Option<()>` (`N = 2`) fails after `UnreachableEnumBranching`:** `UnreachableEnumBranching` runs earlier (`rustc_mir_transform/src/lib.rs:734`, `-Zmir-opt-level >= 1`). In `unreachable_enum_branching.rs:147-168`:
  ```rust
  let replace_otherwise_to_unreachable = allowed_variants.len() <= 1
      && !body.basic_blocks[targets.otherwise()].is_empty_unreachable();
  ```
  For a 2-variant enum (`Option<()>`), `bb0` already matches both variants (`[0: bb3, 1: bb2, otherwise: bb7 -> unreachable]`). Inside child `bb2`, `switchInt(move _3)` explicitly tests `[1: bb5, otherwise: bb1]`, leaving only `1` unmatched variant (`Some` vs `None`, `allowed_variants.len() == 1 <= 1`)! `UnreachableEnumBranching` therefore **expands** that remaining variant explicitly (`[1: bb5, 0: bb1, otherwise: bb7 -> unreachable]`). When `EarlyOtherwiseBranch` later runs (`early_otherwise_branch.rs:416-419`), `verify_candidate_branch` demands **exactly one** explicit target (`(Some(_), None) = (iter.next(), iter.next())`) and rejects `bb2`'s 2-arm switch (`eob_opt2_docstring_default`: `changed: false`)!
- **Why disabling `UnreachableEnumBranching` STILL fails (#95162 soundness guard):** With `-Zmir-enable-passes=-UnreachableEnumBranching`, `bb2` retains `1` explicit arm, **but `bb0`'s `otherwise` (`bb1`, computing `_0 = 1`) is no longer `is_empty_unreachable()`**. Because child blocks read `discriminant(_2)` (`need_hoist_discriminant == true`), `verify_candidate_branch` hits `if !otherwise_is_empty_unreachable && need_hoist_discriminant { return false; }` (`eob.rs:329-363`; `eob_opt2_docstring_no_unreachable_enum_branching`: `changed: false`). Hoisting `discriminant(Q)` before confirming `P` matched a valid arm could read `Q` when `Q` holds invalid enum bit-patterns in `otherwise`—mechanized in `ce4_eob_issue_95162_non_exhaustive_hoist_introduces_ub` (`N >= 2` partial match where invalid `P = Q = 2` reaches `otherwise` -> `100` in source vs `unreachable` UB in buggy hoisted target).
- **Exact firing condition (`ueb_eob_enum_fires_iff_exhaustive_at_least_three_variants`):** After `UnreachableEnumBranching`, enum discriminant hoisting in `EarlyOtherwiseBranch` fires **iff** `matchedArms == enumVariants ∧ enumVariants >= 3`:
  - `bb0` has `allowed_variants.len() == 0 <= 1`, so `otherwise` becomes `empty unreachable`;
  - each child arm only tests `1` value, leaving `enumVariants - 1 >= 2 > 1` unmatched variants, so `UnreachableEnumBranching` leaves the child's `otherwise: bb1` untouched (`eob_e3_three_arms` transforms `E3::{A,B,C}` into `_8 = Ne(copy _6, move _7); switchInt(move _8) -> [0: bb7, otherwise: bb1]`, proved bidirectional in `eob_exhaustive_bidirectional_iff`; whereas `eob_e3_two_arms` fails because `bb0`'s `2` arm goes directly to `bb1` rather than empty `unreachable`).
  - Primitive integer switches without `Discriminant` (`eob_u32_two_arms`, `need_hoist_discriminant == false`) do not need `is_empty_unreachable()` unless an unstable-offset projection triggers the `#159591` guard (`eob.rs:378-382`, `1.102.0`).

---

### 5. `Subtyper` (`add_subtyping_projections.rs`) and `MirPhase::Runtime(Initial)` Cast Insertion

**Basis: source + execution + derived (Lean 4 kernel proof + Anneal AST)**

`Subtyper` (`compiler/rustc_mir_transform/src/add_subtyping_projections.rs`, `1.102.0` lines `1-73`, `1.98.0` lines `1-71`) executes unconditionally (`PassPolicy::Required` / `is_required() == true`) inside `run_runtime_lowering_passes` (`MirPhase::Runtime(RuntimePhase::Initial)`, `rustc_mir_transform/src/lib.rs:662` in `1.102.0`, `633` in `1.98.0`) immediately after `PostAnalysisNormalize`. For every non-generic-reborrow, non-deref-temp assignment `place = rvalue` (`lines 21-49`):

```rust
rval_ty = self.tcx.erase_and_anonymize_regions(rval_ty);
place_ty = self.tcx.erase_and_anonymize_regions(place_ty);
if place_ty != rval_ty {
    let temp = self.patcher.new_temp(rval_ty, ...);
    let new_place = Place::from(temp);
    self.patcher.add_assign(location, new_place, rvalue.clone());
    *rvalue = Rvalue::Cast(CastKind::Subtype, Operand::Move(new_place), place_ty);
}
```

- **What `Subtyper` erases vs. preserves:** Ordinary covariant/invariant lifetime mismatches (`subtyper_covariant_ref`: `&'static u8` assigned to `&'a u8`) erase identically (`&u8 == &u8`), so `Subtyper` leaves `_0 = &(*_1)` untouched (`changed: false`). Conversely, higher-ranked function pointer coercion `subtyper_hrtb` (`for<'a> fn(&'a u8)` coerced to `fn(&'static u8)`) keeps distinct late-bound vs. erased argument types post-erasure, rewriting `_0 = copy _1` into `_2 = copy _1; _0 = move _2 as fn(&u8) (Subtype);` (`changed: true`, `probe_results.json:420-425`).
- **Operational equivalence and Anneal capture interaction:** Dynamically, inserting `tmp = rval; dst = Cast(Subtype, Move(tmp), T)` preserves behavior when `tmp` is a fresh direct local distinct from `dst`, `0`, and tail blocks (`subtyper_region_erasure_and_operational_equiv`). However, in Anneal (`joshlf/anneal` `c131b320`, capturing `Runtime(PostCleanup)` MIR which runs *after* `Runtime(Initial)`), `MirAst.lean:613` lowers `Rvalue::Cast` fail-closed to `.unsupported`. Any Rust body whose lowered MIR retains `CastKind::Subtype` triggers fail-closed `.unsupported` rejection in Anneal's MIR semantics—even when the source wrote zero `as` casts! Fortunately, empirically across `google/zerocopy` (`v0.8.64`, `907b9175`), `Subtyper` produced **`0` `(Subtype)` casts** across all `4,715` (`1.98.0`) and `4,663` (`1.102.0`) `Runtime(Initial)` bodies.

---

### 6. Live `google/zerocopy` MIR Optimization Census (`v0.8.64`, `907b9175`)

**Basis: execution (live `1.98.0-nightly` + `1.102.0-nightly` reference dump telemetry)**

Running `-Zdump-mir=Subtyper|RemoveStorageMarkers|SsaRangePropagation|EarlyOtherwiseBranch|SimplifyComparisonIntegral` over `google/zerocopy` (`--lib`) establishes exact pass-incidence counts:

| Compiler Version & Mode | Pass (`MIR Dump`) | Bodies | Assigns (before -> after) | SwitchInts (before -> after) | StorageLive / Dead / Total Markers (before -> after) | `(Subtype)` Casts | Changed Bodies |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `1.98.0` (`-Copt-level=0 -Zmir-opt-level=2`) | `2-2-003.Subtyper` | `4,715` | `21,018 -> 21,018` | `1,111 -> 1,111` | `15,699 / 15,892 = 31,591 -> 31,591` | `0 -> 0` | `0` |
| `1.98.0` (`-Copt-level=0 -Zmir-opt-level=2`) | `3-2-007.RemoveStorageMarkers` | `4,355` | `18,382 -> 18,382` | `1,032 -> 1,032` | `13,342 / 13,571 = 26,913` -> **`0`** (`-26,913`) | `0 -> 0` | **`2,009`** |
| `1.98.0` (`-Copt-level=0 -Zmir-opt-level=2`) | `3-2-021.SsaRangePropagation` | `4,355` | `10,808 -> 10,808` | `660 -> 660` | `0 -> 0` | `0 -> 0` | `0` |
| `1.98.0` (`-Copt-level=0 -Zmir-opt-level=2`) | `3-2-026.EarlyOtherwiseBranch` | `4,355` | `10,802 -> 10,802` | `655 -> 655` | `0 -> 0` | `0 -> 0` | `0` |
| `1.98.0` (`-Copt-level=0 -Zmir-opt-level=2`) | `3-2-027.SimplifyComparisonIntegral` | `4,355` | `10,802 -> 10,794` (`-8`) | `655 -> 655` | `0 -> 0` | `0 -> 0` | **`7`** |
| `1.98.0` (`-Copt-level=1 -Zmir-opt-level=2`) | `2-2-003.Subtyper` | `4,715` | `20,992 -> 20,992` | `1,111 -> 1,111` | `15,699 / 15,892 = 31,591 -> 31,591` | `0 -> 0` | `0` |
| `1.98.0` (`-Copt-level=1 -Zmir-opt-level=2`) | `3-2-017.SsaRangePropagation` (`RemoveStorageMarkers` skipped) | `4,355` | `10,808 -> 10,808` | `660 -> 660` | **`7,222 / 7,826 = 15,048 -> 15,048`** | `0 -> 0` | `0` |
| `1.98.0` (`-Copt-level=1 -Zmir-opt-level=2`) | `3-2-023.SimplifyComparisonIntegral` | `4,355` | `10,806 -> 10,798` (`-8`) | `657 -> 657` | `7,230 / 7,842 = 15,072 -> 15,072` | `0 -> 0` | **`7`** |
| `1.102.0` (`-Copt-level=0 -Zmir-opt-level=2`) | `2-2-003.Subtyper` | `4,663` | `20,330 -> 20,330` | `1,072 -> 1,072` | `30,392 -> 30,392` | `0 -> 0` | — |
| `1.102.0` (`-Copt-level=0 -Zmir-opt-level=2`) | `RemoveStorageMarkers` | `4,302` | `17,670 -> 17,670` | `997 -> 997` | **`25,716 -> 0`** (`-25,716`) | `0 -> 0` | — |
| `1.102.0` (`-Copt-level=0 -Zmir-opt-level=2`) | `3-2-018.SsaRangePropagation` / `3-2-023.EOB` / `3-2-024.SCI` | `4,302` | `27,176` / `26,426` (`0` delta) | `1,889` / `1,865` (`0` delta) | `39,369` / `40,127` (`0` delta) | `0 -> 0` | `0` delta |

The `7` `zerocopy` functions changed by `SimplifyComparisonIntegral` on `1.98.0` (`assigns: -8`, unchanged `SwitchInt` count because `1.98.0` replaced dead `Eq`/`Ne` assignments with `nop;` while rewriting the `SwitchInt` scrutinee) are: `zerocopy.error-{impl#13}-display_verbose_extras`, `zerocopy.layout-{impl#1}-max_trailing_bytes`, `zerocopy.layout-{impl#2}-has_same_size_sequence`, `zerocopy.layout-{impl#4}-validate_cast_and_convert_metadata`, `zerocopy.split_at-{impl#5}-via_runtime_check`, `zerocopy.util-validate_aligned_to`, and `zerocopy.wrappers-{impl#1}-update`.

---

### 7. Mechanized Lean 4 Theorems and Counterexample Ledger (`StorageMarkersParadoxAndRangeSwitchSoundness.lean`)

**Basis: derived (kernel-checked Lean `v4.34.1` proof + `StorageMarkersAudit.lean`)**

The standalone formalization defines: (a) MIR local slots (`dead`, `direct (Option Val)`, `stack AllocId`), explicit heap `AllocEntry { alive, cell }`, `&raw const`, `*ptr` read/write (`danglingStackPtr`), `discr`, `assume`, `assert` (`enforceOptionalOverflow`), `switchInt`, `deinitMovedPlace`, and fuel-indexed `runBody`; (b) `initScopedState` vs. `initFrameLiveState` (`always_storage_live_locals`); and (c) pass models for all five passes.

| Lean Theorem (`StorageMarkersRangeSwitch.*`) | Formal Property Established | Axioms Reported by `#print axioms` |
| :--- | :--- | :--- |
| `removeStorageMarkers_ignores_mirPreserveUb` | `removeStorageMarkersEnabled` is invariant under flipping `mirPreserveUb` (`true` vs `false`). | `[]` |
| `emitLifetimeMarkers_opt0_vs_opt1` | `emitLifetimeMarkers` flips `false -> true` between `OptLevel.no` and `OptLevel.o1` (with `-Zmir-opt-level=2`, no sanitizers/retag). | `[]` |
| `forwardRefines_removeStorageMarkers` | Stripping all `StorageLive`/`StorageDead` via `RemoveStorageMarkers` unconditionally preserves terminating non-stack `.returned v` values and `.panicked` under explicit `StorageSimRel`. | `[propext, Quot.sound]` |
| `miri_paradox_non_monotone_in_opt_level` | On `danglingStackPtrBody`, `mir0/opt0` yields `.ub .danglingStackPtr`; `mir1/opt0` & `mir2/opt0` (even with `mirPreserveUb := true`) yield `.returned (.int 42)`; `mir2/opt1` & `-RemoveStorageMarkers` restore `.ub .danglingStackPtr`. | `[propext]` |
| `fixedRemoveStorageMarkers_preserves_ub_when_mirPreserveUb` | Gating policy on `&& !s.mirPreserveUb` preserves `.ub .danglingStackPtr` uniformly across all `mirOptLevel`/`optLevel` combinations. | `[propext]` |
| `simplifyCmp_bidirectional_iff` | Exact `runBody` equality (`↔` across `.returned`, `.panicked`, and `.ub`) for `SimplifyComparisonIntegral` on `Eq`/`Ne`, `[0]` vs `[1]` targets, `Move -> Copy` downgrade under both `deinitMovedPlace` modes, and safe continuation tails. | `[propext, Quot.sound]` |
| `simplifyCmp_rejects_ptr_const` | `Scalar::Ptr` constants (`Operand.const (.staticPtr sid)`) are rejected by `isValidSciBinOp`. | `[propext]` |
| `ssaRangeProp_singleton_copy_exact_iff` | `tryAsConstant r = some k` iff singleton, `Assume` guarantees `.bool true`, and replacing `Copy` uses is exact `runBody` equality (`↔`). | `[propext]` |
| `ssaRangeProp_singleton_move_forward_refines` | Replacing `Move` uses of singleton constant `x` preserves non-stack `.returned` / `.panicked` outcomes (`ForwardRefines`) under `ssaBodyNoWriteX`. | `[propext, Quot.sound]` |
| `ssaRangeProp_docstring_counterexample_at_8` | `tryAsConstant { start := 0, stop := 8 } = none`, `8 < 9 = true`, `8 < 8 = false`, `docstringExampleBody` returns `false`, wrong folded body returns `true`. | `[propext]` |
| `ssaRangeProp_optional_overflow_assert_unsound_if_propagated` | Under `enforceOptionalOverflow = false`, propagating from an optional `Assert` turns `.returned (.bool false)` into `.returned (.bool true)` (`panicked` under debug). | `[propext]` |
| `ueb_eob_enum_fires_iff_exhaustive_at_least_three_variants` | Post-`UnreachableEnumBranching` enum `EarlyOtherwiseBranch` fires iff `matchedArms = enumVariants ∧ enumVariants ≥ 3`. | `[propext]` |
| `eob_exhaustive_bidirectional_iff` | Exact `runBody` equality (`↔`) for exhaustive 3-variant `EarlyOtherwiseBranch` hoisting under all `3 × 3` discriminants and both `deinitMovedPlace` modes. | `[propext]` |
| `subtyper_region_erasure_and_operational_equiv` | Region erasure distinguishes `fnPtr true .namedA` from `fnPtr false .rStatic` while equating `.refTy .rStatic` with `.refTy .namedA`; `tmp = op; dst = subtypeCast (move tmp)` preserves `runBody` (`+1` fuel). | `[propext, Quot.sound]` |
| `Examples.ce1_remove_storage_markers_erases_dangling_stack_ptr_ub` | Explicit witness of `¬ ReverseUbSound` for `RemoveStorageMarkers` on `danglingStackPtrBody`. | `[propext]` |
| `Examples.ce1b_loop_reallocation_merges_distinct_alloc_ids` | Cross-iteration dangling pointer reads `11` (`rc = 0`) when markers are stripped instead of faulting `.ub .danglingStackPtr`. | `[propext]` |
| `Examples.ce2_simplify_cmp_retaining_move_operand_deinits_switch_scrutinee_ub` | Retaining `Move` in dead comparison `Eq(move 1, 43)` under `deinitMovedPlace = true` crashes `switchInt(copy 1)` with `.ub .uninitRead` whereas `rewriteSciBlock` (`Copy 1`) returns `10`. | `[propext]` |
| `Examples.ce3_ssa_range_multi_predecessor_join_unsound_without_intersection` | Propagating singleton `[7, 7]` across a multi-predecessor join (`bb0 -> bb1 -> bb2` vs `bb0 -> bb2`) corrupts input `9` to `7`. | `[propext]` |
| `Examples.ce4_eob_issue_95162_non_exhaustive_hoist_introduces_ub` | Hoisting child `discr` when parent `otherwise` is non-empty turns safe return `100` (input `2`) into `.ub .unreachableReached`. | `[propext]` |

---

## Boundaries

1. **`RemoveStorageMarkers` interactions beyond stack-local raw pointers (known not to apply / not examined):**
   - **Sanitizers & `-Zcodegen-emit-retag` (`known not to apply`):** When ASan, MSan, HWASan, KASAN, KHWASan, or `-Zcodegen-emit-retag` (`1.102.0`+) is active, `emit_lifetime_markers()` returns `true` even at `-Copt-level=0`, so `RemoveStorageMarkers` does not run.
   - **Heap (`Box`) / static allocations (`known not to apply`):** Stripping stack storage markers does not affect heap deallocation (`__rust_dealloc`) or static provenance lifetimes.
   - **Codegen LLVM backend equivalence (`not examined`):** Whether `-Copt-level=0 -Zmir-opt-level=2` LLVM IR suffers secondary codegen regressions relative to `-Copt-level=0 -Zmir-opt-level=0` outside `Miri` interpreter checks was not benchmarked.
2. **`SsaRangePropagation` scope exclusions (`known not to apply` / `unsupported`):**
   - Non-single-predecessor join blocks (`predecessors[bb].len() > 1`), switches with `>= 16` total targets (`arms.len() + 1 >= 16`), multi-valued arms jumping to the same target block (`distinct_targets[&target] != 1`), non-singleton intervals (`start < stop`), `bool` inequality tests like `a < 9 => a < 8`, and optional overflow `Assert`s in `1.102.0` are **not** simplified (`unsupported` / unimplemented in `ssa_range_prop.rs`).
   - Interplay when `GVN` or `ReferencePropagation` is re-enabled (unlike `MIRI_DEFAULT_ARGS`, which disables both) is documented at pass-order level (`rustc_mir_transform/src/lib.rs`) but not exhaustively tested beyond single-function specimens.
3. **`SimplifyComparisonIntegral` exclusions (`known not to apply`):**
   - Non-SSA places (`!ssa.is_ssa`), unstable-offset projections, `Float` types, `Scalar::Ptr(..)` provenance constants (`line 53`), non-`Eq`/`Ne` operators (`Lt`, `Le`, etc.), and in `1.102.0` any block where `StorageLive`/`StorageDead` on `to_switch_on.local` appears after the comparison statement (`lines 142-151`) do not fire.
4. **`EarlyOtherwiseBranch` boundaries (`known not to apply` / `not examined`):**
   - Only `NeedHoistDiscriminant` single-statement enum blocks and `0`-statement integer `SwitchInt` children with matching parent/child types (`child_ty == parent_ty`), single explicit arm per child converging to a common `destination` (or empty `unreachable`), and clean non-cleanup blocks are handled; 2-variant enums with `UnreachableEnumBranching` enabled are `known not to apply`. Nested 3+-tuple matches or multi-statement child blocks were not tested beyond the pass guards inspected.
5. **`Subtyper` and Anneal TCB (`not examined` / `known not to apply`):**
   - Zero `Subtyper` `(Subtype)` casts appeared across all `4,715` / `4,663` `zerocopy` crate functions (`0` incidence in current census), though any future generic/function-item function in `zerocopy` or another crate coercing higher-ranked function pointers (`for<'a> fn(&'a T) -> fn(&'b T)`) would emit `CastKind::Subtype` at `Runtime(Initial)` (`not examined` outside tested specimens and `zerocopy --lib`).
6. **Lean 4 formalization model scope:**
   - The `5,620`-line Lean 4 mechanization models direct vs. stack-allocated scalars/pointers, `AllocId` liveness, move deinitialization (`deinitMovedPlace`), `SwitchInt`, `Assume`, `Assert`, `CastKind::Subtype`, and bounded fuel `runBody`. Unwinding (`UnwindAction`), concurrent memory models / Tree Borrows, generic polymorphism, and arbitrary projections beyond frame locals are excluded from the finite operational model (`not examined`).

---

## Evidence

Preserved support artifacts inside `support/`:

| Artifact | Purpose & Key Contents |
| :--- | :--- |
| `support/pin_receipt.json` | Schema `pin-receipt/1` generated `2026-11-21` recording full 40-hex commit SHAs and exact Git blob OIDs resolved live via GitHub GraphQL API for `rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `8144389c895da997dbdecaa635e41d6a50be6ffd`, `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `google/zerocopy` (`907b9175fee081872ec883ca4709e6ad922f8ed0`), and `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`). |
| `support/probe_remove_storage_markers_and_range_switch_passes.py` | Self-contained `803`-line Python runner reproducing the 7-configuration `Miri` single-scope UB matrix, 6-configuration loop cross-iteration alias matrix, `rustc` `RemoveStorageMarkers` MIR dumps, all `18` Part B pass specimens (`SsaRangePropagation`, `SimplifyComparisonIntegral`, `EarlyOtherwiseBranch`, `Subtyper`), native docstring `a=8` check, and `zerocopy --lib` census. |
| `support/probe_results.json` | Complete `969`-line JSON output (`schema: rsm-range-switch-probe/1`, `generated_on: 2026-11-21`) containing scrubbed `stderr`/`stdout`, exact before/after MIR dumps for all specimens, and `zerocopy` census metrics for both `1.98.0-nightly` (`14210df0e2`) and `1.102.0-nightly` (`3ef0c22cd`). |
| `support/StorageMarkersParadoxAndRangeSwitchSoundness.lean` | Standalone `5,620`-line (`272,328`-byte, SHA-256 `21c1847a9cb9a44b8782753fbf09094dd169c13982f143c8111f1ea6cef76897`) Lean `v4.34.1` mechanization with `0` imports. |
| `support/StorageMarkersAudit.lean` | Kernel and axiom auditor (`84` lines) verifying every constant in `StorageMarkersParadoxAndRangeSwitchSoundness`, forbidding non-`safe` defs, `_unsafe_rec` helpers, axioms/opaques, and printing `#print axioms` on `19` core theorems. |
| `support/check_lean.py` | Reproducible Python checker (`207` lines) scanning whole-word forbidden tokens (including comments), compiling `.olean`, running `StorageMarkersAudit.lean`, and emitting `lean_check_receipt.json`. |
| `support/lean_check_receipt.json` | Machine-generated verification receipt (`schema: lean-check-receipt/1`, `generated_on: 2026-11-22`, `passed: true`, `compile.exit_code: 0`, `compile.errors: 0`, `compile.warnings: 0`, `wall_seconds: 28.344`, `peak_rss_kb: 878508`, `olean_bytes: 13055776`, `audit.summary`: `1323` constants, `592` theorems, `441` axiom-free, `616` definitions, `violations: 0`, `axioms_used: ["propext", "Quot.sound"]`, all `13` `forbidden_token_counts: 0`). |

Key immutable upstream Git source coordinates (`rust-lang/rust`, `joshlf/anneal`):
- `rust-lang/rust` `@ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`):
  - `compiler/rustc_mir_transform/src/remove_storage_markers.rs` (`27` lines, lines `11-26`)
  - `compiler/rustc_session/src/session.rs` (`1,983` lines, `emit_lifetime_markers` lines `883-894`)
  - `src/tools/miri/src/lib.rs` (`218` lines, `MIRI_DEFAULT_ARGS` lines `200-218`)
  - `compiler/rustc_const_eval/src/interpret/stack.rs` (`743` lines, lines `13, 193, 203, 495-509, 575-625`)
  - `compiler/rustc_mir_transform/src/ssa_range_prop.rs` (`212` lines, docstring `1-10`, impl `25-212`)
  - `compiler/rustc_mir_transform/src/simplify_comparison_integral.rs` (`218` lines, lines `14-218`)
  - `compiler/rustc_mir_transform/src/early_otherwise_branch.rs` (`421` lines, lines `11-421`)
  - `compiler/rustc_mir_transform/src/unreachable_enum_branching.rs` (`173` lines, lines `80-173`)
  - `compiler/rustc_mir_transform/src/add_subtyping_projections.rs` (`73` lines, lines `1-73`)
  - `compiler/rustc_mir_transform/src/ssa.rs` (`455` lines, lines `1-85`)
  - `compiler/rustc_mir_transform/src/lib.rs` (`855` lines, pipeline slots lines `662, 728, 734, 759, 765, 766`)
- `rust-lang/rust` `@ 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `2026-05-31`, `miri 0.1.0`, LLVM `22.1.6`):
  - `compiler/rustc_mir_transform/src/remove_storage_markers.rs` (`29` lines)
  - `compiler/rustc_session/src/session.rs` (`1,482` lines, lines `547-556`)
  - `src/tools/miri/src/lib.rs` (`200` lines, lines `183-200`)
  - `compiler/rustc_mir_transform/src/ssa_range_prop.rs` (`215` lines, lines `158-171`)
  - `compiler/rustc_mir_transform/src/simplify_comparison_integral.rs` (`253` lines, lines `81-147, 184-193`)
  - `compiler/rustc_mir_transform/src/early_otherwise_branch.rs` (`401` lines)
  - `compiler/rustc_mir_transform/src/add_subtyping_projections.rs` (`71` lines)
  - `compiler/rustc_mir_transform/src/lib.rs` (lines `633, 714, 720, 745, 751, 752`)
- `joshlf/anneal` `@ c131b320eeeb26ef692e5afd5ec8db49ee518613`:
  - `trusted/lean/Trusted/MirAst.lean` (lines `53, 544-546, 612-618, 638-652`)
  - `trusted/lean/Trusted/MirSemantics.lean` (lines `67-70, 664-702, 921-947, 1344-1369`)
  - `trusted/correspondence/Trusted/Correspondence.lean` (line `1317`)
  - `trusted/rustc-capture/src/driver.rs` (line `25`)

Probe evidence was generated on `2026-11-21` (`support/probe_results.json`); Lean 4 formalization re-verification and kernel axiom auditing completed on `2026-11-22` (`support/lean_check_receipt.json`).

---

## Revalidation

To revalidate the compiler/Miri findings against a newer `rustc` or `miri` toolchain or a newer `zerocopy` revision, run the standalone empirical probe from inside this package directory (or pass `--zerocopy-dir <path-to-zerocopy>` for the crate census):

```bash
python3 support/probe_remove_storage_markers_and_range_switch_passes.py \
  --zerocopy-dir <path/to/zerocopy/zerocopy> \
  --out /tmp/probe_recheck.json
```

Quick manual checks against a target `rust-lang/rust` commit `<REV>`:
1. **Check `RemoveStorageMarkers` gating:** Inspect `compiler/rustc_mir_transform/src/remove_storage_markers.rs` and `compiler/rustc_session/src/session.rs` (`emit_lifetime_markers`) for whether `mir_preserve_ub` or `AlwaysEmitLifetimes` is now checked, or test `MIRIFLAGS="-Zmir-opt-level=2 -Copt-level=0 -Zmir-preserve-ub=yes" cargo miri run --bin single_scope` from the probe script: `rc == 0` proves the paradox still holds, `rc == 1` proves it was fixed.
2. **Check `SsaRangePropagation`, `SimplifyComparisonIntegral`, `EarlyOtherwiseBranch`, and `Subtyper`:** Inspect the five `run_part_b` assertion blocks in `probe_remove_storage_markers_and_range_switch_passes.py`: any assertion change immediately isolates behavioral drift in singleton range propagation (`14` vs `15` arms, multi-pred join), comparison `Move -> Copy` rewriting, 2-variant vs 3-variant `EarlyOtherwiseBranch` triggering after `UnreachableEnumBranching`, or `Subtyper` `(Subtype)` insertion.
3. **Re-verify the Lean 4 kernel proof and axiom audit:**

```bash
LEAN_SYSROOT="$(lean --print-prefix)" \
python3 support/check_lean.py \
  --lean "$(which lean)" \
  --out /tmp/lean_recheck.json
```

Confirm `"passed": true`, `"errors": 0`, `"warnings": 0`, `"violations": 0`, and all `forbidden_token_counts` equal to `0`. Finally, validate the corpus package structure from the corpus root with `python3 tools/reference.py check`.
