# `rustc` MIR Branch & Constant Simplification Passes and Inliner Cost Model (`MatchBranchSimplification`, `SimplifyConstCondition`, `SingleUseConsts`, and `CostChecker`)

## Summary

Four `rustc_mir_transform` components govern constant propagation, branch collapse, and inlining profitability inside `rustc`'s `Runtime(PostCleanup) -> Runtime(Optimized)` MIR pipeline (`rust-lang/rust@137d1d49458b73b7b85d2c1599d8730886d65e47` and executed `rustc 1.98.0-nightly` at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):

1. **`SingleUseConsts` (`single_use_consts.rs`, `PassPolicy::optional(ctx.mir_opt_level() >= 1)`):** Eliminates non-argument, non-return locals initialized once by `Rvalue::Use(Operand::Constant(_), _)` and read at most once, rewriting `VarDebugInfoContents::Place` entries to `VarDebugInfoContents::Const`. Because `SingleUseConstsFinder` explicitly ignores `StatementKind::StorageLive` and `StatementKind::StorageDead` (`line 146`), performs no CFG dominance check between `init_loc` and `use_loc`, and never inspects `-Zmir-preserve-ub`, the pass **erases live `DeadLocal` UB and non-dominating uninitialized-memory UB even when `-Zmir-preserve-ub=yes` is set**. In live Miri execution on `rustc 1.98.0-nightly`, both `StorageLive(x); x = 77; StorageDead(x); RET = x` and a non-dominating conditional init flip from `rc=1` (UB detected) to `rc=0` (`DEAD_LOCAL=77` and `NONDOM=88`) under `-Zmir-opt-level=1 -Zmir-preserve-ub=yes` and silently—without Miri's optimization warning—under `-Zmir-opt-level=0 -Zmir-preserve-ub=yes -Zmir-enable-passes=+SingleUseConsts`. This directly collides with Anneal's trusted MIR specification (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted/MirSemantics.lean:2221-2242`), whose negative UB canary `progStorageDeadReadUb` (`CanaryNegativeUbStorageDeadReadAnnealClaim`) has the exact shape erased by `SingleUseConsts`.
2. **`MatchBranchSimplification` (`match_branches.rs`, `PassPolicy::optional(ctx.mir_opt_level() >= 2)`):** Collapses multi-arm `SwitchInt` diamonds into straight-line MIR via five ordered unification arms: `identical_stmts`, `unify_if_equal_const` (forcing `WithRetag::No`), `unify_by_eq_op` (`Eq`/`Ne` erasing unreachable `otherwise`), `unify_by_int_to_int` (signed/unsigned `can_cast` bit truncation), and `unify_by_copy` (enum-clone reconstruction gated on `index == 0`, `dest.is_stable_offset()`, `otherwise.is_none()`, and—added between `14210df0e` and `137d1d4945`—a `borrowed_locals` non-aliasing guard). Only `unify_by_eq_op` and `unify_by_int_to_int` allocate `self.discr_local`; `identical_stmts` and `unify_if_equal_const` leave `self.discr_local == None`, so `simplify_match` (`lines 450-459` at `137d1d4945`, `lines 435-444` at `14210df0e`) drops `Operand::Copy(*null_ptr)` without emitting `StatementKind::PlaceMention`. On pure surface Rust `unsafe { match *p { 0 => 99, _ => 99 } }` with `p = null()`, Miri flips from `rc=1` (1-byte null dereference UB) to `rc=0` (`MBS_NULL=99`) under `-Zmir-opt-level=2 -Zmir-preserve-ub=yes` and silently under `-Zmir-opt-level=0 -Zmir-preserve-ub=yes -Zmir-enable-passes=+MatchBranchSimplification`.
3. **`SimplifyConstCondition` (`simplify_branches.rs`, `PassPolicy::optional(true)`, scheduled under `WithMinOptLevel(1, ...)` three times: `AfterInstSimplify`, `AfterConstProp`, and `Final`):** Tracks a strictly immediate-predecessor constant binding `pre_place_const` (invalidated by `.take()` on every statement), folds `SwitchInt` on constant discriminants to `Goto`, folds `Assert` to `Goto` **only when `constant == expected`** (never folding failing asserts to `Unreachable`, which would unsoundly refine a deterministic panic into UB), folds `Assume(true)` to `Nop`, and patches `Assume(false)` to `TerminatorKind::Unreachable`. Because `MirPatch::apply` (`patch.rs:323-325` at `137d1d4945`, `patch.rs:303-305` at `14210df0e`) executes `bb.statements.clear()` whenever a terminator is patched to `Unreachable`, `Assume(false)` wipes all preceding statements in the basic block—preserving UB refinement and weak UB equivalence (assuming MIR statements cannot panic or diverge) while shifting Miri's diagnostic from an earlier 4-byte null-pointer dereference to `entering unreachable code`.
4. **Documentation-vs.-Implementation Discrepancy on `-Zmir-preserve-ub`:** `compiler/rustc_session/src/options.rs:2787-2789` documents `-Zmir-preserve-ub` as `"implies -Zmir-opt-level=0"`, yet `Session::mir_opt_level` (`compiler/rustc_session/src/session.rs:988-990`) never reads `mir_preserve_ub`. Across all of `rustc_mir_transform`, only `RemovePlaceMention` (`remove_place_mention.rs:13`) and `CfgSimplifier` (`simplify.rs:132-133, 320-326`) consult `mir_preserve_ub`; passing `-Zmir-preserve-ub=yes` alone to `rustc` leaves `mir_opt_level() == 1` (at `-Copt-level=0`) or `2` (at `-Copt-level>=1`), running `SingleUseConsts` and `SimplifyConstCondition` (and `MatchBranchSimplification` at `-O`). Miri avoids this by passing both `-Zmir-preserve-ub` and `-Zmir-opt-level=0` in `MIRI_DEFAULT_ARGS` (`rust-lang/miri@f667c131a9a3c88f1b0d64b1abe2f5ac256043de`, `src/lib.rs:200-205`).
5. **`CostChecker` (`cost_checker.rs` + `inline.rs` + `jump_threading.rs`):** Evaluates MIR inlining and jump-threading cost via saturating subtraction `penalty.saturating_sub(bonus)` with fixed weights (`INSTR_COST=5`, `CALL_PENALTY=25`, `LANDINGPAD_PENALTY=50`, `RESUME_PENALTY=45`, `LARGE_SWITCH_PENALTY=20`, `CONST_SWITCH_BONUS=10`), a function-level `+25` single-call bonus when `count(is_call_like) == 1` (producing a `+50` jump between 1 and 2 calls on equal bodies), intrinsic exemption (`INSTR_COST=5` vs `CALL_PENALTY=25`, yet still counted as `is_call_like == true`), `+25` bonus for `Operand::RuntimeChecks(UbChecks)` when `!inline_mir_preserve_debug.unwrap_or(ub_checks)`, and `5` vs `25` (`+20` delta) on optional overflow-check `Assert`s. All live `rustc` threshold cliffs (`110`, `115`, `155`, `+25` for `UbChecks`, `+80` for 4 overflow asserts) match the closed-form cost algebra with 0-unit error.
6. **Constructive Lean 4 Mechanization (`support/MatchBranchesSingleUseConstsAndCostCheckerSoundness.lean`, 2,412 LOC, 95 theorems):** Kernel-checked under Lean `v4.34.1` (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) using only `[propext]` (`0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`), formalizing all UB-erasure counterexamples, repaired bidirectional soundness (`singleUseConsts_repaired_sound_iff`, `mbs_identical_with_placemention_exact`), all 5 `MatchBranchSimplification` arms including `can_cast` and aliasing guards, `SimplifyConstCondition` + `MirPatch::apply` refinement and trust boundaries, and `CostChecker` monotonicity plus call-site non-amplification (`(c - 1) + k <= c <-> k <= 1`).

## Applicability

### Subject Relationships and Scope

This report combines primary-source audit, live compiler/interpreter execution, normative specification cross-checking, and constructive Lean 4 mechanization across six durable subjects recorded in `REPORT.json`:

| Subject | Exact Revision / Version | Role in This Report |
| :--- | :--- | :--- |
| `rust-lang/rust` (upstream HEAD) | `137d1d49458b73b7b85d2c1599d8730886d65e47` | Primary source for `match_branches.rs`, `simplify_branches.rs`, `single_use_consts.rs`, `cost_checker.rs`, `inline.rs`, `cross_crate_inline.rs`, `jump_threading.rs`, `patch.rs`, `unreachable_prop.rs`, `remove_place_mention.rs`, `remove_storage_markers.rs`, `simplify.rs`, `strip_debuginfo.rs`, `lower_intrinsics.rs`, `pass_manager.rs`, `lib.rs`, `options.rs`, `session.rs`, and `rustc_middle/src/mir/{mod,statement,terminator}.rs`. |
| `rust-lang/rust` (executed toolchain) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `x86_64-unknown-linux-gnu`) | Live differential execution of `rustc` MIR dumps and `miri` UB detection via `support/probe_match_branches_simplify_single_use_consts_and_cost.py`, plus full line-by-line source diff against HEAD. |
| `rust-lang/miri` (upstream HEAD) | `f667c131a9a3c88f1b0d64b1abe2f5ac256043de` | Source audit of `MIRI_DEFAULT_ARGS` (`src/lib.rs:200-217`) and the `mir_opt_level() > 0` optimization warning (`src/bin/miri.rs:176-188`). |
| `rust-lang/reference` (upstream HEAD) | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative Rust UB rules (`src/behavior-considered-undefined.md`: `r[undefined.pointer-access]`, `r[undefined.dangling]`, `r[undefined.validity.scalar]`, `r[undefined.validity.undef]`, `r[undefined.intrinsic]`). |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Trusted-boundary alignment (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean` `evalOperandToSlot` / `deinitMovedPlace = true` / `progStorageDeadReadUb`, `trusted/rustc-capture/src/driver.rs`). |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Independent kernel verification of `support/MatchBranchesSingleUseConstsAndCostCheckerSoundness.lean`. |

### Exact Cross-Revision Deltas Between Executed `14210df0e` and Upstream HEAD `137d1d4945`

Because live execution ran on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` while upstream HEAD is `137d1d49458b73b7b85d2c1599d8730886d65e47`, every file in `rustc_mir_transform` relevant to this report was diffed verbatim between the two commits (`Basis: source`):

| Component | Behavior Shared Across `14210df0e` and `137d1d4945` | Concrete Difference at `137d1d4945` vs. `14210df0e` |
| :--- | :--- | :--- |
| **Pass gating API** | Default opt-level gates (`SingleUseConsts >= 1`, `MatchBranchSimplification >= 2`, `SimplifyConstCondition` wrapped in `o1(...)`, `Inline` off at `0|1`, on at `2` when `-Copt-level>=2` and non-incremental). None of the three simplification passes checks `mir_preserve_ub`. | `137d1d4945` replaced `MirPass::is_enabled(&self, sess)` + `is_required(&self)` with `MirPass::policy(&self, ctx: &PassCtx<'_>) -> PassPolicy` (`pass_manager.rs:88-107, 132-165`), honoring per-function `#[optimize(...)]` via `PassCtx::mir_opt_level()`. |
| **`SingleUseConsts` (`single_use_consts.rs`, 206 LOC at HEAD)** | Identical algorithm, visitor (`StorageLive`/`StorageDead` ignored at `line 146`), lack of dominance check, lack of `mir_preserve_ub` check, and `VarDebugInfoContents::Place -> Const` rewrite (`lines 67-71, 190-204`). | Only imports (`rustc_span::bug`) and `policy` trait method changed. All live Miri UB-erasure results on `14210df0e` apply verbatim to `137d1d4945` (`derived` from identical `run_pass`/`SingleUseConstsFinder`/`LocalReplacer`). |
| **`MatchBranchSimplification` (`match_branches.rs`, 565 LOC at HEAD vs. 550 LOC at `14210df0e`)** | Same 5 unification arms, same `can_cast` logic, same `remove_successors_from_switch` single-target shortcut, and **same missing `PlaceMention` / `discr_local` emission** when `identical_stmts` or `unify_if_equal_const` succeeds (`lines 450-459` at HEAD vs. `lines 435-444` at `14210df0e`). | Two semantic improvements at `137d1d4945`: (1) `unify_if_equal_const` (`lines 68-71`) switched from `try_eval_scalar_int` to `const_.eval(...)`, unifying equal non-scalar constants as well; (2) `unify_by_copy` (`lines 264-276`) added a lazy `borrowed_locals` check (when `copy_src_place.is_indirect()`, reject if `dest.local` is borrowed) and `copy_src_place.local == dest.local` rejection to prevent overlapping copies. |
| **`SimplifyConstCondition` (`simplify_branches.rs`, 99 LOC) & `MirPatch::apply` (`patch.rs`, 366 LOC)** | Identical immediate-predecessor `pre_place_const.take()` logic, `SwitchInt`/`Assert` (`constant == expected` only), `Assume(true) -> nop`, `Assume(false) -> Unreachable`, and `MirPatch::apply` `bb.statements.clear()` on `TerminatorKind::Unreachable`. | `patch.rs` refactored statement insertion merging into `merge(...)` (`lines 292-316, 343-366`), shifting `if let TerminatorKind::Unreachable = patch { bb.statements.clear(); }` from `patch.rs:303-305` (`14210df0e`) to `patch.rs:323-325` (`137d1d4945`). |
| **`CostChecker` (`cost_checker.rs`, 205 LOC at HEAD vs. 200 LOC at `14210df0e`)** | Identical constants (`5, 25, 50, 45, 20, 10`), `saturating_sub`, `add_function_level_costs` single-call `+25` bonus, `is_call_like` partition, intrinsic `INSTR_COST=5` exemption, `RuntimeChecks::UbChecks` `+25` bonus, and optional overflow-check `5` vs `25` gating. | `137d1d4945` added `cost_checker.rs:92-96`: `StatementKind::Assign((_, Rvalue::Use(Operand::Constant(ref constant), _))) if matches!(constant.const_, Const::Val(ConstValue::ZeroSized, _)) => {}` (zero cost for ZST constant assignments, which previously incurred `INSTR_COST=5` at `14210df0e`). |

### Invocation Modes and Pipeline Placement

All four components operate exclusively during `run_optimization_passes` (`compiler/rustc_mir_transform/src/lib.rs:700-789`), which transitions a MIR body from `MirPhase::Runtime(RuntimePhase::PostCleanup)` to `MirPhase::Runtime(RuntimePhase::Optimized)`. Exact relative scheduling at `137d1d4945`:

1. `CheckAlignment`, `CheckNull`, `CheckEnums` (`lib.rs:711-713`)
2. `LowerSliceLenCalls`, `InstSimplify::BeforeInline` (`lib.rs:718-721`)
3. **`ForceInline`** (`PassPolicy::Required`, `lib.rs:723`) -> **`Inline`** (`CostChecker` caller, `lib.rs:725`)
4. `RemoveStorageMarkers`, `RemoveZsts`, `RemoveUnneededDrops`, `UnreachableEnumBranching`, `UnreachablePropagation`, `o1(SimplifyCfg::AfterUnreachableEnumBranching)`, `MultipleReturnTerminators`, `InstSimplify::AfterSimplifyCfg` (`lib.rs:730-743`)
5. **`o1(SimplifyConstCondition::AfterInstSimplify)`** (`lib.rs:752`)
6. `ReferencePropagation`, `ScalarReplacementOfAggregates`, `SimplifyLocals::BeforeConstProp`, `DeadStoreElimination::Initial`, `GVN`, `SimplifyLocals::AfterGVN`, `SsaRangePropagation` (`lib.rs:753-761`)
7. **`MatchBranchSimplification`** (`lib.rs:762`)
8. `DataflowConstProp` (`lib.rs:763`)
9. **`SingleUseConsts`** (`lib.rs:764`)
10. **`o1(SimplifyConstCondition::AfterConstProp)`** (`lib.rs:765`)
11. `JumpThreading` (second `CostChecker` caller, `lib.rs:766`), `EarlyOtherwiseBranch`, `SimplifyComparisonIntegral` (`lib.rs:767-768`)
12. **`o1(SimplifyConstCondition::Final)`** (`lib.rs:769`)

Note that `RemovePlaceMention` runs earlier during `run_runtime_cleanup_passes` (`lib.rs:684-691`, producing `Runtime(PostCleanup)`), gated on `!ctx.opts.unstable_opts.mir_preserve_ub` (`remove_place_mention.rs:13`). Verification frameworks (including Anneal) that capture MIR before `run_optimization_passes` (at or before `Runtime(PostCleanup)`) avoid all UB-erasing rewrites analyzed below; any consumer operating on `optimized_mir`—or invoking Miri with `-Zmir-opt-level >= 1` or explicit `-Zmir-enable-passes`—is directly exposed.

## Findings

### 1. The `-Zmir-preserve-ub` Option Contract vs. `rustc` / `Miri` Reality

**Basis:** `source + execution + documentation`

A foundational premise when auditing MIR optimization passes for UB preservation is what `-Zmir-preserve-ub=yes` actually enforces. Direct inspection of `rust-lang/rust@137d1d49458b73b7b85d2c1599d8730886d65e47` uncovers a concrete divergence between the option's documented help string and its implementation:

- **Documented behavior (`compiler/rustc_session/src/options.rs:2787-2789`):**
  ```rust
  mir_preserve_ub: bool = (false, parse_bool, [TRACKED],
      "keep place mention statements and reads in trivial SwitchInt terminators, which are interpreted \
      e.g., by miri; implies -Zmir-opt-level=0 (default: no)"),
  ```
- **Actual implementation (`compiler/rustc_session/src/session.rs:988-990` and `compiler/rustc_session/src/config.rs:120-128`):**
  ```rust
  pub fn mir_opt_level(&self) -> usize {
      self.opts.unstable_opts.mir_opt_level.unwrap_or_else(|| self.opts.optimize.mir_opt_level())
  }
  ```
  where `OptLevel::mir_opt_level()` returns `1` for `OptLevel::No` and `2` for all optimized levels. Searching the entire `rust-lang/rust` repository for `mir_preserve_ub` finds **zero** code in `rustc_session` or `rustc_mir_transform::pass_manager` that forces `mir_opt_level` to `0` when `mir_preserve_ub` is `true`, and **no** `PassCtx::should_preserve_ub()` helper exists.
- **Complete inventory of `mir_preserve_ub` readers in `rustc_mir_transform` (`137d1d4945`):**
  1. `RemovePlaceMention::policy` (`compiler/rustc_mir_transform/src/remove_place_mention.rs:12-14`): `PassPolicy::optional(!ctx.opts.unstable_opts.mir_preserve_ub)`.
  2. `CfgSimplifier::new` / `simplify_branch` (`compiler/rustc_mir_transform/src/simplify.rs:132-133, 320-326`): sets `preserve_switch_reads = matches!(body.phase, MirPhase::Built | MirPhase::Analysis(_)) || tcx.sess.opts.unstable_opts.mir_preserve_ub` to prevent collapsing trivial `SwitchInt` terminators whose targets are all identical.
- **Empirical confirmation (`support/probe_results.json`, `single_use_consts.mir_preserve_ub_alone_does_not_imply_opt_0`):** Compiling `dead_local_const` with `rustc --edition=2021 --crate-type=lib -Zmir-preserve-ub=yes` (without `-Zmir-opt-level=0`) executes `SingleUseConsts` and all three `SimplifyConstCondition` instances, collapsing the dead-local read into:
  ```text
  fn dead_local_const() -> u32 {
      let mut _0: u32;
      bb0: {
          _0 = const 77_u32;
          return;
      }
  }
  ```
- **Miri's mitigation and blind spot (`rust-lang/miri@f667c131a9a3c88f1b0d64b1abe2f5ac256043de`):** Miri protects default executions by passing **both** `-Zmir-preserve-ub` and `-Zmir-opt-level=0` in `MIRI_DEFAULT_ARGS` (`src/lib.rs:200-217`, along with `-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums,-ReferencePropagation,-GVN`). However, Miri's diagnostic warning (`src/bin/miri.rs:181-188`) is gated solely on `if tcx.sess.mir_opt_level() > 0`. Consequently, passing `-Zmir-opt-level=0 -Zmir-preserve-ub=yes -Zmir-enable-passes=+SingleUseConsts` or `+MatchBranchSimplification` causes live UB erasure in Miri with **`has_miri_opt_warning: false`** (verified empirically across Probes 1A, 1B, and 2A).

### 2. `SingleUseConsts` (`single_use_consts.rs`): Syntactic Eligibility, Live UB Erasure, Repaired Soundness, and `VarDebugInfo` Rewriting

**Basis:** `normative + source + execution + derived` (plus Lean mechanization)

#### 2.1 Exact Pass Algorithm and Eligibility Rules

In `compiler/rustc_mir_transform/src/single_use_consts.rs` (`lines 25-206`, identical in logic between `14210df0e` and `137d1d4945`), `SingleUseConsts` runs at `mir_opt_level() >= 1` (`line 29`)—meaning it is enabled **by default even in unoptimized `-Copt-level=0` debug builds** (`OptLevel::No.mir_opt_level() == 1`).

1. **Ineligible local initialization (`lines 39`):**
   ```rust
   finder.ineligible_locals.insert_range(..Local::arg(body.arg_count));
   ```
   Since `Local::arg(i)` is `Local::from_usize(i + 1)` (`compiler/rustc_middle/src/mir/mod.rs:874-876`), the half-open range `..Local::arg(body.arg_count)` marks `_0` (`RETURN_PLACE`) and every argument `_1..=body.arg_count` ineligible.
2. **Syntactic single-pass cardinality scan (`SingleUseConstsFinder`, `lines 105-166`):**
   - `visit_assign` (`lines 112-126`): If `place.as_local()` is `Some(local)` and `rvalue` is `Rvalue::Use(Operand::Constant(_), _)`, records `locations[local].init_loc = Some(location)` (or marks `local` ineligible on a second constant assignment). Any other assignment falls through to `super_assign` -> `visit_local`, marking `local` ineligible.
   - `visit_operand` (`lines 128-141`): If `operand.place()` is `Some(place)` and `place.as_local()` is `Some(local)` (covering both `Operand::Copy` and `Operand::Move` with empty projection), records `locations[local].use_loc = Some(location)` (or marks `local` ineligible on a second use). Projected places (`place.as_local() == None`) fall through to `super_operand` -> `visit_local`, marking `local` ineligible.
   - `visit_statement` (`lines 143-149`):
     ```rust
     fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
         match &statement.kind {
             // Storage markers are irrelevant to this.
             StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
             _ => self.super_statement(statement, location),
         }
     }
     ```
   - `visit_var_debug_info` (`lines 151-159`): Records `locals_in_debug_info.insert(local)` for `VarDebugInfoContents::Place(place)` with empty projection, rather than marking `local` ineligible.
   - `visit_local` (`lines 161-165`): Any other mention of `local` (address-taken `&local`, `PlaceMention(local)`, `SetDiscriminant`, projected reads/writes, call destinations) marks `local` ineligible.
3. **Mutation and debug-info rewriting (`lines 43-90, 168-205`):**
   - For every eligible local with `Some(init_loc)`:
     - Replaces the statement at `init_loc` with `StatementKind::Nop` (`lines 54-57`), stealing the `Operand::Constant(_)`.
     - If `locals_in_debug_info.contains(local)`, rewrites every matching `VarDebugInfoContents::Place(local)` in `body.var_debug_info` to `VarDebugInfoContents::Const(const_op)` (`lines 67-71, 190-204`).
     - If `locations.use_loc` is `None` (**never-used constant**), `continue` leaves the assignment as `Nop` and retains the rewritten constant debuginfo (`line 73`).
     - Otherwise, `LocalReplacer::visit_operand` replaces the single `Operand::Copy(local)` or `Operand::Move(local)` at `use_loc` with the stolen `Operand::Constant` (`lines 75-86, 179-188`).
   - Calls `drop_invalid_debuginfos(body)` (`line 89`, defined in `strip_debuginfo.rs:42-50`), which prunes per-statement `stmt.debuginfos` referencing locals no longer present in `body.var_debug_info` as `Place`s.

#### 2.2 Three Structural Omissions Causing UB Erasure (and Empirical Reproduction)

`SingleUseConsts` omits three semantic checks required for UB preservation:

1. **Ignoring `StorageLive`/`StorageDead` (`line 146`):** Allows `StorageLive(x); x = const 77; StorageDead(x); RET = x` (or `StorageLive(x); x = const 55; StorageDead(x); StorageLive(x); RET = x`) to rewrite `RET = x` into `RET = const 77` (or `const 55`), erasing a `DeadLocal` or fresh-`StorageLive` uninitialized-memory UB. Similarly, if `x` is already dead at `init_loc`, replacing `x = const c` with `Nop` erases the dead-local store UB.
2. **Omitting CFG dominance (`init_loc` dominates `use_loc`):** A local initialized in only one branch of a diamond (`bb0: StorageLive(x); switchInt(take_init) -> [true: bb_init, _: bb_use]`, `bb_init: x = 88; goto bb_use`, `bb_use: RET = x`) has `initCount == 1` and `useCount == 1`. On `take_init == false`, reading `x` at `bb_use` violates `r[undefined.validity.scalar]` / `r[undefined.validity.undef]` (reading uninitialized memory for `u32`). `SingleUseConsts` propagates `const 88_u32` directly into `bb_use`, making the UB path return `88`.
3. **Omitting `-Zmir-preserve-ub` gating (`line 29`):** Unlike `RemovePlaceMention` and `CfgSimplifier`, `SingleUseConsts` checks only `ctx.mir_opt_level() >= 1`.

**Live `rustc 1.98.0-nightly` + Miri results (`support/probe_results.json`):**

| Probe Case | `-Zmir-opt-level=0 -Zmir-preserve-ub=yes` | `-Zmir-opt-level=1 -Zmir-preserve-ub=yes` | `-Zmir-opt-level=0 -Zmir-preserve-ub=yes -Zmir-enable-passes=+SingleUseConsts` |
| :--- | :--- | :--- | :--- |
| **`DeadLocal` (`dead_local_const`)** | `rc=1`: `error: Undefined Behavior: accessing a dead local variable` | `rc=0`, stdout `DEAD_LOCAL=77` (Miri opt warning emitted) | `rc=0`, stdout `DEAD_LOCAL=77` (**no Miri warning**) |
| **Non-dominating uninit (`nondom_uninit_const(false)`)** | `rc=1`: `error: Undefined Behavior: constructing invalid value of type u32: encountered uninitialized memory, but expected an integer` | `rc=0`, stdout `NONDOM=88` (Miri opt warning emitted) | `rc=0`, stdout `NONDOM=88` (**no Miri warning**) |
| **`VarDebugInfo` + zero-use (`suc_debug`, `-Cdebuginfo=2`)** | Before: `debug single => _2; debug _unused => _3; _5 = copy _2;` | — | After: `debug single => const 42_u32; debug _unused => const 99_u32; _5 = const 42_u32;` (`2` `nop;` statements) |

#### 2.3 Direct Collision with Anneal's Trusted Boundary (`joshlf/anneal@c131b320e`)

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
- `trusted/lean/Trusted/MirSemantics.lean:2221-2242` defines the negative UB canary `progStorageDeadReadUb`:
  ```lean
  -- StorageLive(_1); _1 = const 7u32; StorageDead(_1); _0 = copy _1; return
  noncomputable def CanaryNegativeUbStorageDeadReadAnnealClaim : Prop :=
    NegativeCanaryClaim progStorageDeadReadUb queryEmpty .undefined .unsupported
  ```
  Running `SingleUseConsts` prior to MIR capture rewrites `progStorageDeadReadUb` into `StorageLive(_1); nop; StorageDead(_1); _0 = const 7u32; return`, erasing the exact `.fault .undefined` behavior pinned by Anneal's TCB canary.
- Furthermore, `trusted/lean/Trusted/MirSemantics.lean:949-976` (`evalOperandToSlot`) implements conservative `deinitMovedPlace = true` semantics (evaluating `.move place` transitions non-ZST locals to `liveUninitSlot ty`). Consequently, even in a single-use setting, a verified MIR optimizer targeting Anneal semantics must also treat any intervening `Move` on the candidate local (if generalized beyond single-use) as killing initialization, and must never elide `StorageDead` checks when UB preservation is required.

#### 2.4 Mechanized Counterexamples vs. Repaired Bidirectional Soundness (`Lean v4.34.1`)

In `support/MatchBranchesSingleUseConstsAndCostCheckerSoundness.lean` (Part 2, lines 256-1046):
- **Refinement vs. UB Preservation Separation:** `singleUseConsts_deadLocal_erases_ub` (`line 544`), `singleUseConsts_nonDominating_erases_ub` (`line 587`), and `singleUseConsts_storageReset_erases_ub` (`line 618`) prove `¬ UbEquivalent` on exact models of all three counterexamples, while `singleUseConsts_deadLocal_still_refines` (`line 551`) proves standard UB refinement `Refines` still holds—explaining formally why `rustc` treats `SingleUseConsts` as a valid optimizing pass for native codegen (`-Zmir-preserve-ub=no`) yet unsound for UB-preserving interpreters/verifiers.
- **Repaired Bidirectional Soundness (`singleUseConsts_repaired_exact`, `line 888`; `singleUseConsts_repaired_sound_iff`, `line 995`):** Under five explicit preconditions on a dominating execution segment `pre ++ [x := const c] ++ mid ++ [dest := copy/move x] ++ post`:
  1. `x ≠ 0` (not return place),
  2. `dest ≠ x`,
  3. `hLiveAtInit`: whenever `pre` completes cleanly to `ePre`, `ePre x ≠ .dead` (no dead-store UB erased),
  4. `hMidDisj`: `mid` is completely disjoint from `x` (no `StorageLive x`, `StorageDead x`, write to `x`, or `move x`),
  5. `hPostDisj`: `post` is disjoint from `x` (no later read/write of `x`),
  the pass satisfies **exact outcome equality** (`ExactEq`) and full bidirectional equivalence:
  `(∀ v, eval orig = .ok v ↔ eval opt = .ok v) ∧ (∀ k, eval orig = .ub k ↔ eval opt = .ub k)`.
- **`VarDebugInfo` Scoping (`varDebugInfo_matches_when_live_init`, `line 1034`; `varDebugInfo_overextends_when_dead`, `line 1040`):** Replacing `VarDebugInfoContents::Place(x)` with `Const(c)` matches concrete state when `env x = .liveInit c`, but globally extends `some c` to program points where `x` is `.dead` or `.liveUninit` (e.g., before `init_loc` or after `StorageDead(x)`).

### 3. `MatchBranchSimplification` (`match_branches.rs`): Five Unification Arms, Live Indirect-Discriminant `*null_ptr` UB Erasure, and Revision-Specific Aliasing Guards

**Basis:** `normative + source + execution + derived` (plus Lean mechanization)

#### 3.1 Candidate Filtering and Single-Target Shortcut (`match_branches.rs:359-426`)

`MatchBranchSimplification` runs at `ctx.mir_opt_level() >= 2` (`line 20`) and executes `simplify_cfg(tcx, body)` if any switch block was modified (`lines 33-35`). For each basic block `switch_bb`:

1. **`candidate_match` (`lines 359-384`):**
   - Requires `TerminatorKind::SwitchInt { discr: Operand::Copy(_) | Operand::Move(_), targets, .. }`.
   - Rejects self-loops (`targets.all_targets().contains(&switch_bb)`).
   - Requires all targets to be distinct (`targets.is_distinct()`).
   - Filters out empty-unreachable targets (`!bb.is_empty_unreachable()`) and requires all remaining reachable targets to have identical `(bb.statements.len(), &bb.terminator().kind)`.
2. **Single-reachable-target shortcut (`lines 416-426`):**
   - If `(reachable_cases.len(), otherwise.is_none())` is `(1, true)` or `(0, false)`, delegates to `unreachable_prop::remove_successors_from_switch` (`unreachable_prop.rs:62-151`), which records eliminated unreachable branches as `Assume(discr != val)` (or `Assume(discr == val)` for the `(2, true)` single-explicit-target case) and patches the terminator to `Goto`. Notice an important subtlety: when `(0, false)` holds (all explicit cases are unreachable, leaving only `otherwise`), `remove_successors_from_switch` emits `Assume(discr != val)` for each unreachable explicit case—which evaluates `discr.to_copy()`! By contrast, when `reachable_cases.len() >= 1` and `stmt_len` unification runs below, `discr` is evaluated **only** if `self.discr_local` is allocated.

#### 3.2 Complete Audit of the Five Unification Arms (`try_unify_stmts`, `lines 318-355`)

For each statement index `index ∈ 0..stmt_len`, `try_unify_stmts` attempts five unification strategies in strict priority order:

| Priority | Arm & Location (`137d1d4945`) | Eligibility Conditions | Emitted `StatementKind` | Allocates `discr_local`? | Erases Unreachable `otherwise` UB? |
| :--- | :--- | :--- | :--- | :---: | :---: |
| **1** | `identical_stmts` (`lines 555-565`) | All reachable branch statements at `index` are structurally `PartialEq` (`all_equal()`). | `first_stmt.clone()` (retains original `WithRetag`). | **No** | Yes (if `otherwise` was empty-unreachable) |
| **2** | `unify_if_equal_const` (`lines 61-82`) | All reachable statements assign to the same `dest` (`candidate_assign`) via `Rvalue::Use(Operand::Constant(_), _)` (`candidate_const`), and `const_.eval(...)` (`137d1d4945`) / `try_eval_scalar_int` (`14210df0e`) produces identical evaluated values. | `Assign(dest, Rvalue::Use(Operand::Constant(first_const), WithRetag::No))` (`no_retag`). | **No** | Yes (if `otherwise` was empty-unreachable) |
| **3** | `unify_by_eq_op` (`lines 115-148`) | All reachable RHS constants have type `bool`; `first_const` evaluates to `first_bool` and every remaining reachable arm (including `otherwise` if present) evaluates to `!first_bool`. | `Assign(dest, BinaryOp(Eq or Ne, (Copy(discr_local), const first_case)))`. | **Yes** (`line 142`) | **Yes** (when `otherwise.is_none()`, out-of-range discriminant becomes `!first_bool` instead of `unreachable`) |
| **4** | `unify_by_int_to_int` (`lines 187-215`, `466-489`) | `otherwise.is_none()`, `first_const.ty().is_integral()`, and for every `(case, const_)`, `can_cast(tcx, case, discr_layout, const_.ty(), scalar_int)` returns `true`. | `Assign(dest, Use(Copy(discr_local), WithRetag::No))` if same type, else `Cast(IntToInt, Copy(discr_local), target_ty)`. | **Yes** (`line 205`) | **Yes** (requires `otherwise.is_none()`, maps out-of-range discriminant via `IntToInt`) |
| **5** | `unify_by_copy` (`lines 233-315`) | `index == 0`, `dest.is_stable_offset()` (no `Deref`/`Index` projections; `rustc_middle/src/mir/statement.rs:279-290, 383-385`), `otherwise.is_none()`, preceding stmt in `switch_bb` is `discr_place = Rvalue::Discriminant(copy_src_place)` matching `self.discr.place()`, same enum type (not downcast), non-aliasing guard (`137d1d4945` `lines 264-276`), and every arm is `Copy(copy_src_place)` or a fieldless variant constant/aggregate matching `case`. | `Assign(dest, Rvalue::Use(Operand::Copy(copy_src_place), WithRetag::No))`. | **No** (preceding `Discriminant` already accessed `copy_src_place`) | **Yes** (requires `otherwise.is_none()`) |

Key subtle invariants verified from primary source, execution, and Lean proof:

- **Why `unify_if_equal_const` and `unify_by_copy` force `WithRetag::No` (`lines 75-77, 309-313, 526`):** `candidate_const` ignores the `WithRetag` flag of the original `Rvalue::Use`. If branch `0` used `WithRetag::No` and branch `1` used `WithRetag::Yes`, emitting `WithRetag::Yes` could introduce aliasing/retag UB on inputs taking branch `0`. In our live probe (`arm2_equal_const`, `0 => 10_u32, _ => const { 5 + 5 }`), `MatchBranchSimplification` bypasses `identical_stmts` (because one arm is `Const::Unevaluated`) and emits `_0 = no_retag const 10_u32;`. Theorem `mbs_equal_const_retag_yes_unsound` (`line 1234`) proves `WithRetag::Yes` violates `Refines`, while `mbs_equal_const_with_no_retag_refines` (`line 1189`) proves `WithRetag::No` is sound.
- **Exact `can_cast` signed/unsigned truncation semantics (`match_branches.rs:466-489`):**
  ```rust
  let v = match src_layout.ty.kind() {
      ty::Uint(_) => from_scalar.to_uint(src_layout.size),
      ty::Int(_) => from_scalar.to_int(src_layout.size) as u128,
      _ => return false,
  };
  let size = match *cast_ty.kind() {
      ty::Int(t) => Integer::from_int_ty(&tcx, t).size(),
      ty::Uint(t) => Integer::from_uint_ty(&tcx, t).size(),
      _ => return false,
  };
  let v = size.truncate(v);
  let cast_scalar = ScalarInt::try_from_uint(v, size).unwrap();
  cast_scalar == target_scalar
  ```
  Signed discriminants sign-extend through `i128 as u128` before `size.truncate(v)`. On `#[repr(i8)] enum SignedNeg { NegOne = -1, Zero = 0, One = 1 }` mapping `NegOne => 255_u16`, `-1_i8` sign-extends to `0xFFFF_u16` (`65535`), not `255`, so `can_cast` rejects the rewrite (confirmed live in `arm4_int_to_int_fail`: `switchInt` remains untouched; mechanized in `canCast_signed_neg1_i8_to_u16_rejects_255`, `line 1443`). On `#[repr(u8)] enum Tri { A = 1, B = 2, C = 3 }` mapping to `1_i16..3_i16`, `arm4_int_to_int_ok` rewrites the switch to `_0 = copy _3 as i16 (IntToInt);` (mechanized in `mbs_int_to_int_refines`, `line 1391`).
- **Why `137d1d4945` added the `borrowed_locals` aliasing guard in `unify_by_copy` (`lines 264-276`):**
  ```rust
  if copy_src_place.is_indirect() {
      let borrowed_locals = self
          .borrowed_locals
          .get_or_insert_with(|| rustc_mir_dataflow::impls::borrowed_locals(self.body));
      if borrowed_locals.contains(dest.local) {
          return None;
      }
  } else if copy_src_place.local == dest.local {
      return None;
  }
  ```
  In MIR operational semantics, `dest = copy *src_ptr` where `src_ptr` points to `dest` is an overlapping-memory copy (UB), whereas the original unit-variant arm `dest = const Foo::B` never read `*src_ptr`. Without this guard (absent in `14210df0e`), `unify_by_copy` could introduce overlapping-copy UB into defined code (mechanized in `mbs_unify_by_copy_aliasing_hazard`, `line 1517`, contrasting with the sound non-aliasing proof `mbs_unify_by_copy_sound`, `line 1472`).

#### 3.3 Live Indirect-Discriminant `*null_ptr` UB Erasure Under `-Zmir-preserve-ub=yes`

Inspecting `simplify_match` (`match_branches.rs:445-462` at `137d1d4945`; `430-447` at `14210df0e`):

```rust
let discr = discr.clone();

let statement_index = body.basic_blocks[switch_bb].statements.len();
let parent_end = Location { block: switch_bb, statement_index };
let mut patch = simplify_match.patch;
if let Some(discr_local) = simplify_match.discr_local {
    patch.add_statement(parent_end, StatementKind::StorageLive(discr_local));
    patch.add_assign(parent_end, Place::from(discr_local), Rvalue::Use(discr, WithRetag::No));
}
for new_stmt in new_stmts {
    patch.add_statement(parent_end, new_stmt);
}
if let Some(discr_local) = simplify_match.discr_local {
    patch.add_statement(parent_end, StatementKind::StorageDead(discr_local));
}
patch.patch_terminator(switch_bb, body.basic_blocks[first_case_bb].terminator().kind.clone());
patch.apply(body);
```

When every statement in the branches is unified solely by `identical_stmts` or `unify_if_equal_const`, `simplify_match.discr_local` remains `None`. The cloned `discr` is **silently discarded** without emitting either a temporary load or `StatementKind::PlaceMention(place)`.

On pure surface Rust (requiring zero `custom_mir` or unstable features):

```rust
#[inline(never)]
unsafe fn mbs_null_surface(p: *const u8) -> u32 {
    match *p {
        0 => 99_u32,
        _ => 99_u32,
    }
}
```

- **Before `MatchBranchSimplification` (`arm1_identical`):** `bb0: switchInt(copy (*_1)) -> [0: bb2, otherwise: bb1];` where both `bb1` and `bb2` assign `_0 = const 99_u32; goto -> bb3;`.
- **After `MatchBranchSimplification`:** `bb0: { _0 = const 99_u32; return; }` — both `(*_1)` and any `PlaceMention` are completely absent!
- **Live Miri differential execution (`support/probe_results.json`, `match_branch_simplification.indirect_null_discr_ub_erasure`):**
  - `-Zmir-opt-level=0 -Zmir-preserve-ub=yes`: `rc=1` (`error: Undefined Behavior: memory access failed: attempting to access 1 byte, but got null pointer`, violating `r[undefined.pointer-access]` / `r[undefined.dangling]`).
  - `-Zmir-opt-level=2 -Zmir-preserve-ub=yes`: `rc=0`, stdout `MBS_NULL=99` (Miri opt warning emitted).
  - `-Zmir-opt-level=0 -Zmir-preserve-ub=yes -Zmir-enable-passes=+MatchBranchSimplification`: `rc=0`, stdout `MBS_NULL=99` (**no Miri warning**).
- **Mechanized counterexample and repair (`support/MatchBranchesSingleUseConstsAndCostCheckerSoundness.lean`):** `mbs_identical_indirect_null_erases_ub` (`line 1146`) proves `¬ UbEquivalent`, while `mbs_identical_with_placemention_exact` (`line 1170`) proves that emitting `PlaceMention(discr)` when `discr_local == None` restores **exact** semantic equality (`ExactEq`) across all heaps, including null pointers (assuming reachable `otherwise`). By contrast, `mbs_eq_op_preserves_discr_fault` (`line 1262`) proves that `unify_by_eq_op` (and `unify_by_int_to_int`) automatically preserve `*null_ptr` faults because they materialize `discr` into `discr_local`—yet still erase unreachable-`otherwise` UB (`mbs_eq_op_unreachable_otherwise_erases_ub`, `line 1339`).

### 4. `SimplifyConstCondition` (`simplify_branches.rs` + `patch.rs`): Immediate-Predecessor `has_place_const`, `Assert` Asymmetry, and `Assume(false)` Block-Statement Wipe

**Basis:** `normative + source + execution + derived` (plus Lean mechanization)

#### 4.1 Pass Scheduling and the Immediate-Predecessor `has_place_const` Invariant

`SimplifyConstCondition` (`compiler/rustc_mir_transform/src/simplify_branches.rs:1-99`) is registered as three distinct named instances (`AfterInstSimplify`, `AfterConstProp`, and `Final`) inside `run_optimization_passes` (`lib.rs:752, 765, 769`), each wrapped in `WithMinOptLevel(1, ...)`. Its `policy` returns `PassPolicy::optional(true)` (`lines 26-28`), so `WithMinOptLevel::policy` (`pass_manager.rs:224-232`) enables all three instances whenever `ctx.mir_opt_level() >= 1`—again with **no** check on `ctx.opts.unstable_opts.mir_preserve_ub`.

Inside `run_pass` (`lines 30-98`), `try_get_const` (`lines 35-51`) resolves an operand either directly (`Operand::Constant`) or from the **single immediately preceding statement** via `has_place_const`:

```rust
fn try_get_const<'tcx, 'a>(
    operand: &'a Operand<'tcx>,
    has_place_const: Option<(Place<'tcx>, &'a ConstOperand<'tcx>)>,
) -> Option<&'a ConstOperand<'tcx>> {
    match operand {
        Operand::Constant(const_operand) => Some(const_operand),
        // `has_place_const` must be the LHS of the previous statement.
        // Soundness: There is nothing can modify the place, as there are no statements between the two statements.
        Operand::Copy(place) | Operand::Move(place)
            if let Some((place_const, const_operand)) = has_place_const
                && place_const == *place =>
        {
            Some(const_operand)
        }
        Operand::Copy(_) | Operand::Move(_) | Operand::RuntimeChecks(_) => None,
    }
}
```

The per-block loop (`lines 53-75`) enforces this single-statement adjacency strictly by calling `let has_place_const = pre_place_const.take();` at the top of every iteration (`line 57`):
- Only an assignment `StatementKind::Assign((lhs, Rvalue::Use(Operand::Constant(c), _)))` populates `pre_place_const = Some((lhs, c))` (`lines 70-74`).
- **Any** other intervening statement—even an unrelated assignment `_other = const 0`, a `Nop`, a `StorageLive`, or a `StorageDead`—consumes `pre_place_const` via `.take()` and leaves it `None` for the following statement or terminator.
- **Empirical confirmation (`support/probe_results.json`, `simplify_const_condition.immediate_predecessor_has_place_const`):** Running `-Zmir-opt-level=0 -Zmir-enable-passes=+SimplifyConstCondition-after-inst-simplify` folds `c = 1_u8; switchInt(copy c)` (`scc_switch_immediate`) directly to `goto -> bb2;`, whereas inserting `other = 0_u32;` between the assignment and the switch (`scc_switch_intervening`) leaves `switchInt(copy _1)` completely untouched.
- **Note on indirect, dead, and moved places in `has_place_const` (`derived`):** `lines 70-74` record `(lhs, c)` for any `Place` (including indirect `*ptr = const c` without checking `lhs.is_indirect()` or aliasing). Under sequential non-atomic MIR execution with zero intervening statements, another thread cannot mutate `*ptr` without exhibiting a data race (`r[undefined.race]`), and if `*ptr` is dangling, misaligned, or dead, the preceding store `*ptr = const c` already triggered immediate UB before the read. Separately, when the folded operand is `Operand::Move(lhs)` under move-deinitializing semantics (`deinitMovedPlace = true`), replacing `SwitchInt`/`Assert` with `Goto` or `Assume(true)` with `Nop` leaves `lhs = const c` in place and omits the deinitialization of `lhs`—a boundary interaction if downstream code ever illegally reads `lhs` after the eliminated move (recorded under **Boundaries**).

#### 4.2 `SwitchInt` and `Assert` Folding Asymmetry (`simplify_branches.rs:78-95`)

After scanning a block's statements, `SimplifyConstCondition` inspects the block terminator (`lines 78-95`):

```rust
let terminator = match terminator.kind {
    TerminatorKind::SwitchInt { ref discr, ref targets, .. }
        if let Some(c) = try_get_const(discr, pre_place_const.take())
            && let Some(constant) = c.const_.try_eval_bits(tcx, typing_env) =>
    {
        let target = targets.target_for_value(constant);
        TerminatorKind::goto(target)
    }
    TerminatorKind::Assert { target, ref cond, expected, .. }
        if let Some(c) = try_get_const(&cond, pre_place_const.take())
            && let Some(constant) = c.const_.try_eval_bool(tcx, typing_env)
            && constant == expected =>
    {
        TerminatorKind::goto(target)
    }
    _ => continue,
};
patch.patch_terminator(bb, terminator);
```

Crucial asymmetry:
- **`TerminatorKind::SwitchInt`:** Any evaluable constant bit-pattern folds directly to `TerminatorKind::goto(targets.target_for_value(constant))`.
- **`TerminatorKind::Assert`:** Guarded by `&& constant == expected` (`line 89`). A **passing** assert (`constant == expected`) folds to `TerminatorKind::goto(target)`. A **failing** assert (`constant != expected`) is **never** folded to `TerminatorKind::Unreachable`, because a failing MIR `Assert` denotes a deterministic runtime panic (potentially caught by `catch_unwind` or executing drop/unwind cleanup pads), NOT undefined behavior! Folding a failing `Assert` to `Unreachable` would turn `.panic` into `.ub .unreachable`, violating even standard compiler UB refinement (`Refines`).
- **Empirical confirmation (`support/probe_results.json`, `simplify_const_condition.assert_folding_asymmetry`):** With `+DataflowConstProp,+SimplifyConstCondition-after-const-prop`:
  - `scc_assert_pass` (`x / 1`): `assert(!const false, "attempt to divide `{}` by zero", copy _2) -> [success: bb1, unwind continue]` folds to `goto -> bb1;`.
  - `scc_assert_fail` (`x / 0`, `#[allow(unconditional_panic)]`): `assert(!const true, "attempt to divide `{}` by zero", copy _2) -> [success: bb1, unwind continue]` remains **unchanged** (`unreachable;` is not emitted).
- **Mechanized proof (`support/MatchBranchesSingleUseConstsAndCostCheckerSoundness.lean`):** `scc_passing_assert_folds_to_goto` (`line 2018`), `scc_failing_assert_preserved` (`line 2021`), and `scc_folding_failing_assert_to_unreachable_unsound` (`line 2027`: proves `¬ Refines .panic (.ub .unreachable)`).

#### 4.3 `Assume(false)` Block-Statement Wipe via `MirPatch::apply` (`simplify_branches.rs:59-69`, `patch.rs:320-327`)

When `SimplifyConstCondition` encounters `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(discr))` whose condition evaluates to a constant `bool`:
- If `constant == true`: marks the statement as `Nop` via `patch.nop_statement(...)` (`line 65`).
- If `constant == false`: executes:
  ```rust
  patch.patch_terminator(bb, TerminatorKind::Unreachable);
  continue 'blocks;
  ```
  (`lines 67-68`). Note that `SimplifyConstCondition` itself does **not** explicitly delete statements in `bb`—instead, the block-statement wipe happens inside `MirPatch::apply` (`compiler/rustc_mir_transform/src/patch.rs:320-327` at `137d1d4945`; `lines 300-307` at `14210df0e`):
  ```rust
  for (src, patch) in self.term_patch_map {
      debug!("MirPatch: patching block {:?}", src);
      let bb = &mut bbs[src];
      if let TerminatorKind::Unreachable = patch {
          bb.statements.clear();
      }
      bb.terminator_mut().kind = patch;
  }
  ```
  The interaction between `simplify_branches.rs:67` and `patch.rs:323-325` unconditionally clears **every** statement in `bb`—including all statements **preceding** `Assume(false)` in the same basic block!

- **Empirical confirmation (`support/probe_results.json`, `simplify_const_condition.assume_false_wipes_prior_ub`):** On `unsafe fn assume_false_wipe(p: *const u32) -> u32 { let v = *p; core::intrinsics::assume(false); v }` called with `p = null()`:
  - **MIR before `SimplifyConstCondition-after-inst-simplify`:** `bb0` contains `_2 = copy (*_1); assume(const false); _0 = copy _2; return;`.
  - **MIR after `SimplifyConstCondition-after-inst-simplify`:** `bb0: { unreachable; }` — `(*_1)` and `assume(const false)` are completely wiped.
  - **Live Miri execution:**
    - `-Zmir-opt-level=0 -Zmir-preserve-ub=yes`: `rc=1`, `error: Undefined Behavior: memory access failed: attempting to access 4 bytes, but got null pointer`.
    - `-Zmir-opt-level=1 -Zmir-preserve-ub=yes`: `rc=1`, `error: Undefined Behavior: entering unreachable code` (plus Miri opt warning).
    - `-Zmir-opt-level=0 -Zmir-preserve-ub=yes -Zmir-enable-passes=+SimplifyConstCondition-after-inst-simplify`: `rc=1`, `error: Undefined Behavior: entering unreachable code` (no Miri warning).
- **Exact soundness vs. diagnostic boundary (`Lean v4.34.1`):**
  - `simplifyConstCondition_ubEquivalent` (`line 1926`) and `simplifyConstCondition_refines` (`line 1987`) prove that under `rustc` MIR semantics—where **no** `StatementKind` can panic, perform external I/O, or diverge—every statement preceding `Assume(false)` either succeeds or triggers immediate UB; in both cases, entering the block inevitably causes UB (`nullDeref` or `assumeFalse`), so clearing all statements and setting `TerminatorKind::Unreachable` preserves BOTH standard UB refinement (`Refines`) AND weak UB equivalence (`UbEquivalent`: UB iff UB).
  - However, `scc_assume_false_wipes_statements_and_shifts_ub_kind` (`line 2040`) proves `¬ ExactEq` (exact UB kind shifts from `.nullDeref` to `.unreachable`), and `assume_false_clear_requires_non_panicking_non_diverging_stmts` (`line 2059`) isolates the hidden TCB invariant of `MirPatch::apply`: if any MIR dialect or custom statement could panic, trap, observe external side effects, or diverge before `Assume(false)`, `bb.statements.clear()` would become **unsound** (`¬ Refines`).

### 5. `CostChecker` (`cost_checker.rs`) and `Inline` / `JumpThreading` / `CrossCrateInline` Callers

**Basis:** `source + execution + derived` (plus Lean mechanization)

#### 5.1 Complete Cost Algebra (`compiler/rustc_mir_transform/src/cost_checker.rs:1-205`)

`CostChecker` maintains two `usize` accumulators (`penalty: usize`, `bonus: usize`, initialized to `0`) and computes final cost via saturating subtraction (`lines 49-51`):

```rust
pub(super) fn cost(&self) -> usize {
    usize::saturating_sub(self.penalty, self.bonus)
}
```

Exact constants (`lines 6-11`) and per-construct deltas at `rust-lang/rust@137d1d49458b73b7b85d2c1599d8730886d65e47`:

| MIR Construct / Hook | `penalty` Delta | `bonus` Delta | Conditions & Source Lines (`137d1d4945`) |
| :--- | :---: | :---: | :--- |
| `add_function_level_costs()` | `0` | **`+25`** (`CALL_PENALTY`) | Iff `callee_body.basic_blocks.iter().filter(\|bbd\| is_call_like(bbd.terminator())).count() == 1` (`lines 39-47`). Note: inspects ALL basic blocks in `callee_body`, not only worklist-reachable ones! |
| `Operand::RuntimeChecks(UbChecks)` | `0` | **`+25`** (`CALL_PENALTY`) | Iff `!inline_mir_preserve_debug.unwrap_or(sess.ub_checks())` (`lines 65-78`). |
| `StatementKind::Intrinsic(Assume)` | `+5` (`INSTR_COST`) | `0` | `lines 86-88`. |
| `StatementKind::Intrinsic(CopyNonOverlapping)` | `+25` (`CALL_PENALTY`) | `0` | `lines 86, 89`. |
| `StatementKind::Assign` of ZST `ConstValue::ZeroSized` | **`0`** | `0` | **New at `137d1d4945`** (`lines 92-96`); charged `+5` at `14210df0e`. |
| All other `StatementKind::Assign` | `+5` (`INSTR_COST`) | `0` | `line 97` (and `super_statement` visits operands!). |
| Other `StatementKind` (`StorageLive`, `StorageDead`, `Nop`, `PlaceMention`, `Retag`, `SetDiscriminant`, ...) | `0` | `0` | `line 98` (still invokes `super_statement` at `line 100`). |
| `TerminatorKind::Drop` | `+25` (`+50` if `Cleanup`) | `0` | Only if instantiated `ty.needs_drop(tcx, typing_env)` is `true` (`lines 105-114`); otherwise `0`! |
| `TerminatorKind::Call` (intrinsic: `func.const_fn_def()` + `tcx.intrinsic(def_id).is_some()`) | **`+5`** (`INSTR_COST`) (`+50` if `Cleanup`) | `0` | Intrinsic call exemption (`lines 116-120, 124-126`). Still calls `super_terminator` (visits args). |
| `TerminatorKind::Call` (non-intrinsic) | `+25` (`CALL_PENALTY`) (`+50` if `Cleanup`) | `0` | `lines 121-126`. |
| `TerminatorKind::TailCall` | `+25` (`CALL_PENALTY`) | `0` | `lines 128-130` (note: `inline.rs:429-432` currently refuses to inline callees containing `TailCall`). |
| `TerminatorKind::SwitchInt` (`Operand::Constant` or `Operand::RuntimeChecks`) | `0` | **`+10`** (`CONST_SWITCH_BONUS`) | `lines 132-135` (plus `super_terminator` visits `discr`, which can ALSO add `+25` if `RuntimeChecks::UbChecks`!). |
| `TerminatorKind::SwitchInt` (other, `all_targets().len() > 3`) | `+20` (`LARGE_SWITCH_PENALTY`) | `0` | `lines 136-138` (more than 2 explicit targets + `otherwise`). |
| `TerminatorKind::SwitchInt` (other, `all_targets().len() <= 3`) | `+5` (`INSTR_COST`) | `0` | `lines 139-141`. |
| `TerminatorKind::Assert` (optional overflow check & `!preserve_debug_or_overflow`) | **`+5`** (`INSTR_COST`) (`+50` if `Cleanup`) | `0` | `msg.is_optional_overflow_check()` = `OverflowNeg \| Overflow(Add \| Sub \| Mul \| Shl \| Shr)` (`rustc_middle/src/mir/terminator.rs:172-176`) and `!inline_mir_preserve_debug.unwrap_or(sess.overflow_checks())` (`cost_checker.rs:144-159`). |
| `TerminatorKind::Assert` (all other asserts or checks preserved) | `+25` (`CALL_PENALTY`) (`+50` if `Cleanup`) | `0` | `lines 154-159`. |
| `TerminatorKind::UnwindResume` | `+45` (`RESUME_PENALTY`) | `0` | `line 161`. |
| `TerminatorKind::InlineAsm` | `+5` (`+50` if `Cleanup`) | `0` | `lines 162-167`. |
| `TerminatorKind::Unreachable` | `0` | `+5` (`INSTR_COST`) | `lines 168-170`. |
| `TerminatorKind::Goto`, `Return`, `UnwindTerminate` | `0` | `0` | `lines 171-172`. |

#### 5.2 Exact Partition of `is_call_like` and Three Subtle Cost Interactions

`is_call_like` (`cost_checker.rs:189-205`) classifies terminators as:
- **`true`:** `Call`, `TailCall`, `Drop`, `Assert`, `InlineAsm`
- **`false`:** `Goto`, `SwitchInt`, `UnwindResume`, `UnwindTerminate`, `Return`, `Unreachable`

Three subtle interactions emerge directly from comparing `cost_checker.rs` and `inline.rs`:

1. **The `+50` Two-Call Inlining Cliff & Non-Amplification Principle:** For a non-intrinsic callee with non-call penalty `P` and bonus `B <= P`, adding a single call gives `penalty = P + 25` and `bonus = B + 25` (from `add_function_level_costs`), so `cost = (P + 25) - (B + 25) = P - B` (`single_call_bonus_cancels_call_penalty`, `line 2245`). Adding a second call raises `penalty` to `P + 50` **and drops the `+25` single-call bonus**, jumping net cost to `(P - B) + 50`—a **`+50` (`2 * CALL_PENALTY`)** cliff (`two_call_cliff_delta`, `line 2254`). Mechanized theorem `single_call_inlining_non_amplification` (`line 2271`) proves the exact structural justification: replacing one call-site in a caller with `c >= 1` calls by a callee with `k` calls yields `(c - 1) + k <= c <-> k <= 1`. This same threshold `k > 1` drives `NormalInliner::on_inline_success` (`inline.rs:460-466`), which increments `self.top_down_counter` (capped at `TOP_DOWN_DEPTH_LIMIT = 5`, `inline.rs:32, 287`) if and only if `new_calls_count > 1`.
2. **Intrinsic Call + Single-Call Bonus Net Negative Cost (`-20`):** Because `is_call_like` (`line 192`) matches `Call { .. }` **without** excluding intrinsics, a callee containing exactly one intrinsic `Call` (and no other `Drop`/`Assert`/`InlineAsm`) incurs `+5` (`INSTR_COST`) in `visit_terminator` while receiving `+25` (`CALL_PENALTY`) in `add_function_level_costs`—a **net `-20` bonus** offsetting up to 4 non-call assignments (`single_intrinsic_net_bonus_and_two_intrinsic_jump`, `line 2326`)! Conversely, a `Drop` terminator whose instantiated type has `!ty.needs_drop(...)` contributes `0` penalty in `visit_terminator` (`line 108`), yet `is_call_like` (`line 192`) **still** counts it as `true` in `add_function_level_costs` (because `add_function_level_costs` does not check `needs_drop`)—so a dead `Drop` can either spuriously grant a `+25` bonus to a 0-call function or spuriously suppress the `+25` bonus of a 1-call function!
3. **`Inline`, `CrossCrateInline`, and `JumpThreading` Caller Semantics:**
   - **`NormalInliner::check_callee_mir_body` (`inline.rs:369-450`):** Selects base `threshold`:
     - `inline_mir_forwarder_threshold` (default `30`) if `caller_is_inline_forwarder || past_depth_limit()` (`history.len() > 20 || top_down_counter > 5`),
     - else `inline_mir_hint_threshold` (default `100`) if `tcx.cross_crate_inlinable(callee.def_id())`,
     - else `inline_mir_threshold` (default `50`).
     Then adds a `25%` small-CFG bonus (`threshold += threshold / 4`) if `callee_body.basic_blocks.len() <= 3` (`lines 380-382`, raising `50 -> 62` and `100 -> 125`), calls `checker.add_function_level_costs()`, traverses reachable blocks via DFS worklist (skipping unwind cleanup edges of `Drop`s where `!ty.needs_drop`), and inlines iff `checker.cost() <= threshold` (`line 443`). Note also that `check_codegen_attributes` (`inline.rs:831-834`) rejects non-generic callees whenever `!tcx.cross_crate_inlinable(callee.def_id())`, and `cross_crate_inline.rs:109-143` uses a **separate** local `struct CostChecker` requiring `calls == 0 && resumes == 0 && landing_pads == 0 && statements <= threshold`! Thus non-generic functions containing a real `Call` are **not** MIR-inlined unless marked `#[inline]` (which sets `cross_crate_inlinable = true` and uses `inline_mir_hint_threshold`, default `100`).
   - **`ForceInline` (`inline.rs:75-97`):** Uses `PassPolicy::Required` (`line 86`) and `ForceInliner` (bypasses `CostChecker` entirely).
   - **`JumpThreading` (`jump_threading.rs:75, 868-876`):** Instantiates `CostChecker::new(tcx, typing_env, None, body)` per basic block (without `add_function_level_costs()`) to bound block duplication cost against `MAX_COST: u8 = 100`.

#### 5.3 Exact Empirical Calibration Against Live `rustc 1.98.0-nightly` (`support/probe_results.json`)

Every cost formula was verified against `rustc 1.98.0-nightly (14210df0e)` by sweeping `-Zinline-mir-hint-threshold=T` and binary-searching exact minimum inlining thresholds across single-crate and cross-crate callees (`support/probe_results.json`, `cost_checker`):

| Callee Under Test | MIR Structure | Analytical `CostChecker` Cost | Observed Live `rustc` Cliff (`T` -> `eff_threshold`) | Match? |
| :--- | :--- | :---: | :--- | :---: |
| `one_call_under_bonus` (`#[inline]`, 2 BBs `<= 3`) | 22 assigns (`110`) + 1 `Call` (`+25`) − single-call bonus (`-25`) | **`110`** | `T=87` (`eff=108`): NOT inlined; `T=88` (`eff=110`): **INLINED**; default `T=100` (`eff=125`): **INLINED** | **Exact (0 err)** |
| `two_intrinsics_exempt` (`#[inline]`, 3 BBs `<= 3`) | 21 assigns (`105`) + 2 `ctpop` intrinsics (`2 × 5 = 10`) − 0 bonus | **`115`** | `T=91` (`eff=113`): NOT inlined; `T=92` (`eff=115`): **INLINED**; default `T=100` (`eff=125`): **INLINED** | **Exact (0 err)** |
| `two_calls_no_bonus` (`#[inline]`, 3 BBs `<= 3`) | 21 assigns (`105`) + 2 regular `Call`s (`2 × 25 = 50`) − 0 bonus | **`155`** | Default `T=100` (`eff=125`): **NOT inlined**; `T=123` (`eff=153`): NOT inlined; `T=124` (`eff=155`): **INLINED** | **Exact (0 err)** |
| `ub_dep_fn` (cross-crate, `> 3` BBs, `UbChecks` preserved in dep MIR) | 30 assigns (`150`) + `SwitchInt` (`5`) + 2 `Call`s (`50`) + `Operand::RuntimeChecks(UbChecks)` (`-25` when `!preserve_debug`) | **`180`** (`preserve_debug=no`) vs **`205`** (`preserve_debug=yes`), delta **`+25`** | Binary search: `T=180` (`no`) vs `T=205` (`yes`), observed delta **`+25`** | **Exact (0 err)** |
| `ovf_dep_fn` (cross-crate, `> 3` BBs, 4 `AssertKind::Overflow(Add)`) | 13 assigns (`65`) + 4 optional overflow asserts (`4 × 5 = 20` vs `4 × 25 = 100`) | **`85`** (`preserve_debug=no`) vs **`165`** (`preserve_debug=yes`), delta **`+80`** | Binary search: `T=85` (`no`) vs `T=165` (`yes`), observed delta **`+80`** (`4 × 20`) | **Exact (0 err)** |

All 5 exact costs and threshold transitions are additionally cross-checked inside Lean 4 (`probe_callees_exact_costs_and_cliffs`, `line 2368`; `probe_four_overflow_exact_delta`, `line 2390`; `probe_ub_checks_exact_delta`, `line 2403`).

### 6. Synthesis for Verified-Compiler and Anneal Trusted-Boundary Design

**Basis:** `derived` (from Sections 1–5 and `joshlf/anneal@c131b320e`)

1. **Mandatory MIR Capture Phase Isolation:** Any verifier whose semantics models `StorageDead` / uninitialized reads (`SingleUseConsts`), dereference validity (`MatchBranchSimplification`), or exact UB attribution (`SimplifyConstCondition` + `MirPatch::apply`) **must** capture MIR at or before `Runtime(PostCleanup)` with `-Zmir-preserve-ub=yes` **and** explicit `-Zmir-opt-level=0` (never relying on `-Zmir-preserve-ub=yes` alone to disable MIR optimizations, nor assuming Miri warns on `-Zmir-enable-passes` overrides).
2. **Repairing the Three Simplification Passes for a Verified Compiler:**
   - **Verified `SingleUseConsts`:** Must check (i) `init_loc` strictly dominates `use_loc` in the CFG, (ii) `local` is live on all paths at `init_loc`, (iii) no `StorageLive(local)`, `StorageDead(local)`, write to `local`, or intervening `Move(local)` (under `deinitMovedPlace = true`) occurs on any path from `init_loc` to `use_loc`, and (iv) scoped debuginfo preservation if debug fidelity is required.
   - **Verified `MatchBranchSimplification`:** When `self.discr_local == None` (i.e., `identical_stmts` or `unify_if_equal_const`), emitting `StatementKind::PlaceMention(place)` for indirect/place discriminants under UB-preserving modes closes the `*null_ptr` erasure gap (`mbs_identical_with_placemention_exact`); under `unify_by_copy`, retaining `137d1d4945`'s `borrowed_locals` and `copy_src_place.local != dest.local` checks is mandatory for sound refinement.
   - **Verified `SimplifyConstCondition`:** Preserving the `constant == expected` guard on `Assert` is soundness-critical; when lowering `Assume(false)` via `MirPatch::apply`, clearing prior statements in `bb` is sound **if and only if** the MIR dialect guarantees all `StatementKind` variants are terminating and non-panicking (no inline traps, panics, or externally observable I/O inside statements).
3. **Cost Model as Pure Untrusted Oracle:** `CostChecker` affects only inlining and jump-threading profitability (never operational semantics), so in a verified compiler architecture it belongs strictly outside the Trusted Computing Base as an untrusted heuristic oracle—while remembering that `inline_mir_preserve_debug` and `ub_checks` / `overflow_checks` shift inlining thresholds by exact multiples of `+25` and `+20`, which affects downstream MIR shape and proof-checking cost.

## Boundaries

To prevent over-generalization, negative space is partitioned explicitly using the four standard categories:

1. **Known not to apply:**
   - **Default Miri invocations without explicit MIR-opt overrides:** Because `MIRI_DEFAULT_ARGS` (`rust-lang/miri@f667c131a9a3c88f1b0d64b1abe2f5ac256043de`, `src/lib.rs:204-205`) passes **both** `-Zmir-preserve-ub` and `-Zmir-opt-level=0`, default `cargo miri run` does **not** run `SingleUseConsts`, `MatchBranchSimplification`, or `SimplifyConstCondition` and therefore does **not** exhibit the UB erasures documented here unless the user overrides `-Zmir-opt-level >= 1` or passes `-Zmir-enable-passes=+...`.
   - **`unify_by_copy` aliasing bug on upstream HEAD `137d1d4945`:** The missing `borrowed_locals` / same-local aliasing check present at `14210df0e` (`rustc 1.98.0-nightly`) does **not** apply to `rust-lang/rust@137d1d49458b73b7b85d2c1599d8730886d65e47`, which added the guard at `match_branches.rs:264-276`.
   - **ZST constant `Assign` penalty on upstream HEAD `137d1d4945`:** The `+5` `INSTR_COST` penalty on `ConstValue::ZeroSized` assignments present at `14210df0e` does **not** apply to `137d1d4945`, which exempts ZST constant assignments at `cost_checker.rs:92-96`.
   - **Native codegen soundness claims for `SingleUseConsts` and `MatchBranchSimplification` (`identical_stmts` / `unify_by_eq_op` / `unify_by_int_to_int`):** Under standard Rust UB refinement (`Refines`, where a program exhibiting UB may be compiled to any behavior, `r[undefined.intro]`), erasing `DeadLocal`, uninitialized-read, `*null_ptr`, or unreachable-`otherwise` UB is **not** a miscompilation of UB-free Rust programs. The violation is specifically against **UB preservation** (`UbEquivalent` / `-Zmir-preserve-ub` / Miri / Anneal negative UB canaries).
   - **Lean 4 mechanization scope (`support/MatchBranchesSingleUseConstsAndCostCheckerSoundness.lean`):** The Lean proofs formalize faithful standalone operational abstractions of the four passes (with explicit storage slots, `deinitMovedPlace = true`, abstract heap, bit-level `can_cast`, and exact `CostChecker` algebra); they do **not** directly import `joshlf/anneal`'s full `Trusted.MirSemantics` or `rustc_middle::mir::Body` Rust implementation, and therefore do **not** mechanically certify the Rust compiler binaries themselves.

2. **Not examined:**
   - **Downstream MIR passes beyond the four audited components:** Other `run_optimization_passes` passes (`GVN`, `DataflowConstProp`, `ReferencePropagation`, `DeadStoreElimination`, `JumpThreading`'s transformation body, `EarlyOtherwiseBranch`, `SimplifyComparisonIntegral`, `DestinationPropagation`, `SsaRangePropagation`) were not audited for `-Zmir-preserve-ub` leaks or UB erasure.
   - **Live binary execution on a compiler built directly from `rust-lang/rust@137d1d49458b73b7b85d2c1599d8730886d65e47`:** Live `rustc` and `miri` executions ran on `rustc 1.98.0-nightly (14210df0e 2026-05-31)`; applicability to `137d1d4945` is established via complete line-by-line source diffs of all affected files (`match_branches.rs`, `simplify_branches.rs`, `single_use_consts.rs`, `cost_checker.rs`, `inline.rs`, `patch.rs`).
   - **Non-`x86_64-unknown-linux-gnu` host/target platforms:** Although `CostChecker` constants and MIR simplification logic are target-independent except for `pointer_width` (`isize`/`usize` bit width in `can_cast` and `remove_successors_from_switch`), live probes were executed only on `x86_64-unknown-linux-gnu`.
   - **`SingleUseConsts` interaction with `Operand::Move` on `deinitMovedPlace` in `SimplifyConstCondition`:** Whether a real `rustc` MIR sequence can produce an illegal post-`Move` read whose `Move` was folded away by `SimplifyConstCondition`'s `try_get_const` (leaving the local initialized) was identified analytically from source (`simplify_branches.rs:43-48`) but not empirically executed in Miri.
   - **`CostChecker` interaction with `Drop` terminators whose `needs_drop == false` in `add_function_level_costs`:** Identified directly by source inspection (`cost_checker.rs:42-46, 108, 192`), but not constructed as an empirical live `rustc` threshold probe.

3. **Unknown:**
   - **Whether `options.rs:2789`'s `"implies -Zmir-opt-level=0"` claim is an intentional stale comment or an unfixed CLI regression:** Source inspection of `rust-lang/rust@137d1d4945` proves the implication is absent from `rustc_session/src/session.rs:988-990` and `config.rs`, and live execution confirms `-Zmir-preserve-ub=yes` alone runs `mir_opt_level == 1`, but upstream maintainer intent (whether the doc string should be corrected or `Session::mir_opt_level` should check `mir_preserve_ub`) is unresolved without inspecting upstream design discussions.
   - **Exact performance/compile-time cost of gating `SingleUseConsts`, `MatchBranchSimplification`, and `SimplifyConstCondition` on `!mir_preserve_ub` or emitting `PlaceMention`:** Not measured.

4. **Unsupported:**
   - **`TailCall` MIR inlining:** Explicitly rejected by `inline.rs:429-432` (`"can't inline functions with tail calls"`) and `check_inline.rs:76-80` despite `CostChecker::visit_terminator` assigning `CALL_PENALTY` to `TerminatorKind::TailCall` (`cost_checker.rs:128-130`).
   - **`can_cast` over `char` or `bool` discriminants:** Explicitly unsupported in `match_branches.rs:477-480` (`_ => return false`).
   - **Cross-crate non-`#[inline]` MIR inlining of non-generic functions containing `Call`s:** Explicitly rejected by `cross_crate_inline.rs:113` (`checker.calls == 0`) combined with `inline.rs:831-834` (`!is_generic && !tcx.cross_crate_inlinable(...)`).

## Evidence

### 1. Primary Upstream Source Citations (Observed `2026-11-23`)

- **`rust-lang/rust` at `137d1d49458b73b7b85d2c1599d8730886d65e47`:**
  - `compiler/rustc_mir_transform/src/single_use_consts.rs:25-206` (`SingleUseConsts::policy` line `29`, `ineligible_locals` line `39`, `Nop` replacement lines `54-57`, `VarDebugInfo` loop lines `67-71`, `drop_invalid_debuginfos` line `89`, `SingleUseConstsFinder` lines `105-166`, `StorageLive`/`StorageDead` ignored line `146`, `LocalReplacer` lines `168-205`).
  - `compiler/rustc_mir_transform/src/match_branches.rs:15-565` (`MatchBranchSimplification::policy` lines `18-21`, `discr_local()` lines `52-58`, `unify_if_equal_const` lines `61-82`, `unify_by_eq_op` lines `115-148`, `unify_by_int_to_int` lines `187-215`, `unify_by_copy` lines `233-315` with `borrowed_locals` guard lines `264-276`, `try_unify_stmts` lines `318-355`, `candidate_match` lines `359-384`, `simplify_match` lines `386-463` with `if let Some(discr_local)` lines `450-459`, `can_cast` lines `466-489`, `identical_stmts` lines `555-565`).
  - `compiler/rustc_mir_transform/src/simplify_branches.rs:8-99` (`SimplifyConstCondition` enum lines `8-12`, `policy` lines `26-28`, `try_get_const` lines `35-51`, per-block scan lines `53-75`, `Assume(true)` -> `nop_statement` line `65`, `Assume(false)` -> `patch_terminator(..., Unreachable)` lines `67-68`, `SwitchInt`/`Assert` folding lines `78-95`).
  - `compiler/rustc_mir_transform/src/patch.rs:261-328` (`MirPatch::apply`, specifically `if let TerminatorKind::Unreachable = patch { bb.statements.clear(); }` at lines `323-325`).
  - `compiler/rustc_mir_transform/src/cost_checker.rs:6-205` (constants lines `6-11`, `add_function_level_costs` lines `39-47`, `cost()` lines `49-51`, `visit_operand` lines `63-81`, `visit_statement` lines `83-101` with ZST const exemption lines `92-96`, `visit_terminator` lines `103-181`, `is_call_like` lines `189-205`).
  - `compiler/rustc_mir_transform/src/inline.rs:31-32, 75-97, 263-475, 813-862` (`HISTORY_DEPTH_LIMIT = 20`, `TOP_DOWN_DEPTH_LIMIT = 5`, `ForceInline`, `NormalInliner::check_callee_mir_body`, threshold calculation lines `369-383`, `on_inline_success` lines `460-466`, `check_codegen_attributes` lines `831-834`).
  - `compiler/rustc_mir_transform/src/cross_crate_inline.rs:109-143` (separate `CostChecker` requiring `calls == 0`).
  - `compiler/rustc_mir_transform/src/jump_threading.rs:75, 868-876` (block-level `CostChecker` usage with `MAX_COST = 100`).
  - `compiler/rustc_mir_transform/src/unreachable_prop.rs:62-151` (`remove_successors_from_switch`).
  - `compiler/rustc_mir_transform/src/remove_place_mention.rs:11-15` (`!ctx.opts.unstable_opts.mir_preserve_ub`).
  - `compiler/rustc_mir_transform/src/simplify.rs:131-137, 320-326` (`preserve_switch_reads`).
  - `compiler/rustc_mir_transform/src/strip_debuginfo.rs:42-50` (`drop_invalid_debuginfos`).
  - `compiler/rustc_mir_transform/src/lower_intrinsics.rs:27-37` (`ub_checks` -> `RuntimeChecks::UbChecks`).
  - `compiler/rustc_mir_transform/src/lib.rs:684-789` (`run_runtime_cleanup_passes` and `run_optimization_passes` exact pass order).
  - `compiler/rustc_mir_transform/src/pass_manager.rs:88-165, 210-285` (`PassPolicy`, `PassCtx`, `WithMinOptLevel`, `should_run_pass`).
  - `compiler/rustc_session/src/options.rs:2784-2789` (`mir_opt_level`, `mir_preserve_ub` help text), `compiler/rustc_session/src/session.rs:988-990` (`Session::mir_opt_level`), `compiler/rustc_session/src/config.rs:120-128` (`OptLevel::mir_opt_level`).
  - `compiler/rustc_middle/src/mir/mod.rs:869-877` (`Local::arg`), `compiler/rustc_middle/src/mir/statement.rs:279-290, 383-385` (`is_stable_offset`), `compiler/rustc_middle/src/mir/terminator.rs:172-176` (`AssertKind::is_optional_overflow_check`).
- **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`):**
  - Diffed directly against `137d1d4945` for `match_branches.rs` (550 LOC; `if let Some(discr_local)` at lines `435-444`), `simplify_branches.rs`, `single_use_consts.rs`, `cost_checker.rs` (200 LOC), `inline.rs`, and `patch.rs` (`bb.statements.clear()` at lines `303-305`).
- **`rust-lang/miri` at `f667c131a9a3c88f1b0d64b1abe2f5ac256043de`:**
  - `src/lib.rs:200-217` (`MIRI_DEFAULT_ARGS`), `src/bin/miri.rs:176-188` (`mir_opt_level() > 0` warning).
- **`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:**
  - `src/behavior-considered-undefined.md:18-19, 49-50, 99-111, 133-135, 199-200` (`r[undefined.pointer-access]`, `r[undefined.intrinsic]`, `r[undefined.dangling]`, `r[undefined.validity.scalar]`, `r[undefined.validity.undef]`).
- **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
  - `trusted/lean/Trusted/MirAst.lean:544, 638-655, 689-755`, `trusted/lean/Trusted/MirSemantics.lean:678-695, 916-977, 1344-1345, 1529-1531, 2220-2286` (`evalOperandToSlot` with `deinitMovedPlace = true`, `progStorageDeadReadUb`, `CanaryNegativeUbStorageDeadReadAnnealClaim`), `trusted/rustc-capture/src/driver.rs:1-152`.

### 2. Preserved Package Support Artifacts (Observed `2026-11-23`)

| Artifact Path | Purpose & Key Contents | SHA-256 |
| :--- | :--- | :--- |
| `support/probe_match_branches_simplify_single_use_consts_and_cost.py` | Standalone Python 3.10+ differential probe invoking live `rustc` and `miri` in a temporary directory for all 4 passes (no hardcoded results). | `86e4f351ae2c4ca1d0d4d62212782b1491ff7dc7c19ebc27b3db1aee7e0cc5f4` |
| `support/probe_results.json` | Complete live execution receipts captured on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `x86_64-unknown-linux-gnu` / LLVM `22.1.6` + `miri`. | `c74a28bb9a1092506af487e07d6ebb60fa555bf61844ae1ed450bd4499a04ec6` |
| `support/MatchBranchesSingleUseConstsAndCostCheckerSoundness.lean` | Standalone constructive Lean `v4.34.1` mechanization (`2,412` lines, `2,158` non-empty lines, `95` top-level theorems, `102` defs, `25` inductives/structures; verified `DISTINCT_AXIOMS=[propext]`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`). | `f3f5450db65cfb43930114c999f5b72e5775d6a8e166e346b5b1f727b24105dd` |

### 3. Lean 4 Verification Receipt (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)

- **Command executed (`2026-11-23`):**
  ```bash
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/MatchBranchesSingleUseConstsAndCostCheckerSoundness.lean
  ```
- **Observed result:** Exit code `0`, zero errors, zero warnings.
- **Metaprogramming environment audit (`Lean.collectAxioms` + `env.constants.map₂` scan across all `RustcMirBranchConstCost.*` declarations):**
  - `95` user-authored top-level `theorem`s (`245` total kernel theorem constants including equation/match lemmas), `102` user-authored `def`s (`519` total kernel definition constants).
  - Distinct axioms used across the entire namespace: `[propext]` only (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`).
  - Auxiliary `._unsafe_rec` constants in namespace: `0`.

## Revalidation

Use the following targeted checks to determine whether the findings still hold on a newer `rust-lang/rust`, `rust-lang/miri`, `joshlf/anneal`, or `leanprover/lean4` revision without repeating the full audit:

1. **Rerun the live `rustc` + `Miri` differential probe (~10 s on any nightly toolchain with `miri` installed):**
   ```bash
   python3 support/probe_match_branches_simplify_single_use_consts_and_cost.py --out /tmp/reval_probe.json
   ```
   Check these specific discriminating fields in `/tmp/reval_probe.json`:
   - `single_use_consts.dead_local_ub_erasure.isolated_single_use_consts_at_opt_0.rc`: remains `0` (`DEAD_LOCAL=77`) iff `SingleUseConsts` still ignores `StorageDead` and `-Zmir-preserve-ub`; flips to `1` if fixed upstream.
   - `single_use_consts.non_dominating_uninit_ub_erasure.isolated_single_use_consts_at_opt_0.rc`: remains `0` (`NONDOM=88`) iff `SingleUseConsts` still omits CFG dominance; flips to `1` if fixed.
   - `single_use_consts.mir_preserve_ub_alone_does_not_imply_opt_0.ran_single_use_consts`: remains `true` iff `-Zmir-preserve-ub=yes` still fails to force `mir_opt_level() == 0`.
   - `match_branch_simplification.indirect_null_discr_ub_erasure.isolated_mbs_at_opt_0.rc`: remains `0` (`MBS_NULL=99`) iff `simplify_match` still drops indirect discriminants without `PlaceMention`; flips to `1` if `PlaceMention` emission or `!mir_preserve_ub` gating is added.
   - `simplify_const_condition.assume_false_wipes_prior_ub.isolated_scc_at_opt_0.ub_summary`: reports `entering unreachable code` iff `MirPatch::apply` still executes `bb.statements.clear()` on `TerminatorKind::Unreachable`.
   - `cost_checker.exact_threshold_cliff_sweep` (`87->88`, `91->92`, `123->124`), `runtime_checks_ub_checks_bonus.observed_delta` (`25`), and `optional_overflow_check_delta.observed_delta` (`80`): any drift indicates a change to `cost_checker.rs` weights, `add_function_level_costs`, `is_call_like`, or `inline.rs` threshold scaling.

2. **Diff narrow upstream source regions against `rust-lang/rust@137d1d49458b73b7b85d2c1599d8730886d65e47`:**
   ```bash
   git diff 137d1d49458b73b7b85d2c1599d8730886d65e47..HEAD -- \
     compiler/rustc_mir_transform/src/single_use_consts.rs \
     compiler/rustc_mir_transform/src/match_branches.rs \
     compiler/rustc_mir_transform/src/simplify_branches.rs \
     compiler/rustc_mir_transform/src/cost_checker.rs \
     compiler/rustc_mir_transform/src/patch.rs \
     compiler/rustc_session/src/session.rs \
     compiler/rustc_session/src/options.rs
   ```
   Specifically inspect: (a) whether `Session::mir_opt_level` reads `mir_preserve_ub`; (b) whether `SingleUseConsts`, `MatchBranchSimplification`, or `SimplifyConstCondition` check `mir_preserve_ub`; (c) whether `simplify_match` emits `PlaceMention` when `discr_local.is_none()`; (d) whether `MirPatch::apply` still clears `bb.statements` on `TerminatorKind::Unreachable`; and (e) whether `cost_checker.rs` constants or `is_call_like` changed.

3. **Re-verify the Lean 4 mechanization on a newer Lean toolchain:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MatchBranchesSingleUseConstsAndCostCheckerSoundness.lean
   ```
   A clean exit code `0` confirms all 95 theorems continue to typecheck strictly under the target kernel; re-running an environment scan over `RustcMirBranchConstCost.*` confirms `DISTINCT_AXIOMS=[propext]` and `0` `._unsafe_rec` constants remain intact.
