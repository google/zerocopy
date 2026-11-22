# `rustc` Cold-Block Propagation, Branch Weights, `#[optimize]` Attributes, and `fn_can_unwind` (`nounwind`) Derivation

## Summary

In `rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `1.102.0-nightly 2026-11-11` / LLVM `23.1.5`, and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `1.98.0-nightly 2026-05-31` / LLVM `22.1.6`), three SSA/LLVM-lowering contracts govern hint propagation, per-function optimization attributes, and unwinding (`nounwind`) boundary semantics:

1. **Cold-block propagation & `2000:1` branch-weight lowering (`rustc_codegen_ssa::mir::find_cold_blocks`, `block.rs`, `intrinsic.rs`, `rustc_codegen_llvm/src/builder.rs`)**:
   - `core::intrinsics::{likely, unlikely}` desugar directly into `if b` / `if !b` calling `core::intrinsics::cold_path()` (`#[rustc_intrinsic] #[rustc_nounwind] #[cold]`), while stabilized `core::hint::cold_path()` (`#[inline(always)] #[cold]`) wraps `core::intrinsics::cold_path()`. Because `rustc_mir_transform::check_inline::is_inline_valid_on_fn` rejects `CodegenFnAttrFlags::COLD` (`Err("cold")`), MIR `NormalInliner` inlines `likely`/`unlikely` (leaving `core::intrinsics::cold_path` calls in MIR) yet leaves `core::hint::cold_path()` un-inlined until codegen.
   - During MIR-to-SSA lowering (`codegen_mir`), `find_cold_blocks` runs a **single `traversal::postorder(mir)` pass** seeding blocks terminated by `TerminatorKind::Unreachable` or a direct `FnDef` `Call`/`TailCall` whose target carries `CodegenFnAttrFlags::COLD`, and propagates coldness backward whenever a terminator has $\ge 1$ successor and **all** successors are already marked cold. This single postorder pass is unconditionally sound on arbitrary CFGs and complete on postorder DAGs, but strictly under-approximates cyclic CFGs by missing loop headers whose backedge successor has not yet been marked.
   - During codegen, `core::intrinsics::cold_path()` lowers to `OperandValue::ZeroSized` (`0` IR instructions), whereas `core::hint::cold_path()` emits an `alwaysinline cold nounwind` call before optimization (`opt2_prepass`) that LLVM's `AlwaysInlinerPass` erases. On 2-way `SwitchInt` branches with asymmetric successor coldness, `rustc_codegen_ssa` calls `@llvm.expect.i1(cond, expected)` (unless `-C opt-level=0`), which LLVM's `LowerExpectIntrinsicPass` lowers to `!{!"branch_weights", !"expected", i32 1, i32 2000}` (or `2000, 1`). On multi-way switches, `switch_with_weights` emits `!{!"branch_weights", ...}` with `2000` vs `1` directly (without `!"expected"`), and `-C opt-level=0` suppresses both mechanisms.

2. **`#[optimize(size|speed|none)]`, `#[cold]`, & `-C opt-level={s,z}` attribute derivation (`rustc_codegen_llvm/src/attributes.rs`)**:
   - `default_optimisation_attrs` emits `optsize` alone at `-C opt-level=s` and **both** `minsize` and `optsize` at `-C opt-level=z` (because LLVM's software pipeliner reads `optsize` directly).
   - `llfn_attrs_from_instance` gives per-function `#[optimize(...)]` strict override priority over `-C opt-level`: `#[optimize(size)]` emits `minsize optsize` even at `-O0`/`-O2`/`-Os`; `#[optimize(speed)]` strips both `minsize` and `optsize` even at `-Os`/`-Oz`; `#[optimize(none)]` emits `optnone`, blocks LLVM `PostOrderFunctionAttrsPass`, and forces `InlineAttr::Never` (`noinline`) in `inline_attr` (even overriding `#[inline(always)]`). `#[cold]` (`CodegenFnAttrFlags::COLD`) attaches `cold` orthogonally to `optsize`/`minsize`.

3. **`fn_can_unwind` 3-gate precedence, `AbortUnwindingCalls`, `-Z panic-in-drop=abort`, and `-C panic=immediate-abort` (`rustc_middle/src/ty/layout.rs`, `rustc_metadata/src/dependency_format.rs`)**:
   - `layout::fn_can_unwind` gates LLVM `nounwind` (on both definitions and callsites) through three `DefId` gates before dispatching on `ExternAbi`: (1) `NEVER_UNWIND` (`#[rustc_nounwind]`), (2) `!panic_strategy().unwinds() && !is_foreign_item(did)`, and (3) `!panic_in_drop.unwinds() && LangItem::DropGlue`.
   - Under `-C panic=abort`, Gate 2 assigns `nounwind` to Rust-defined `pub extern "C-unwind" fn`, whereas foreign `unsafe extern "C-unwind"` bypasses Gate 2 and remains non-`nounwind`, forcing callers—even `nounwind` Rust callers—to emit `invoke ... unwind label %terminate` rather than `call`.
   - Under `-C panic=unwind -Z panic-in-drop=abort`, Gate 3 marks `LangItem::DropGlue` (`core::ptr::drop_glue::<T>`) `nounwind` (with internal `invoke <T as Drop>::drop ... -> core::panicking::panic_cannot_unwind`), while public `core::ptr::drop_in_place::<T>` stays non-`nounwind`. Linking a binary directly against prebuilt `std` with `-Z panic-in-drop=abort` fails at `dependency_format::verify_ok` with `IncompatiblePanicInDropStrategy`, whereas an independently compiled object aborts with `SIGABRT` inside `drop_glue`.
   - Under `-C panic=immediate-abort` (`-Z unstable-options`), `#![no_std]` library IR marks functions `nounwind` while still emitting `tail call @core::panicking::panic_bounds_check` + `unreachable` (`has_llvm_trap = false`) against prebuilt `core`, and linking any final binary fails with `IncompatibleWithImmediateAbortCore` unless `core` itself is compiled with `ImmediateAbort`.

4. **Mechanization (`support/ColdBlocksAndNoUnwindSoundness.lean`)**:
   - Kernel-verified in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with `0` errors, `0` warnings, `0` audit violations, `0` forbidden tokens, and axioms restricted to `[propext, Quot.sound]`. Proves `findColdBlocks_sound_and_dag_complete`, `coldPath_erasure_preserves_behavior`, `fnCanUnwind_nounwind_soundness`, and three constructive counterexamples (`ce1`–`ce3`) demonstrating cyclic postorder incompleteness, foreign `C-unwind` `nounwind` unsafety under `panic=abort`, and `drop_in_place` vs `drop_glue` conflation unsafety under `-Z panic-in-drop=abort`.

## Applicability

This report establishes primary-source, empirical, and mechanized properties across the five subjects recorded in `REPORT.json`:

1. **`rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly 2026-11-11`, bundled LLVM `23.1.5`)**:
   - Primary source audit across `compiler/rustc_codegen_ssa/src/mir/{mod.rs, block.rs, intrinsic.rs}`, `compiler/rustc_codegen_ssa/src/traits/builder.rs`, `compiler/rustc_codegen_llvm/src/{builder.rs, intrinsic.rs, attributes.rs, abi.rs, back/write.rs}`, `compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs`, `compiler/rustc_mir_transform/src/{check_inline.rs, inline.rs, abort_unwinding_calls.rs, shim.rs}`, `compiler/rustc_middle/src/{ty/layout.rs, middle/codegen_fn_attrs.rs}`, `compiler/rustc_ty_utils/src/abi.rs`, `compiler/rustc_metadata/src/dependency_format.rs`, and `library/core/src/{intrinsics/mod.rs, hint.rs, ptr/mod.rs}`.
   - Empirical baseline preservation in `support/probe_output/llvm23_baseline.json` for `x86_64-unknown-linux-gnu` covering the 3-mode `cold_path`/`likely`/`unlikely` matrix, the `3 × 5` `#[optimize]`/`#[cold]` × `-O{2,s,z}` attribute matrix, and the 4-strategy `nounwind`/`ImmediateAbort` matrix.

2. **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly 2026-05-31`, bundled LLVM `22.1.6`)**:
   - Both source inspection and **live compiler/binary execution** (`support/probe_cold_blocks_optimize_and_nounwind.py` -> `support/probe_output/probe_results.json`, `20/20` checks passing on `x86_64-unknown-linux-gnu`).
   - **Shared vs. differing behavior between `14210df0e` (`1.98.0`) and `3ef0c22cd` (`1.102.0`)**:
     - *Shared*: Exact algorithmic identity for `find_cold_blocks`, `@llvm.expect.i1` emission, `switch_with_weights` `2000:1` weights, `lowerExpect` lowering (`!{!"branch_weights", !"expected", i32 1, i32 2000}` confirmed identically in LLVM `22.1.6` and LLVM `23.1.5`), `default_optimisation_attrs` / `llfn_attrs_from_instance` / `inline_attr` `OptNone` coercion, 3-gate `fn_can_unwind` precedence, `DropGlue` vs `drop_in_place` split, and prebuilt `core`/`std` link rejections (`IncompatibleWithImmediateAbortCore`, `IncompatiblePanicInDropStrategy`).
     - *Differing*:
       1. `find_cold_blocks` stores its result in `IndexVec<mir::BasicBlock, bool>` at `14210df0e` (`mir/mod.rs:596-600`) versus `DenseBitSet<mir::BasicBlock>` at `3ef0c22cd` (`mir/mod.rs:670-674`).
       2. `#[optimize(...)]` requires `#![feature(optimize_attribute)]` in `1.98.0-nightly` (`14210df0e`), whereas `OptimizeParser` has `AttributeStability::Stable` in `1.102.0-nightly` (`3ef0c22cd`, `codegen_attrs.rs:32`).
       3. `attributes.rs:73-78` at `3ef0c22cd` drops the `target_features` restriction on `InlineAttr::Always` when `llvm_util::get_version() >= (23, 0, 0)`.
       4. `layout.rs` replaces `ExternAbi::Unadjusted` (`14210df0e:1294`) with `ExternAbi::LlvmIntrinsic` (`3ef0c22cd:1379`) and adds `ExternAbi::RustTail` (`3ef0c22cd:1380`) to the `tcx.sess.panic_strategy().unwinds()` arm.

3. **`rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (`text/2945-c-unwind-abi.md`)**:
   - Normative definition of unwinding vs. aborting vs. UB across `"C"`-like and `"C-unwind"` boundaries under `panic=unwind` and `panic=abort`.

4. **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `trusted/audit/TrustedBoundary.lean`, `trusted/rustc-capture/src/driver.rs`)**:
   - Downstream verified-MIR consumer boundary. Establishes that `Trusted.MirAst` and `Trusted.MirSemantics` deliberately abstract away coldness metadata, optimization attributes, and unwinding terminators (`UnwindTerminate`, `Drop`, indirect `Call`, `TailCall` map to `.unsupported`), while explaining the invariants required if `Trusted.MirAst` is later extended with `Drop`, `FnAbi` `nounwind`, or unwinding FFI calls.

5. **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`)**:
   - Kernel checking `support/ColdBlocksAndNoUnwindSoundness.lean` and `support/ColdBlocksAndNoUnwindAudit.lean`. Mechanized proofs govern the standalone Lean operational models (explicitly mirroring `rustc` AST/pass algorithms) rather than directly compiling `rustc` Rust crates.

Target and flag scope empirically exercised: `x86_64-unknown-linux-gnu` under `--edition=2024`, `-C opt-level={0,2,s,z}`, `-C no-prepopulate-passes`, `-Z merge-functions=disabled`, `-Z dump-mir=Inline`, `-C panic={unwind,abort,immediate-abort}`, and `-Z panic-in-drop=abort`.

## Findings

### 1. Single-Pass Postorder Cold-Block Propagation (`find_cold_blocks`) and `cold_path` MIR Inlining

Basis: source (`3ef0c22cd`: `compiler/rustc_codegen_ssa/src/mir/mod.rs:264,667-712`, `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:125,592-595`, `compiler/rustc_mir_transform/src/check_inline.rs:57-59`, `compiler/rustc_mir_transform/src/inline.rs:290-440`, `library/core/src/intrinsics/mod.rs:676-724`, `library/core/src/hint.rs:778-786`; `14210df0e`: `mir/mod.rs:593-638`, `mir/intrinsic.rs:587-590`, `intrinsics/mod.rs:419-468`, `hint.rs:784`) + execution (`probe_results.json` `part_a_cold_blocks_and_branch_weights`).

#### Core Hint Definitions and the MIR `Inline` Split

In `library/core/src/intrinsics/mod.rs:676-724` (`3ef0c22cd`), `cold_path`, `likely`, and `unlikely` are defined so all branch hinting flows through a single `#[cold]` intrinsic:

```rust
#[rustc_intrinsic]
#[rustc_nounwind]
#[miri::intrinsic_fallback_is_spec]
#[cold]
pub const fn cold_path() {}

#[rustc_nounwind]
#[inline(always)]
pub const fn likely(b: bool) -> bool {
    if b { true } else { cold_path(); false }
}

#[rustc_nounwind]
#[inline(always)]
pub const fn unlikely(b: bool) -> bool {
    if b { cold_path(); true } else { false }
}
```

Meanwhile, stabilized `core::hint::cold_path()` (`library/core/src/hint.rs:778-786`) wraps the intrinsic in an ordinary `const fn` marked `#[inline(always)] #[cold]`:

```rust
#[stable(feature = "cold_path", since = "1.95.0")]
#[rustc_const_stable(feature = "cold_path", since = "1.95.0")]
#[inline(always)]
#[cold]
pub const fn cold_path() {
    crate::intrinsics::cold_path()
}
```

This single attribute difference creates an observable divergence during MIR optimization before codegen even starts:

- `likely` and `unlikely` carry `#[inline(always)]` **without** `#[cold]`. During `rustc_mir_transform`'s `Inline` pass (`inline.rs`), `check_inline::is_inline_valid_on_fn` (`check_inline.rs:38-70`) admits them into callers, exposing `if b` / `if !b` plus a direct `TerminatorKind::Call` to `core::intrinsics::cold_path()` inside the caller's MIR.
- Conversely, `core::hint::cold_path()` carries `#[cold]` (`CodegenFnAttrFlags::COLD`). Line `57-59` of `compiler/rustc_mir_transform/src/check_inline.rs` explicitly rejects MIR inlining of any `#[cold]` callee:

```rust
if codegen_attrs.flags.contains(CodegenFnAttrFlags::COLD) {
    return Err("cold");
}
```

Live `-Z dump-mir=Inline` output (`probe_results.json` `mir_inline_check`) confirms this exact split at `-C opt-level=2`:

| Function (`specimens`) | Call Target Remaining in MIR After `Inline` Pass | LLVM Instruction Emitted in `opt2_prepass` |
| :--- | :--- | :--- |
| `cw_1_two_way_unlikely` | `core::intrinsics::cold_path` (`true`) | None (`OperandValue::ZeroSized`, `has_cold_path_call_insn: false`) |
| `cw_2b_two_way_intrinsic_cold_path` | `core::intrinsics::cold_path` (`true`) | None (`OperandValue::ZeroSized`, `has_cold_path_call_insn: false`) |
| `cw_2_two_way_hint_cold_path` | `core::hint::cold_path` (`true`) | `call void @...cold_path() #4` (`alwaysinline cold nounwind`) |

At codegen (`rustc_codegen_ssa::mir::intrinsic::codegen_intrinsic_call`, `intrinsic.rs:125,592-595`), `sym::cold_path => OperandValue::ZeroSized` lowers `core::intrinsics::cold_path()` directly to zero instructions. Because `core::hint::cold_path()` was blocked from MIR inlining by `check_inline.rs:57`, it lowers as a normal function call to an empty `#[inline(always)] #[cold] #[rustc_nounwind]` body (`opt2_prepass`), which LLVM's `AlwaysInlinerPass` then deletes across all optimization levels including `-C opt-level=0`. Note the subtle corollary: if `#[cold]` were removed from `core::hint::cold_path()`, MIR `Inline` would inline it into `core::intrinsics::cold_path()` and `find_cold_blocks` would still see `CodegenFnAttrFlags::COLD` on the intrinsic; keeping `#[cold]` on the wrapper ensures that even if the intrinsic is invisible or disabled, `find_cold_blocks` sees `CodegenFnAttrFlags::COLD` directly (`library/core/src/hint.rs:781-782`).

#### The `find_cold_blocks` Algorithm and Cyclic Under-Approximation

During `codegen_mir` (`compiler/rustc_codegen_ssa/src/mir/mod.rs:264`), `rustc` computes `cold_blocks: DenseBitSet<mir::BasicBlock>` (`IndexVec<BasicBlock, bool>` in `14210df0e`) via `find_cold_blocks` (`mir/mod.rs:667-712` in `3ef0c22cd`; `593-638` in `14210df0e`):

```rust
for (bb, bb_data) in traversal::postorder(mir) {
    let terminator = bb_data.terminator();

    match terminator.kind {
        // If a BB ends with a call to a cold function, mark it as cold.
        mir::TerminatorKind::Call { ref func, .. }
        | mir::TerminatorKind::TailCall { ref func, .. }
            if let ty::FnDef(def_id, ..) = *func.ty(local_decls, tcx).kind()
                && let attrs = tcx.codegen_fn_attrs(def_id)
                && attrs.flags.contains(CodegenFnAttrFlags::COLD) =>
        {
            cold_blocks.insert(bb);
            continue;
        }

        // If a BB ends with an `unreachable`, also mark it as cold.
        mir::TerminatorKind::Unreachable => {
            cold_blocks.insert(bb);
            continue;
        }

        _ => {}
    }

    // If all successors of a BB are cold and there's at least one of them, mark this BB as cold
    let mut succ = terminator.successors();
    if let Some(first) = succ.next()
        && cold_blocks.contains(first)
        && succ.all(|s| cold_blocks.contains(s))
    {
        cold_blocks.insert(bb);
    }
}
```

Four structural properties follow directly from this source:

1. **Direct call-target restriction**: Only static `ty::FnDef(def_id, ..)` targets of `Call` or `TailCall` seed coldness. Indirect calls via `FnPtr` (even if the function pointer came from a `#[cold]` function), `Drop`, `Assert`, and `InlineAsm` never act as direct cold seeds.
2. **Zero-successor non-seed terminators**: `Return`, `UnwindResume`, `UnwindTerminate`, and diverging `Call`s (`target: None`, `unwind: Continue | Terminate | Unreachable`) without `COLD` yield `succ.next() == None`, so they are never marked cold unless a `COLD` direct call or `Unreachable` terminator sits in the block itself.
3. **Unwind cleanup inclusion**: `terminator.successors()` yields **both** the normal return target (`target`) and any `UnwindAction::Cleanup(cleanup_bb)`. Thus, a non-cold `Call` whose normal target goes to a cold block is *not* marked cold if its `Cleanup` landing pad ends in `UnwindResume`, `Return`, or a non-cold path; conversely, if a call is followed by `unreachable` on normal return and a `cold`/cleanup-to-`unreachable` pad, all successors are cold and the caller block becomes cold.
4. **Single-pass postorder vs. backward greatest fixed point**: `traversal::postorder(mir)` visits each reachable block **once**, inserting into `cold_blocks` in-place. On any **acyclic CFG**, postorder visits every successor before every predecessor, so single-pass universal backward propagation computes the exact set of blocks that inevitably hit a `#[cold]` call or `Unreachable`. However, on a **cyclic CFG** (`cw_5_cyclic_cold_loop`), when `traversal::postorder` visits a loop header `bb1` whose only successors are the cold exit `bb3` and the loop backedge `bb1` (not yet inserted into `cold_blocks`), `succ.all(|s| cold_blocks.contains(s))` evaluates `cold_blocks.contains(bb1) == false`. Consequently `bb1` stays unmarked, and the function's entry guard `if enter_loop { loop { ... if n == 0 { cold_path(); return 99; } } }` emits **no** `@llvm.expect.i1` and **no** `!prof` branch weights on the loop entry branch—verified empirically in `probe_results.json` (`cw_5_cyclic_cold_loop.entry_block_has_expect == false`, `entry_block_has_prof == false`), while the internal exit test inside the loop *does* receive `!{!"branch_weights", !"expected", i32 1, i32 2000}`.

---

### 2. Two-Way `@llvm.expect.i1` vs. Multi-Way `2000:1` `!prof !"branch_weights"` Lowering

Basis: source (`3ef0c22cd`: `compiler/rustc_codegen_ssa/src/mir/block.rs:427-565`, `compiler/rustc_codegen_ssa/src/traits/builder.rs:112-123`, `compiler/rustc_codegen_llvm/src/intrinsic.rs:997-1007`, `compiler/rustc_codegen_llvm/src/builder.rs:425-461`; `14210df0e`: `mir/block.rs:383-521`, `llvm/src/intrinsic.rs:1040-1050`, `llvm/src/builder.rs:364-400`) + execution (`probe_results.json` `part_a_cold_blocks_and_branch_weights`, `llvm23_baseline.json`).

`FunctionCx::codegen_switchint_terminator` (`rustc_codegen_ssa/src/mir/block.rs:427-566`) partitions `TerminatorKind::SwitchInt` into four lowering paths depending on branch arity, `-C opt-level`, and `self.cold_blocks`:

1. **1 explicit value + `otherwise` (`target_iter.len() == 1`, `block.rs:445-475`)**:
   - Computes `target_cold = self.cold_blocks.contains(target)` and `otherwise_cold = self.cold_blocks.contains(otherwise)`.
   - Sets `expect = if target_cold == otherwise_cold { None } else { Some(otherwise_cold) }` (inverting `expect.map(|e| !e)` when `switch_ty == bool && test_value == 0`).
   - Calls `bx.cond_br_with_expect(cond, then_llbb, else_llbb, expect)` (`traits/builder.rs:112-123`), which invokes `self.expect(cond, expect)` whenever `expect.is_some()`.
   - `rustc_codegen_llvm::Builder::expect` (`llvm/src/intrinsic.rs:997-1007`) gates on `self.cx.sess().opts.optimize != OptLevel::No`: if optimizing, it emits `call i1 @llvm.expect.i1(i1 %cond, i1 <expected>)`; at `-C opt-level=0`, it returns `cond` unmodified.

2. **Boolean/2-variant enum (`target_iter.len() == 2`, `otherwise` is `is_empty_unreachable()`, values `{0, 1}`, `block.rs:476-508`)**:
   - Explicitly checks `self.cx.sess().opts.optimize == OptLevel::No` (`block.rs:489`), setting `expected_cond_value = None` at `-O0`, and otherwise matching `(cold(true_bb), cold(false_bb))` (`(true, false) => Some(false)`, `(false, true) => Some(true)`, equal coldness `=> None`) before `cond_br_with_expect`.

3. **Unoptimized 2-arm + empty-unreachable non-`{0, 1}` switch (`optimize == OptLevel::No && target_iter.len() == 2`, `block.rs:509-532`)**:
   - Emits `bx.cond_br(cmp, ll1, ll2)` directly without calling `cond_br_with_expect` (FastISel compile-time optimization).

4. **General multi-way switch (`block.rs:533-565` & `llvm/src/builder.rs:425-461`)**:
   - Counts `cold_count` over explicit `targets.iter()`. If all reachable targets agree in coldness (ignoring an empty-unreachable `otherwise` via `(none_cold && (!otherwise_cold || otherwise_unreachable)) || (all_cold && (otherwise_cold || otherwise_unreachable))`, lines `541-542`), emits bare `bx.switch(...)` without weights.
   - Otherwise calls `bx.switch_with_weights(...)`. Inside `rustc_codegen_llvm/src/builder.rs:432-435`, if `optimize == OptLevel::No`, `switch_with_weights` falls back to bare `self.switch(...)`. When optimizing, it constructs `!prof` `!"branch_weights"` directly using `cold_weight = 1` and `hot_weight = 2000` (`else_is_cold` first, followed by each `(on_val, dest, is_cold)` case in order) — deliberately matching LLVM's `LowerExpectIntrinsic` `2000:1` ratio (`builder.rs:442-444`), **without** the `!"expected"` metadata tag inserted by LLVM's `LowerExpectIntrinsicPass`.

Empirical LLVM IR matrix across both `rustc 1.98.0-nightly` (LLVM `22.1.6`) and `rustc 1.102.0-nightly` (LLVM `23.1.5` baseline):

| Function | `opt2_prepass` (`-O2 -C no-prepopulate-passes`) | `opt2_full_nomerge` (`-O2 -Z merge-functions=disabled`) | `opt2_full` (`-O2`, default `MergeFunctions`) | `opt0` (`-O0`) |
| :--- | :--- | :--- | :--- | :--- |
| `cw_1_two_way_unlikely` | `call i1 @llvm.expect.i1(i1 %c, i1 false)`; no `cold_path` call | `!{"branch_weights", !"expected", i32 1, i32 2000}`; no `expect` | Identical definition (`select` + `!prof`) | No `cold_path`, no `expect`, no `!prof` |
| `cw_2_two_way_hint_cold_path` | `call @...hint::cold_path()` **present** + `call i1 @llvm.expect.i1(i1 %c, i1 false)` | `AlwaysInliner` erases `cold_path`; `!{"branch_weights", !"expected", i32 1, i32 2000}` | Collapsed to `alias` of `@cw_1_two_way_unlikely` | `AlwaysInliner` erases `cold_path`; no `expect`/`!prof` |
| `cw_2b_two_way_intrinsic_cold_path` | No `cold_path` call (`ZeroSized`); `call i1 @llvm.expect.i1(i1 %c, i1 false)` | `!{"branch_weights", !"expected", i32 1, i32 2000}`; no `expect` | Collapsed to `alias` of `@cw_1_two_way_unlikely` | No `cold_path`, no `expect`, no `!prof` |
| `cw_3_multi_way_switch_cold` | `call @...hint::cold_path()` **present**; no `expect`; `!{"branch_weights", i32 2000, i32 2000, i32 2000, i32 1, i32 2000}` | `AlwaysInliner` erases `cold_path`; `!{"branch_weights", i32 2000, i32 2000, i32 2000, i32 1, i32 2000}` (no `!"expected"`) | Same as `opt2_full_nomerge` | No `cold_path`, no `expect`, no `!prof` |
| `cw_4_likely_hot_branch` | `call i1 @llvm.expect.i1(i1 %c, i1 true)`; no `cold_path` call | `!{"branch_weights", !"expected", i32 2000, i32 1}` | Same as `opt2_full_nomerge` | No `cold_path`, no `expect`, no `!prof` |
| `cw_5_cyclic_cold_loop` | `start:` `br` has **no** `expect`; inner loop exit has `expect(false)` + `hint::cold_path` call | `start:` `br` has **no** `!prof`; inner loop exit has `!{"branch_weights", !"expected", i32 1, i32 2000}` | Same as `opt2_full_nomerge` | No `cold_path`, no `expect`, no `!prof` |

Notice two downstream consequences of this matrix:
- In `opt2_full`, LLVM's `MergeFunctionsPass` (enabled by default in `rustc`) deduplicates `cw_2_two_way_hint_cold_path` and `cw_2b_two_way_intrinsic_cold_path` into `@cw_2... = unnamed_addr alias ..., ptr @cw_1_two_way_unlikely` once `AlwaysInliner` erases `core::hint::cold_path()`!
- On 2-way `Select`-folded branches (`select i1 %c, i32 99, i32 -1, !prof !4`), `!prof` remains attached directly to the `select` instruction after `LowerExpectIntrinsicPass` + `SimplifyCFG`.

---

### 3. Per-Function `#[optimize(size|speed|none)]`, `#[cold]`, and `-C opt-level={0,2,s,z}` Attribute Derivation

Basis: source (`3ef0c22cd`: `compiler/rustc_codegen_llvm/src/attributes.rs:50-91,473-563`, `compiler/rustc_codegen_llvm/src/back/write.rs:124-144`, `compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs:20-68`; `14210df0e`: `attributes.rs:45-83,381-460`) + execution (`probe_results.json` `part_b_optimize_and_cold_attrs`, `llvm23_baseline.json`).

#### Attribute Precedence Equations in `rustc_codegen_llvm`

`rustc_codegen_llvm/src/attributes.rs` computes per-function LLVM optimization, inlining, and coldness attributes inside `llfn_attrs_from_instance` (`502-563` in `3ef0c22cd`; `406-460` in `14210df0e`):

```rust
// attributes.rs:475-493 (3ef0c22cd)
// Either attribute satisfies LLVM's combined size predicate, but the software pipeliner reads
// `optsize` alone, so a `z` build needs both.
match sess.opts.optimize {
    OptLevel::Size => {
        attrs.push(llvm::AttributeKind::OptimizeForSize.create_attr(cx.llcx));
    }
    OptLevel::SizeMin => {
        attrs.push(llvm::AttributeKind::MinSize.create_attr(cx.llcx));
        attrs.push(llvm::AttributeKind::OptimizeForSize.create_attr(cx.llcx));
    }
    _ => {}
}
```

```rust
// attributes.rs:513-529 (3ef0c22cd)
match codegen_fn_attrs.optimize {
    OptimizeAttr::Default => {
        to_add.extend(default_optimisation_attrs(cx, sess));
    }
    OptimizeAttr::DoNotOptimize => {
        to_add.push(llvm::AttributeKind::OptimizeNone.create_attr(cx.llcx));
    }
    OptimizeAttr::Size => {
        to_add.push(llvm::AttributeKind::MinSize.create_attr(cx.llcx));
        to_add.push(llvm::AttributeKind::OptimizeForSize.create_attr(cx.llcx));
    }
    OptimizeAttr::Speed => {}
}
```

And inside `inline_attr` (`attributes.rs:62-67`):

```rust
// `optnone` requires `noinline`
let inline = match (codegen_fn_attrs.inline, &codegen_fn_attrs.optimize) {
    (_, OptimizeAttr::DoNotOptimize) => InlineAttr::Never,
    (InlineAttr::None, _) if instance.def.requires_inline(tcx) => InlineAttr::Hint,
    (inline, _) => inline,
};
```

Finally, line `555-557` (`458-460` in `14210df0e`) independently appends `AttributeKind::Cold` (`cold`) whenever `codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::COLD)`.

#### Empirical Matrix Across `-C opt-level={0,2,s,z}` (`prepass` and `full`)

Table below records the exact LLVM IR attributes emitted on `x86_64-unknown-linux-gnu` before LLVM's optimization passes (`-C no-prepopulate-passes`, matching `rustc_codegen_llvm` emission directly) and after the full LLVM pass pipeline (`1.98.0-nightly` / LLVM `22.1.6`, matching `1.102.0-nightly` / LLVM `23.1.5` identically across all size/inline/cold tokens):

| Function / Rust Attribute | `-O0` (`prepass`) | `-O2` (`prepass` / `full`) | `-Os` (`prepass` / `full`) | `-Oz` (`prepass` / `full`) |
| :--- | :--- | :--- | :--- | :--- |
| **`oa_default`** (none) | `nonlazybind uwtable` | `prepass`: `nonlazybind uwtable`<br>`full`: `+ mustprogress nofree norecurse nosync nounwind willreturn memory(none)` | `prepass`: **`optsize`** `nonlazybind uwtable`<br>`full`: `optsize` + inferred IPO attrs | `prepass`: **`minsize optsize`** `nonlazybind uwtable`<br>`full`: `minsize optsize` + inferred IPO attrs |
| **`oa_size`** (`#[optimize(size)]`) | **`minsize optsize`** `nonlazybind uwtable` | **`minsize optsize`** (+ IPO attrs in `full`) | **`minsize optsize`** (+ IPO attrs in `full`) | **`minsize optsize`** (+ IPO attrs in `full`) |
| **`oa_speed`** (`#[optimize(speed)]`) | `nonlazybind uwtable` | `nonlazybind uwtable` (+ IPO attrs in `full`) | **Stripped** (`optsize` absent!) (+ IPO attrs in `full`) | **Stripped** (`minsize`, `optsize` absent!) (+ IPO attrs in `full`) |
| **`oa_none`** (`#[optimize(none)]`) | **`noinline optnone`** `nonlazybind uwtable` | **`noinline optnone`** (`full` IPO attrs **suppressed**!) | **`noinline optnone`** (`full` IPO attrs **suppressed**!) | **`noinline optnone`** (`full` IPO attrs **suppressed**!) |
| **`oa_inline_always_optnone`** (`#[inline(always)] #[optimize(none)]`) | **`noinline optnone`** (`alwaysinline` overridden) | **`noinline optnone`** (`alwaysinline` overridden) | **`noinline optnone`** (`alwaysinline` overridden) | **`noinline optnone`** (`alwaysinline` overridden) |
| **`oa_cold`** (`#[cold]`) | **`cold`** `nonlazybind uwtable` | **`cold`** (+ IPO attrs in `full`) | **`cold optsize`** (+ IPO attrs in `full`) | **`cold minsize optsize`** (+ IPO attrs in `full`) |

Key invariants demonstrated by both source and execution:
1. **`-Os` vs `-Oz` asymmetry**: `-C opt-level=s` emits **only** `optsize` (without `minsize`), whereas `-C opt-level=z` emits **both** `minsize` and `optsize` (`attributes.rs:480-489` explicit comment: *"the software pipeliner reads `optsize` alone, so a `z` build needs both"*).
2. **`#[optimize(size)]` semantic strength**: `#[optimize(size)]` maps to `minsize + optsize` (equivalent to `-Oz`, stronger than `-Os`), overriding `-O0`, `-O2`, `-O3`, and `-Os`.
3. **`#[optimize(speed)]` attribute stripping**: `#[optimize(speed)]` removes `optsize` and `minsize` even under `-Os` and `-Oz`, while the New Pass Manager pass builder still runs crate-level `PassBuilderOptLevel::{Os, Oz}` (`write.rs:141-142`) unless controlled per-function via function attributes in LLVM passes (`InlineCost`, `LoopVectorize`, `MachineOutliner`).
4. **`#[optimize(none)]` dual-attribute & IPO barrier**: `#[optimize(none)]` attaches `optnone`, forces `noinline` in `inline_attr` (even when combined with `#[inline(always)]`) to satisfy LLVM IR verification (`optnone requires noinline`), suppresses `optsize`/`minsize`, and inhibits LLVM's `PostOrderFunctionAttrsPass` from deducing `mustprogress nofree norecurse nosync nounwind willreturn memory(none)`.

---

### 4. `fn_can_unwind` 3-Gate Precedence, `AbortUnwindingCalls`, `-Z panic-in-drop=abort`, and `-C panic=immediate-abort`

Basis: normative (`rfc_2945_c_unwind.md:190-240`) + source (`3ef0c22cd`: `compiler/rustc_middle/src/ty/layout.rs:1321-1384`, `compiler/rustc_ty_utils/src/abi.rs:601-615`, `compiler/rustc_codegen_llvm/src/abi.rs:480-482,656-658`, `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:27-146`, `compiler/rustc_mir_transform/src/shim.rs:254-372`, `compiler/rustc_codegen_ssa/src/mir/block.rs:169-295,864-885,1695-1698,2245-2360`, `compiler/rustc_metadata/src/dependency_format.rs:416-501`, `library/core/src/ptr/mod.rs:818-845`; `14210df0e`: `layout.rs:1236-1297`, `llvm/src/abi.rs:442,603`, `core/src/ptr/mod.rs:808-845`) + execution (`probe_results.json` `part_c_nounwind_and_panic_strategies`, `llvm23_baseline.json`).

#### Exact Three-Gate Precedence of `layout::fn_can_unwind`

Both MIR's `AbortUnwindingCalls` pass (`abort_unwinding_calls.rs:62,99,103,106`) and `rustc_ty_utils::abi::fn_abi_new_uncached` (`ty_utils/src/abi.rs:601-615`, which writes `FnAbi::can_unwind`, directly controlling LLVM `nounwind` emission on function definitions at `llvm/src/abi.rs:480-482` and callsites at `llvm/src/abi.rs:656-658`) consult one shared predicate `rustc_middle::ty::layout::fn_can_unwind(tcx, fn_def_id, abi)` (`layout.rs:1321-1384` in `3ef0c22cd`; `1236-1297` in `14210df0e`):

```rust
pub fn fn_can_unwind(tcx: TyCtxt<'_>, fn_def_id: Option<DefId>, abi: ExternAbi) -> bool {
    if let Some(did) = fn_def_id {
        // Gate 1: Special attribute for functions which can't unwind (`#[rustc_nounwind]`).
        if tcx.codegen_fn_attrs(did).flags.contains(CodegenFnAttrFlags::NEVER_UNWIND) {
            return false;
        }

        // Gate 2: With `-C panic=abort`, all non-FFI functions are required to not unwind
        // (even `extern "C-unwind"` defined in Rust).
        if !tcx.sess.panic_strategy().unwinds() && !tcx.is_foreign_item(did) {
            return false;
        }

        // Gate 3: With `-Z panic-in-drop=abort`, `drop_glue` never unwinds.
        if !tcx.sess.opts.unstable_opts.panic_in_drop.unwinds()
            && tcx.is_lang_item(did, LangItem::DropGlue)
        {
            return false;
        }
    }

    // Gate 4: Otherwise unwinding follows ExternAbi and crate panic strategy.
    match abi {
        C { unwind } | System { unwind } | Cdecl { unwind } | Stdcall { unwind }
        | Fastcall { unwind } | Vectorcall { unwind } | Thiscall { unwind }
        | Aapcs { unwind } | Win64 { unwind } | SysV64 { unwind } => unwind,
        PtxKernel | Msp430Interrupt | X86Interrupt | GpuKernel | EfiApi
        | AvrInterrupt | AvrNonBlockingInterrupt | CmseNonSecureCall
        | CmseNonSecureEntry | Custom | RiscvInterruptM | RiscvInterruptS
        | RustInvalid | Swift | LlvmIntrinsic => false,
        Rust | RustCall | RustCold | RustPreserveNone | RustTail => {
            tcx.sess.panic_strategy().unwinds()
        }
    }
}
```

Notice how `rustc_ty_utils::abi.rs:603-613` populates `fn_def_id`: `Some(item)` for `InstanceKind::{Item, Intrinsic}`, **`Some(def_id)` for `InstanceKind::Shim(ShimKind::DropGlue(def_id, _))`** (specifically so Gate 3 recognizes `LangItem::DropGlue`!), and `None` for all other shims, virtual vtable slots, indirect `FnPtr` calls, and LLVM intrinsics.

#### Case A: Foreign vs. Rust-Defined `extern "C-unwind"` Under `-C panic=abort`

Under `-C panic=abort` (`!tcx.sess.panic_strategy().unwinds()`):
- A **Rust-defined** `pub extern "C-unwind" fn rust_def_extern_c_unwind()` has `Some(did)` with `tcx.is_foreign_item(did) == false`. Gate 2 returns `false`, attaching LLVM **`nounwind`** to `rust_def_extern_c_unwind`.
- A **foreign** `unsafe extern "C-unwind" { fn ext_c_unwind(); }` has `tcx.is_foreign_item(did) == true`. It bypasses Gate 2 and reaches Gate 4 (`C { unwind: true } => true`), so **`ext_c_unwind` has NO `nounwind` attribute** (`foreign_c_unwind_nounwind: false`)!
- Inside `caller_of_foreign_c_unwind(mut d: LoudDrop)`, `body_can_unwind == false` (Caller receives **`nounwind`** under `-C panic=abort`), yet `call_can_unwind == true` for `ext_c_unwind()`! Therefore `AbortUnwindingCalls` preserves `d`'s cleanup block (`LoudDrop::drop`) and rewrites its `UnwindResume` to `UnwindTerminate(UnwindTerminateReason::Abi)` (`abort_unwinding_calls.rs:81-83,124-135`), and `rustc_codegen_ssa` (`block.rs:218-286`) lowers the foreign call to **`invoke void @ext_c_unwind()`** landing in the drop cleanup block -> `terminate` (`panic_cannot_unwind`) even though `caller_of_foreign_c_unwind` itself carries `nounwind`! By contrast, calling `unsafe extern "C" { fn ext_c(); }` yields `call_can_unwind == false`, emitting a plain `call` with `UnwindAction::Unreachable`.

#### Case B: `-Z panic-in-drop=abort` `LangItem::DropGlue` vs. Public `core::ptr::drop_in_place` Split

In `library/core/src/ptr/mod.rs:818-845`:
- Public `core::ptr::drop_in_place<T: PointeeSized>(to_drop: *mut T)` carries `#[inline(always)]` and `#[rustc_diagnostic_item = "ptr_drop_in_place"]` (it is **not** `LangItem::DropGlue`), and delegates to `drop_glue(&mut *to_drop)`.
- Crate-private `pub(crate) const unsafe fn drop_glue<T: PointeeSized>(_: &mut T)` carries `#[lang = "drop_glue"]` (`LangItem::DropGlue`), and its MIR body is replaced by `compiler/rustc_mir_transform/src/shim.rs:258-372` (`build_drop_shim`), which initializes `Unwind::To(resume_block)` (`TerminatorKind::UnwindResume`) so drops can unwind by default.

When compiling under **`-C panic=unwind -Z panic-in-drop=abort`**:
1. **LLVM `nounwind` split**: In `core::ptr::drop_glue::<LoudDrop>`, Gate 3 sees `tcx.is_lang_item(did, LangItem::DropGlue) == true`, returning `fn_can_unwind == false` (`nounwind` attached, `lang_drop_glue_nounwind: true`). Inside `build_drop_shim`'s MIR, `AbortUnwindingCalls` computes `body_can_unwind = false` while `<LoudDrop as Drop>::drop` still has `call_can_unwind = true` (`Drop::drop` is `ExternAbi::Rust` under `panic=unwind`, not `LangItem::DropGlue`), emitting **`invoke void @<LoudDrop as Drop>::drop(...)`** unwinding to a `call void @core::panicking::panic_cannot_unwind()` terminate pad (`drop_glue_has_invoke_drop: true`, `drop_glue_calls_panic_cannot_unwind: true`).
2. Public `core::ptr::drop_in_place::<LoudDrop>` fails Gate 3 (`did != LangItem::DropGlue`), so `fn_can_unwind` returns `true` and its LLVM IR declaration/definition has **no** `nounwind` attribute (`public_drop_in_place_nounwind: false`)—though once `#[inline(always)]` inlines `drop_in_place` at `-O2`, callers call `drop_glue` (`nounwind`) directly.
3. **Crate-link enforcement (`dependency_format.rs:489-500`) vs. native cross-object abort**: Attempting to compile `--crate-type=bin` directly with `-C panic=unwind -Z panic-in-drop=abort` against prebuilt `std` fails in `dependency_format::verify_ok` across all 17 prebuilt sysroot crates (`error: the crate 'std' is compiled with the panic-in-drop strategy 'unwind' which is incompatible with this crate's strategy of 'abort'`). However, compiling `drop_mod.o` (`--emit=obj -C panic=unwind -Z panic-in-drop=abort`) and linking it into a `-C panic=unwind` harness executing `std::panic::catch_unwind(|| unsafe { trigger_drop_panic(); })` proves the runtime boundary: under `-C panic=unwind`, `catch_unwind` catches the unwinding drop (`rc = 0`, stdout `CAUGHT_DROP_PANIC`); with `drop_mod` compiled under `-Z panic-in-drop=abort`, `core::ptr::drop_glue::<LoudDrop>` intercepts the unwind and aborts via `core::panicking::panic_cannot_unwind` (`SIGABRT`, `rc = -6`) despite the enclosing `catch_unwind`!

| Symbol / Property | `panic=unwind` | `panic=abort` | `panic=unwind -Z panic-in-drop=abort` |
| :--- | :--- | :--- | :--- |
| `unsafe extern "C" { fn ext_c(); }` (`nounwind`) | **`true`** | **`true`** | **`true`** |
| `unsafe extern "C-unwind" { fn ext_c_unwind(); }` (`nounwind`) | **`false`** | **`false`** | **`false`** |
| `pub extern "C" fn rust_def_extern_c()` (`nounwind`) | **`true`** | **`true`** | **`true`** |
| `pub extern "C-unwind" fn rust_def_extern_c_unwind()` (`nounwind`) | **`false`** | **`true`** | **`false`** |
| `core::ptr::drop_glue::<LoudDrop>` (`nounwind`) | **`false`** | **`true`** | **`true`** (internal `invoke` -> `panic_cannot_unwind`) |
| `core::ptr::drop_in_place::<LoudDrop>` (`nounwind`) | **`false`** | **`true`** | **`false`** |
| `caller_of_foreign_c_unwind` (`nounwind`) | **`false`** | **`true`** | **`false`** |
| `caller_of_foreign_c_unwind` uses `invoke @ext_c_unwind` | **`true`** | **`true`** | **`true`** |

#### Case C: `-C panic=immediate-abort` Against Prebuilt `core`

Under `-Z unstable-options -C panic=immediate-abort`:
- `PanicStrategy::ImmediateAbort.unwinds()` returns `false`, so Gate 2 marks local Rust functions `nounwind` (`imm_bounds_index` has `nounwind`).
- However, compiling `#![no_std]` `--crate-type=lib --emit=llvm-ir` (`imm_bounds_index`) against prebuilt `core` **does not** emit `@llvm.trap()` (`has_llvm_trap == false`); instead it emits:
  ```llvm
  tail call void @core::panicking::panic_bounds_check(...) #2
  unreachable
  ```
  because prebuilt `core` in the sysroot was compiled under `PanicStrategy::Unwind` (`#[inline(never)]` on `panic_bounds_check`), and `rustc` emits calls to `core::panicking::panic_bounds_check` whenever `panic_immediate_abort` cannot inline/rewrite prebuilt non-`ImmediateAbort` core panic functions without `-Z build-std`.
- When linking any final binary (`--crate-type=bin`), `dependency_format::verify_ok` (`dependency_format.rs:418-438`) checks `tcx.required_panic_strategy(cnum) != Some(PanicStrategy::ImmediateAbort)`, immediately triggering a single fatal error at line `430`: `IncompatibleWithImmediateAbortCore` (`error: the crate 'core' was compiled with a panic strategy which is incompatible with 'immediate-abort'`).

---

### 5. Mechanized Lean `v4.34.1` Formalization and Counterexamples

Basis: derived + execution (`support/ColdBlocksAndNoUnwindSoundness.lean`, `support/ColdBlocksAndNoUnwindAudit.lean`, `support/lean_check_receipt.json`).

`support/ColdBlocksAndNoUnwindSoundness.lean` (`1,277` lines, `53,194` bytes, SHA-256 `6a8cc38fbf9a6bf40169d9522c3be7d561716c9ae4cb7c2c98d21310478475e1`) compiles in Lean `v4.34.1` with zero imports (`imports: []`), zero errors, zero warnings, and zero unsafe helpers or forbidden tactics, and audits to `1,313` constants (`651` theorems, `530` definitions, `0` violations) using only `[propext, Quot.sound]`:

| Theorem / Counterexample (`ColdBlocksAndNoUnwind.*`) | Formal Statement Summary | Axioms Used |
| :--- | :--- | :--- |
| `findColdBlocksPass_sound` | For arbitrary (possibly cyclic) `cfg` and arbitrary block list `order`, `findColdBlocksPass cfg order bb = true → MustHitColdOrUnreachable cfg bb` (proved via insertion-rank witness `RankSound` + `InevitableCold` least-fixed-point induction). | `propext`, `Quot.sound` |
| `findColdBlocks_sound_and_dag_complete` | Combines unconditional CFG soundness with `IsPostorderDAG cfg order depth → (MustHitColdOrUnreachable cfg bb ↔ findColdBlocksPass cfg order bb = true)`. | `propext`, `Quot.sound` |
| `coldPath_erasure_preserves_behavior` | Operational `execSsaProg` equivalence proving hint erasure (`eraseStmt`, `stripTermHints`), `opt2_prepass` lowering (`lowerStmtPrepass`, `attachSwitchProf`), and `opt2_full` lowering (`lowerStmtFull`, `attachExpectProf`) preserve `ExecOutcome` across all CFGs, states, and fuel bounds. | `propext` |
| `optimize_attr_s_vs_z_default` & `optimize_attr_size_speed_none_overrides` | Proves `deriveLlvmFnAttrs` produces `optsize` alone at `-Os`, `minsize + optsize` at `-Oz` and `#[optimize(size)]`, `{}` size attrs at `#[optimize(speed)]`, `noinline + optnone` at `#[optimize(none)]` (overriding `InlineAttr::always`), and orthogonal `cold` flags. | `propext` |
| `fnCanUnwind_precedence_characterization` | Exact characterization of all 4 gates in `fn_can_unwind`, including `rustFn`/`C-unwind` vs `foreignItem`/`C-unwind` under `panic=abort`, `langDropGlue` vs `publicDropInPlace` under `panic=unwind -Z panic-in-drop=abort`, and `rustTail` vs `interrupt`. | `propext` |
| `abortUnwindingCalls_sound_for_call` & `fnCanUnwind_nounwind_soundness` | Proves callsite soundness after `abortUnwindingEdge`: when callees satisfy their `fnCanUnwind` contract and pre-lowering edges are valid (`origAction ≠ .unreachable`), lowered frames never hit `.ub .nounwindViolated` or `.ub .unreachableUnwind`, `nounwind` callers never exit with `.unwound` (aborting via `.abortedTerminateAbi`), and `checkCrateDagLink` rejects mismatched prebuilt `core` strategies. | `propext` |
| `ce1_single_pass_postorder_misses_cyclic_cold_loop_header` | Concrete 4-block cyclic CFG (`cw5Cfg`, order `[2, 3, 1, 0]`) where `MustHitColdOrUnreachable cw5Cfg 1` and `gfpColdBlocks cw5Cfg 4 1 = true` hold, `findColdBlocksPass ... 3 = true`, yet `findColdBlocksPass ... 1 = false`. | `propext` |
| `ce2_marking_foreign_c_unwind_nounwind_under_panic_abort_skips_terminate_pad` | Concrete witness showing that omitting `!isForeign` in Gate 2 turns `abortUnwindingEdge` into `UnwindAction::Unreachable` without `invoke`, causing `.ub .nounwindViolated` on foreign unwind, whereas actual `fnCanUnwind` emits `invoke` and yields `.abortedTerminateAbi`. | `propext` |
| `ce3_conflating_public_drop_in_place_with_lang_drop_glue_under_panic_in_drop_abort` | Concrete witness showing `hasLlvmNoUnwind .unwind .abort (some (.langDropGlue false)) .rust = true` vs `publicDropInPlace = false`, that `drop_glue` lowers `Drop::drop` to `.abortedTerminateAbi`, and that assigning `nounwind` without `AbortUnwindingCalls` yields `.ub .nounwindViolated`. | `propext` |

---

### 6. Integration Boundary with Verified MIR Consumers (`joshlf/anneal`)

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/Trusted/MirAst.lean:620-663,742-795`, `trusted/lean/Trusted/MirSemantics.lean:174-182`, `trusted/rustc-capture/src/driver.rs:25,75-85`) + derived.

1. **Hint & attribute transparency in `Trusted.MirAst`**: `Trusted.MirAst` sits strictly downstream of `Runtime(PostCleanup)` MIR and captures neither `find_cold_blocks`, LLVM `!prof` branch weights, nor `#[optimize(...)]` / `#[cold]` function attributes (`MirAst.lean` executes `StatementKind::{assign, storageLive, storageDead, nop}` and `TerminatorKind::{goto, switchInt, return_, unreachable, unwindResume, assert, call}` over abstract `MirSemantics`). By `coldPath_erasure_preserves_behavior`, ignoring `core::hint::cold_path`, `core::intrinsics::{cold_path, likely, unlikely}`, `!prof` metadata, and `#[optimize]`/`#[cold]` is **sound** for functional/UB correctness: none of them alter MIR operational semantics (though `core::hint::cold_path()` remains a direct `TerminatorKind::Call` in MIR unless inlined/erased, so any call to `core::hint::cold_path` must be treated as a `#[rustc_nounwind]` unit-returning no-op or `.unsupported` fail-closed).
2. **Unwinding & `Drop` boundary**: `Trusted.MirAst` currently routes `TerminatorKind::{UnwindTerminate, Drop, TailCall, InlineAsm}` and indirect `Call` to `.unsupported` (`MirAst.lean:782-784`) and checks `anneal-rustc-capture` only up to `after_analysis` (`driver.rs:75-84`). Any future extension supporting FFI calls (`#[cold]`/`C-unwind`), `Drop` shims, or `UnwindAction` must consume the post-`AbortUnwindingCalls` MIR unwinding edge and the 3-gate `fn_can_unwind` predicate (not surface ABI names alone), because under `-C panic=abort` and `-Z panic-in-drop=abort` identical ABI signatures (`extern "C-unwind"`, `drop_in_place` vs `drop_glue`) have opposite unwinding contracts across foreign vs. Rust items and `LangItem::DropGlue` vs. public wrappers.

## Boundaries

- **Known not to apply**:
  - Single-pass postorder `find_cold_blocks` completeness does **not** apply to cyclic cold loops (`cw_5_cyclic_cold_loop` empirically and `ce1` formally).
  - `@llvm.expect.i1` and `!prof !"branch_weights"` emission does **not** apply under `-C opt-level=0` (`rustc_codegen_llvm/src/intrinsic.rs:998`, `builder.rs:432`, `block.rs:489,509`).
  - Gate 2 (`!panic_strategy().unwinds()`) `nounwind` attribution does **not** apply to foreign `unsafe extern "C-unwind"` declarations (`tcx.is_foreign_item(did) == true`, proved in `ce2`).
  - Gate 3 (`!panic_in_drop.unwinds()`) `nounwind` attribution does **not** apply to public `core::ptr::drop_in_place::<T>` (`did != LangItem::DropGlue`, proved in `ce3`), and direct `--crate-type=bin` linking with `-Z panic-in-drop=abort` or `-C panic=immediate-abort` against prebuilt `std`/`core` is rejected by `dependency_format::verify_ok`.
  - `#![feature(optimize_attribute)]` is required on `14210df0e` (`1.98.0-nightly`) and becomes unnecessary on `3ef0c22cd` (`1.102.0-nightly` where `OptimizeParser` has `AttributeStability::Stable`).
- **Not examined (empirical execution)**:
  - Live execution of `rustc 1.102.0-nightly (3ef0c22cd)` beyond the preserved `support/probe_output/llvm23_baseline.json` specimen (live commands in this environment executed `rustc 1.98.0-nightly` / LLVM `22.1.6` while cross-checking all `3ef0c22cd` source files directly).
  - Non-`x86_64` codegen targets (`aarch64`, `wasm32` `exception-handling`, Windows MSVC SEH `catchswitch` / `cp_terminate` funclets in `block.rs:2286-2360`) and `rustc_codegen_cranelift` / `rustc_codegen_gcc` backends.
  - Rebuilding `core` / `std` from source via `-Z build-std` under `-C panic=immediate-abort` or `-Z panic-in-drop=abort` (where `panic_bounds_check` and `std` drop glues are themselves compiled with matching panic strategies, enabling inlining/trap lowering of `ImmediateAbort` panics).
  - Downstream LLVM IR optimization consumers beyond `AlwaysInliner` / `LowerExpectIntrinsic` / `MergeFunctions` / `PostOrderFunctionAttrs` (e.g., exact MachineOutliner / SoftwarePipeliner thresholds on `minsize` vs `optsize` loops).
- **Model boundaries (Lean mechanization)**:
  - `support/ColdBlocksAndNoUnwindSoundness.lean` models CFG postorder coldness, straight-line/branching SSA execution, attribute derivation, and single-callsite `AbortUnwindingCalls` frame outcomes constructively (`List` / `Nat` / algebraic types), rather than extracting `rustc`'s Rust compiler data structures or modeling LLVM's full optimization pass pipeline or multi-frame DWARF/Itanium EH tables.
- **Unsupported**:
  - `optnone` (`#[optimize(none)]`) paired with forced inlining (`#[inline(always)]`) is rejected by LLVM's IR verifier unless `noinline` accompanies `optnone`; `rustc` prevents this combination by overriding `InlineAttr::Never` in `attributes.rs:64`.

## Evidence

### 1. Pinned Upstream Sources (`support/pin_receipt.json`)

Every subject in `REPORT.json` (`observed_at: 2026-11-22`) and all 39 cited files were verified via GitHub API and `raw.githubusercontent.com` (`passed: true` in `support/pin_receipt.json`):

| Repository | Verified 40-Hex Commit | Primary Files & Line Ranges Inspected |
| :--- | :--- | :--- |
| `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_codegen_ssa/src/mir/mod.rs` (`264, 667-712`); `block.rs` (`169-295, 427-566, 864-885, 1695-1698, 2245-2360`); `intrinsic.rs` (`125, 592-595`); `traits/builder.rs` (`112-123`); `compiler/rustc_codegen_llvm/src/builder.rs` (`425-461`); `intrinsic.rs` (`997-1007`); `attributes.rs` (`50-91, 473-563`); `abi.rs` (`477-495, 653-659`); `back/write.rs` (`124-144`); `compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs` (`20-68`); `compiler/rustc_mir_transform/src/check_inline.rs` (`1-85`); `inline.rs` (`46-61, 290-440`); `abort_unwinding_calls.rs` (`27-146`); `shim.rs` (`254-372`); `compiler/rustc_middle/src/ty/layout.rs` (`1321-1384`); `middle/codegen_fn_attrs.rs` (`15-150`); `compiler/rustc_ty_utils/src/abi.rs` (`601-615`); `compiler/rustc_metadata/src/dependency_format.rs` (`416-501`); `library/core/src/intrinsics/mod.rs` (`676-724`); `hint.rs` (`778-786`); `ptr/mod.rs` (`818-845`) |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_codegen_ssa/src/mir/mod.rs` (`593-638`); `block.rs` (`383-521`); `intrinsic.rs` (`587-590`); `compiler/rustc_codegen_llvm/src/builder.rs` (`364-400`); `intrinsic.rs` (`1040-1050`); `attributes.rs` (`45-83, 381-460`); `abi.rs` (`442, 603`); `compiler/rustc_middle/src/ty/layout.rs` (`1236-1297`); `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs` (`26-144`); `compiler/rustc_metadata/src/dependency_format.rs` (`69-70, 418-500`); `library/core/src/intrinsics/mod.rs` (`419-468`); `hint.rs` (`784`); `ptr/mod.rs` (`808-845`) |
| `rust-lang/rfcs` | `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | `text/2945-c-unwind-abi.md` (`190-275`, ABI boundary unwinding table under `panic=unwind` and `panic=abort`) |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean` (`560-810`), `Trusted/MirSemantics.lean` (`140-260`), `trusted/audit/TrustedBoundary.lean` (`1-120`), `trusted/rustc-capture/src/driver.rs` (`1-120`) |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | Lean `v4.34.1` compiler/kernel (`--version` match confirmed in `support/lean_check_receipt.json`) |

### 2. Empirical `rustc` Probe & LLVM 23.1.5 Baseline (`support/probe_cold_blocks_optimize_and_nounwind.py`)

- **Executed toolchain (`2026-11-22`)**: `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `LLVM 22.1.6` on `x86_64-unknown-linux-gnu`.
- **Recorded outputs**: `support/probe_output/probe_results.json` (`all_checks_passed: true`, `20/20` checks passing including `parity_with_llvm23_baseline_part_a`, `parity_with_llvm23_baseline_part_b`, `parity_with_llvm23_baseline_part_c`) and preserved `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` / `LLVM 23.1.5` baseline `support/probe_output/llvm23_baseline.json`.
- **Verified artifacts inside `probe_results.json`**: MIR `Inline` pass dump assertions (`mir_inline_check`), `opt2_prepass`/`opt2_full`/`opt2_full_nomerge`/`opt0` LLVM IR extractions for all 6 Part A functions, `prepass`/`full` attribute extractions across `-O{0,2,s,z}` for all 6 Part B functions, `nounwind` and `invoke` IR matrix for `panic_unwind`/`panic_abort`/`panic_unwind_drop_abort`, cross-object `SIGABRT` (`drop_glue` -> `panic_cannot_unwind`) and `IncompatiblePanicInDropStrategy` link failure, and `panic=immediate-abort` `#![no_std]` library IR + `IncompatibleWithImmediateAbortCore` link failure.

### 3. Lean `v4.34.1` Verification & Kernel Audit (`support/lean_check_receipt.json`)

- **Script & command**: `support/check_lean.py` compiles `support/ColdBlocksAndNoUnwindSoundness.lean` (`1,277` lines, `53,194` bytes, SHA-256 `6a8cc38fbf9a6bf40169d9522c3be7d561716c9ae4cb7c2c98d21310478475e1`) with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, scans all 13 forbidden whole-word tokens (`0` hits), and executes `support/ColdBlocksAndNoUnwindAudit.lean` over the compiled `.olean`.
- **Results (`2026-11-22`, `passed: true`)**: Compile `exit_code = 0`, `errors = 0`, `warnings = 0`, `olean_bytes = 4581904`; Audit `exit_code = 0`, `constants = 1313`, `theorems = 651`, `theorems_without_axioms = 483`, `definitions = 530`, `inductive_types = 24`, `constructors = 84`, `recursors = 24`, `violations = 0`, `axioms_used = ["propext", "Quot.sound"]` (`#print axioms` confirms zero `Classical.choice`, `sorryAx`, or `Lean.ofReduceBool` across all theorems and counterexamples).

## Revalidation

To verify whether a newer `rust-lang/rust`, `joshlf/anneal`, or `leanprover/lean4` revision preserves all findings:

1. **Rerun the empirical `rustc` probe suite** (executes all 20 MIR, LLVM IR, native `SIGABRT`, and linker diagnostic checks in ~5 seconds; requires nightly `rustc`):
   ```console
   cd reports/rustc-cold-block-propagation-branch-weights-optimize-attrs-and-nounwind-derivation/support
   python3 probe_cold_blocks_optimize_and_nounwind.py --rustc rustc --out /tmp/probe_reval
   ```
   Confirm `Probe complete: 20/20 checks passed.` and `"all_checks_passed": true` in `/tmp/probe_reval/probe_results.json`.

2. **Re-verify and kernel-audit the Lean formalization** (requires Lean `v4.34.1`):
   ```console
   python3 reports/rustc-cold-block-propagation-branch-weights-optimize-attrs-and-nounwind-derivation/support/check_lean.py
   ```
   (Pass `--wrap ...` if running inside a cgroup wrapper.) Confirm `"passed": true`, `"errors": 0`, `"warnings": 0`, and `"violations": 0`.

3. **Diff the narrow upstream compiler hooks** on any newer `rust-lang/rust` commit:
   - Check `compiler/rustc_codegen_ssa/src/mir/mod.rs` (`find_cold_blocks`) for fixed-point iteration vs single-pass `traversal::postorder` changes, and `compiler/rustc_mir_transform/src/check_inline.rs` for `CodegenFnAttrFlags::COLD` inlining rules.
   - Check `compiler/rustc_codegen_ssa/src/mir/block.rs` (`codegen_switchint_terminator`) and `compiler/rustc_codegen_llvm/src/builder.rs` (`switch_with_weights`) for changes to `2000:1` weights, `@llvm.expect`, or `OptLevel::No` gating.
   - Check `compiler/rustc_codegen_llvm/src/attributes.rs` (`default_optimisation_attrs`, `inline_attr`, `llfn_attrs_from_instance`) and `compiler/rustc_middle/src/ty/layout.rs` (`fn_can_unwind`) + `compiler/rustc_metadata/src/dependency_format.rs` (`IncompatibleWithImmediateAbortCore`, `IncompatiblePanicInDropStrategy`) for any change to attribute precedence or `LangItem::DropGlue` / foreign `C-unwind` handling.

4. **Validate corpus metadata and report structure**:
   ```console
   python3 tools/reference.py catalog
   python3 tools/reference.py check
   ```
