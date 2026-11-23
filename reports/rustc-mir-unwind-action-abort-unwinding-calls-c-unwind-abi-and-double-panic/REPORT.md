# rustc MIR UnwindAction, AbortUnwindingCalls, extern "C-unwind" ABI Boundaries, Double-Panic InCleanup, -Cpanic=abort Erasure, and LLVM nounwind Lowering

## Summary

In `rustc` Mid-level Intermediate Representation (MIR), every unwinding edge and cleanup boundary is governed by a strict four-state continuation algebra (`UnwindAction::{Continue, Unreachable, Terminate(UnwindTerminateReason), Cleanup(BasicBlock)}`) paired with a context-sensitive ABI capability predicate (`rustc_middle::ty::layout::fn_can_unwind`) and enforced during runtime MIR lowering by the mandatory `AbortUnwindingCalls` pass (`PassPolicy::Required`).

The core operational invariants across MIR construction, transformation, LLVM IR lowering, and native execution are:

1. **Non-unwinding ABI barrier (`extern "C"` vs. `extern "C-unwind"`):** Under `-C panic=unwind`, unwinding out of a non-unwinding callee or ABI (including `extern "C"`) is never left as implicit LLVM `nounwind` undefined behavior. `AbortUnwindingCalls` rewrites `UnwindAction::Continue` to `UnwindAction::Terminate(UnwindTerminateReason::Abi)` and rewrites cleanup exit `TerminatorKind::UnwindResume` terminators to `TerminatorKind::UnwindTerminate(UnwindTerminateReason::Abi)`. Local cleanups (`Drop` guards) strictly execute **before** the barrier fires `core::panicking::panic_cannot_unwind()` (`SIGABRT`, exit status `-6` on Linux).
2. **Asymmetric `-C panic=abort` foreign and indirect `extern "C-unwind"` semantics:** Under `-C panic=abort`, `fn_can_unwind` returns `false` for *all locally defined* items regardless of ABI—including locally defined `extern "C-unwind" fn` functions—causing `AbortUnwindingCalls` to turn their internal unwind edges into `UnwindAction::Unreachable`, drop dead cleanup blocks via `remove_dead_blocks`, and emit LLVM `nounwind` + plain `call`. By contrast, **`extern "C-unwind"` foreign declarations (`tcx.is_foreign_item(did) == true`) and indirect `extern "C-unwind"` function pointers (`fn_def_id == None`) STILL return `fn_can_unwind == true`** under `-C panic=abort`. Furthermore, because `RemoveNoopLandingPads` uses `PassPolicy::optional(ctx.panic_strategy().unwinds())` and is therefore skipped under `-C panic=abort`, calls to foreign or indirect `extern "C-unwind"` targets under `-C panic=abort` keep an `invoke ... unwind label %cleanup` edge routing into `bb (cleanup): terminate(abi)` (`landingpad { ptr, i32 } cleanup` -> `panic_cannot_unwind()`), rather than directly converting the callsite unwind action into `Terminate(Abi)` (`filter [0 x ptr] zeroinitializer`).
3. **Double-panic cleanup termination (`InCleanup`):** Cleanup drops created in `rustc_mir_build::builder::scope` and `ElaborateDrops` attach `UnwindAction::Terminate(UnwindTerminateReason::InCleanup)` (`panic_in_cleanup`) rather than `Continue` or `Cleanup(_)`. `AbortUnwindingCalls` explicitly skips cleanup blocks (`if block.is_cleanup { continue; }`) when rewriting unwind actions, preserving double-panic abort semantics in cleanup scopes while rewriting outer normal edges to `Unreachable` when `-C panic=abort` or `-Z panic-in-drop=abort` makes unwind paths unreachable.
4. **LLVM `nounwind` soundness and post-monomorphization cleanup skipping:** `rustc_codegen_llvm::abi` attaches `nounwind` (`AttributeKind::NoUnwind`) to both function definitions and callsites iff `!fn_abi.can_unwind`. Under LLVM `LangRef`, raising an exception out of a `nounwind` function is immediate undefined behavior. `rustc_codegen_ssa::mir::block` preserves safety by lowering every `UnwindAction::Cleanup(bb)` (unless identified post-monomorphization by `fx.nop_landing_pads`) and every `UnwindAction::Terminate(reason)` to `invoke` (except SEH `InCleanup`, where native Windows SEH enforces double-fault termination).
5. **Downstream `joshlf/anneal` representation status and mechanized proof:** At `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst.UnwindAction` erases `UnwindTerminateReason`, while `MirSemantics` and `Correspondence` map calls, drops, unwind terminations, and `UnwindResume` to `.unsupported` / sentinel fail-closed behavior in single-frame execution. The standalone Lean `v4.34.1` development (`support/MirUnwindActionAbortUnwindingSoundness.lean`, `6,181` lines, `322` theorems, pure `[propext, Quot.sound]`, `0` `_unsafe_rec` constants) mechanizes multi-frame MIR and LLVM semantics and proves:
   - `abortUnwindingCalls_exact_soundness`: every non-unwinding boundary converts unwinds to deterministic `Terminate(Abi)` aborts with zero UB;
   - `double_panic_inCleanup_termination`: nested cleanup panics halt deterministically in `InCleanup` via a strict cleanup-depth invariant;
   - `eraseDeadCleanup_preserves_WF_and_exec`: `-C panic=abort` leaves cleanup blocks unreachable and cleanup-block erasure preserves well-formedness and semantics;
   - `llvm_nounwind_never_escapes` and `mir_llvm_lockstep_sim`: MIR and lowered LLVM IR execute in lockstep with zero UB and zero unwinding escape across `nounwind` functions.

## Applicability

This report characterizes the design, invariants, compiler pass interactions, IR lowering, runtime execution, and mechanized soundness properties across the five pinned subjects recorded in `REPORT.json`:

1. **`rust-lang/rust` (`960ba7cf7e8666ecb449402ca82b6e9e631bd227`)**: Primary upstream source inspection across `rustc_middle`, `rustc_mir_build`, `rustc_mir_transform`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, and `core::panicking`.
2. **`rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, toolchain `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, host `x86_64-unknown-linux-gnu`, LLVM `22.1.6`)**: Both live empirical execution (MIR dumps via `-Zdump-mir=AbortUnwindingCalls`, unoptimized LLVM IR via `--emit=llvm-ir -Copt-level=0 -Cdebuginfo=0`, and five native Linux binary executions) and matching upstream source diffing against `960ba7cf7e8666ecb449402ca82b6e9e631bd227`.
3. **`llvm/llvm-project` (`510c32aa35634c7298181857d7bcd92ca9457d1f`)**: Normative LLVM IR attribute definition (`Attributes.td`), exception handling documentation (`ExceptionHandling.md`), and `nounwind` undefined-behavior rules (`LangRef.md`) interpreting the emitted LLVM IR.
4. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)**: Interpreted against the upstream compiler invariants to document exact MIR AST, operational semantics, and Miri-correspondence gaps for `UnwindAction` and multi-frame unwinding. Note that `joshlf/anneal`'s own source comments cite an earlier compiler snapshot (`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and driver version (`1.98.0-nightly (f8a08b688 2026-05-30)`).
5. **`leanprover/lean4` (`v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`)**: Standalone kernel checker validating all `322` theorems and `680` definitions in `support/MirUnwindActionAbortUnwindingSoundness.lean` strictly over `Init` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Version Comparison: `rust-lang/rust` `14210df0e2` vs. `960ba7cf7e`

Direct source comparison across all audited files shows that unwinding semantics, pass ordering, validation rules, and LLVM lowering remain **semantically invariant** between `14210df0e2` and `960ba7cf7e`, with only localized refactorings and variant additions:

| Component | `14210df0e2` (`1.98.0-nightly`) | `960ba7cf7e` (`main`) | Semantic impact on unwinding |
| :--- | :--- | :--- | :--- |
| `AbortUnwindingCalls` pass gate | `fn is_required(&self) -> bool { true }` | `fn policy(&self, _) -> PassPolicy { PassPolicy::Required }` | Identical mandatory scheduling |
| `AbortUnwindingCalls` ABI query | `body_ty.fn_sig(tcx).abi()`, `ty.fn_sig(tcx).abi()` | `body_ty.fn_sig_abi(tcx)`, `ty.fn_sig_abi(tcx)` | Equivalent ABI extraction |
| `layout::fn_can_unwind` | `Unadjusted => false`; `Rust \| RustCall \| RustCold \| RustPreserveNone` (`lines 1236–1297`) | `LlvmIntrinsic => false`; adds `RustTail` (`lines 1358–1421`) | Identical `-C panic=abort` and `C`/`C-unwind` lattice |
| `TerminatorKind::Drop` | Has `async_fut: Option<Local>` field in `builder/scope.rs` | `async_fut` field removed (`builder/scope.rs:422-429`) | No change to `unwind: UnwindAction::Terminate(InCleanup)` |
| `core::panicking` immediate abort | Calls `super::intrinsics::abort()` when `cfg!(panic = "immediate-abort")` | Calls `super::intrinsics::abort_immediate()` (`panicking.rs:62, 103`); `block.rs:2398` checks `is_call_from_compiler_builtins_to_upstream_monomorphization` | Same non-unwinding abort intent; runtime immediate-abort targets not empirically probed |

### Configuration and Target Scope

- **Empirically verified:** Rust Edition 2024 on `x86_64-unknown-linux-gnu` (Itanium DWARF exception handling) under `-C panic=unwind`, `-C panic=abort`, `-C panic=abort -Zpanic_abort_tests`, `-C opt-level=0`, `-Z mir-opt-level=0`, `-Z dump-mir=AbortUnwindingCalls`, and `--emit=llvm-ir`.
- **Analyzed by source inspection only:** Wasm exception handling (and Wasm without `exception-handling` under `-C panic=abort`), Windows MSVC SEH (`catchswitch`/`catchpad`), `-Z panic-in-drop=abort`, `-C panic=immediate-abort`, and optimized pipelines (`-C opt-level >= 1`). These are explicitly separated under **Boundaries**.

## Findings

### 3.1 MIR Unwind Data Model and Termination Lang Items

Basis: source (`rust-lang/rust` `960ba7cf7e8666ecb449402ca82b6e9e631bd227`) + source (`rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`).

MIR encodes unwinding edges on unwinding-capable terminators (`Call`, `Drop`, `Assert`, `FalseUnwind`, `InlineAsm`) using `UnwindAction` and `UnwindTerminateReason` in `compiler/rustc_middle/src/mir/syntax.rs:1010-1038`:

```rust
pub enum UnwindAction {
    /// No action is to be taken. Continue unwinding.
    ///
    /// This is similar to `Cleanup(bb)` where `bb` does nothing but `Resume`, but they are not
    /// equivalent, as presence of `Cleanup(_)` will make a frame non-POF.
    Continue,
    /// Triggers undefined behavior if unwind happens.
    Unreachable,
    /// Terminates the execution if unwind happens.
    Terminate(UnwindTerminateReason),
    /// Cleanups to be done.
    Cleanup(BasicBlock),
}

pub enum UnwindTerminateReason {
    /// Unwinding is just not possible given the ABI of this function.
    Abi,
    /// We were already cleaning up for an ongoing unwind, and a *second*, *nested* unwind was
    /// triggered by the drop glue.
    InCleanup,
}
```

Two properties of this representation are load-bearing for downstream analyses and codegen:

1. **POF (Plain Old Frame) sensitivity (`syntax.rs:1016-1018`):** `UnwindAction::Continue` and `Cleanup(bb)` where `bb` only executes `UnwindResume` are semantically distinct because `Cleanup(_)` designates a cleanup landing pad that makes the frame non-POF and triggers landing-pad codegen unless removed by `RemoveNoopLandingPads` or post-monomorphization `nop_landing_pads`.
2. **Exact mapping from `UnwindTerminateReason` to runtime lang items (`terminator.rs:145-168`, `library/core/src/panicking.rs:347-370`):**

| `UnwindTerminateReason` | MIR short text (`as_short_str`) | Diagnostic text (`as_str`) | `LangItem` (`lang_item`) | Target callee attributes & implementation |
| :--- | :--- | :--- | :--- | :--- |
| `Abi` | `"abi"` | `"panic in a function that cannot unwind"` | `LangItem::PanicCannotUnwind` | `#[lang = "panic_cannot_unwind"] #[rustc_nounwind] fn panic_cannot_unwind() -> !` calling `panic_nounwind(...)` |
| `InCleanup` | `"cleanup"` | `"panic in a destructor during cleanup"` | `LangItem::PanicInCleanup` | `#[lang = "panic_in_cleanup"] #[rustc_nounwind] fn panic_in_cleanup() -> !` calling `panic_nounwind_nobacktrace(...)` |

Both termination helpers are marked `#[rustc_nounwind]` (`CodegenFnAttrFlags::NEVER_UNWIND`), guaranteeing that the termination handler itself cannot initiate another unwind cycle. Both MIR representations (`960ba7cf7e` and `14210df0e2`) share this exact definition.

### 3.2 Unwind Eligibility Lattice (`layout::fn_can_unwind`)

Basis: source (`rust-lang/rust` `960ba7cf7e8666ecb449402ca82b6e9e631bd227`, `compiler/rustc_middle/src/ty/layout.rs:1358-1421`; `14210df0e2`, `lines 1236-1297`).

Unwind eligibility for any callable (`Option<DefId>` + `ExternAbi`) is decided by a strict four-stage decision cascade in `rustc_middle::ty::layout::fn_can_unwind(tcx, fn_def_id, abi)`:

```text
1. if did has CodegenFnAttrFlags::NEVER_UNWIND           => false   (e.g., #[rustc_nounwind])
2. if !panic_strategy().unwinds() && !is_foreign_item    => false   (-Cpanic=abort local items!)
3. if !opts.unstable_opts.panic_in_drop.unwinds()
      && is_lang_item(did, LangItem::DropGlue)           => false   (-Zpanic-in-drop=abort)
4. match abi:
     C { unwind } | System { unwind } | Cdecl { unwind }
     | Stdcall { unwind } | Fastcall { unwind }
     | Vectorcall { unwind } | Thiscall { unwind }
     | Aapcs { unwind } | Win64 { unwind }
     | SysV64 { unwind }                                 => unwind
     Rust | RustCall | RustCold | RustPreserveNone
     | RustTail (960ba7cf7e)                             => panic_strategy().unwinds()
     all other ABIs (PtxKernel, Swift, Custom, ...)      => false
```

This creates a crucial asymmetry between **local definitions**, **foreign `extern` declarations**, and **indirect function pointers**:

| Target expression | `fn_def_id` | `abi` | `-C panic=unwind` | `-C panic=abort` | Reason in `fn_can_unwind` |
| :--- | :--- | :--- | :---: | :---: | :--- |
| Local `fn f()` | `Some(did)` (`is_foreign_item = false`) | `Rust` | `true` | `false` | Rule 2 (local abort) / Rule 4 (`Rust`) |
| Local `#[rustc_nounwind] fn f()` | `Some(did)` | `Rust` / `C { unwind: true }` | `false` | `false` | Rule 1 (`NEVER_UNWIND` wins first) |
| Local `extern "C" fn f()` | `Some(did)` (`false`) | `C { unwind: false }` | `false` | `false` | Rule 4 (`unwind = false`) / Rule 2 |
| Local `extern "C-unwind" fn f()` | `Some(did)` (`false`) | `C { unwind: true }` | **`true`** | **`false`** | Under `-C panic=abort`, Rule 2 forces local `extern "C-unwind"` definitions to **not** unwind |
| Foreign `extern "C" { fn f(); }` | `Some(did)` (`is_foreign_item = true`) | `C { unwind: false }` | `false` | `false` | Rule 4 (`unwind = false`) |
| Foreign `extern "C-unwind" { fn f(); }` | `Some(did)` (`is_foreign_item = true`) | `C { unwind: true }` | **`true`** | **`true`** | `is_foreign_item == true` skips Rule 2; Rule 4 returns `unwind = true` |
| Indirect ptr `f: extern "C-unwind" fn()` | **`None`** (`ty::FnPtr`) | `C { unwind: true }` | **`true`** | **`true`** | `fn_def_id == None` skips Rules 1–3; Rule 4 returns `unwind = true` |
| Indirect ptr `f: extern "C" fn()` | `None` (`ty::FnPtr`) | `C { unwind: false }` | `false` | `false` | Rule 4 (`unwind = false`) |
| `drop_in_place` glue (when `-Z panic-in-drop=abort`) | `Some(DropGlue)` | `Rust` | `false` | `false` | Rule 3 (`DropGlue` + `!panic_in_drop.unwinds()`) |

Equally subtle: inside `AbortUnwindingCalls`, `TerminatorKind::Drop` (`abort_unwinding_calls.rs:101-104`) checks `panic_in_drop == PanicStrategy::Unwind && fn_can_unwind(tcx, None, ExternAbi::Rust)`, and `Assert` / `FalseUnwind` (`lines 105-107`) check `fn_can_unwind(tcx, None, ExternAbi::Rust)`, whereas `InlineAsm` (`lines 108-110`) checks `options.contains(InlineAsmOptions::MAY_UNWIND)`.

### 3.3 MIR Pipeline Ordering and Pass Interactions

Basis: source (`rust-lang/rust` `960ba7cf7e`, `compiler/rustc_mir_transform/src/{lib.rs, cleanup_post_borrowck.rs, remove_noop_landing_pads.rs, elaborate_drops.rs, abort_unwinding_calls.rs}` and `compiler/rustc_mir_build/src/builder/scope.rs`) + execution (`support/probe_results.json`).

#### Pipeline sequence (`rustc_mir_transform/src/lib.rs:641-698`)

1. **`run_analysis_cleanup_passes`:**
   - `CleanupPostBorrowck` (`PassPolicy::Required`): eliminates administrative borrowck instructions and lowers `FalseEdge`/`FalseUnwind` to `Goto { target: real_target }` (`cleanup_post_borrowck.rs:66-70, 88`).
   - `RemoveNoopLandingPads` (**`PassPolicy::optional(ctx.panic_strategy().unwinds())`**, `remove_noop_landing_pads.rs:18`): replaces unwind jumps targeting cleanup chains that do only `Nop`/local moves + `UnwindResume` with `UnwindAction::Continue` (when `-Z mir-opt-level >= 1` or optional passes enabled under `panic=unwind`). Crucially, **`ctx.panic_strategy().unwinds()` makes this pass DISABLED whenever `-C panic=abort` is active**—independent of MIR opt-level! Under `-Z mir-opt-level=0 -C panic=unwind`, `RemoveNoopLandingPads` does not run either (note the upstream `FIXME` at `remove_noop_landing_pads.rs:16`), which is why pre-monomorphization MIR still contains empty cleanup blocks such as `bb4 (cleanup) -> bb5 (cleanup) -> bb6 (cleanup): resume;` in `may_drop`.
   - `SimplifyCfg::PostAnalysis`, `Derefer`, `PostAnalysisNormalize`.
2. **`run_runtime_lowering_passes`:**
   - `CriticalCallEdges` -> `Subtyper` -> `ElaborateDrops` -> `Lint(CheckDropRecursion)` -> **`AbortUnwindingCalls` (`PassPolicy::Required`)** -> `AddMovesForPackedDrops` -> ... -> `pm::run_passes_no_validate(..., Some(MirPhase::Runtime(RuntimePhase::Initial)))`.
   - Note that `AbortUnwindingCalls` invokes `super::simplify::remove_dead_blocks(body)` internally (`abort_unwinding_calls.rs:139`).

#### How `InCleanup` termination enters MIR (`builder/scope.rs:422-430`, `elaborate_drops.rs:360-375`)

When MIR is initially built for drops inside unwind cleanup scopes (`builder/scope.rs:425`), `DropKind::Value` emits:

```rust
let terminator = TerminatorKind::Drop {
    target: blocks[drop_node.next].unwrap(),
    unwind: UnwindAction::Terminate(UnwindTerminateReason::InCleanup),
    place: drop_node.data.local.into(),
    replace: false,
    drop: None,
};
```

And during `ElaborateDrops::elaborate_drop` (`elaborate_drops.rs:360-362`), if `data.is_cleanup` holds on a drop block, `unwind` is systematically translated to `Unwind::InCleanup`, routing nested unwinds inside cleanup drop ladders to a `terminate(cleanup)` block (or keeping `unwind terminate(cleanup)` directly on the elaborated `drop(...)` terminator, as observed in `trigger_double_panic` and `c_abi_with_drop_calls_c_unwind`).

#### `AbortUnwindingCalls` state transition rules (`abort_unwinding_calls.rs:47-140`)

Let:
- `target_supports_unwinding = !(is_like_wasm && panic_strategy == Abort && !has_feature(exception_handling))`
- `body_can_unwind = layout::fn_can_unwind(tcx, Some(def_id), body_abi)`

`AbortUnwindingCalls` transforms every `BasicBlockData` in `body.basic_blocks`:

1. **First check (`UnwindResume`, lines 78-84):** Runs even when `block.is_cleanup == true`:
   - If `!target_supports_unwinding`: `UnwindResume` -> `TerminatorKind::Unreachable`.
   - Else if `!body_can_unwind`: `UnwindResume` -> `TerminatorKind::UnwindTerminate(UnwindTerminateReason::Abi)`.
   - Else (`target_supports_unwinding && body_can_unwind`): `UnwindResume` is preserved.
2. **Cleanup block skip (lines 86-88):**
   - `if block.is_cleanup { continue; }` — cleanup `Drop`/`Call`/`Assert` terminators keep their existing `UnwindAction` (specifically `UnwindAction::Terminate(InCleanup)`). Because cleanup blocks in valid MIR can only be reached via a non-cleanup block's `UnwindAction::Cleanup(bb)`, making all incoming outer unwind edges `Unreachable` under `-C panic=abort` renders those cleanup blocks unreachable, and step 4 (`remove_dead_blocks`) deletes them completely.
3. **Non-cleanup unwinding terminators (lines 90-135):** For `Call`, `Drop`, `Assert`, `FalseUnwind`, `InlineAsm`:
   - If `!call_can_unwind || !target_supports_unwinding`: replace `unwind` with **`UnwindAction::Unreachable`**.
   - Else (`call_can_unwind && target_supports_unwinding`) and `!body_can_unwind` and `unwind == UnwindAction::Continue`: replace `unwind` with **`UnwindAction::Terminate(UnwindTerminateReason::Abi)`**.
   - Else if `!body_can_unwind` and `unwind == UnwindAction::Cleanup(bb)`: **`Cleanup(bb)` is preserved untouched!** Thus local destructors in `bb (cleanup)` still execute before reaching `bb_exit (cleanup): UnwindResume` -> rewritten by rule 1 to `UnwindTerminate(Abi)`.
4. **Dead cleanup removal (line 139):** `super::simplify::remove_dead_blocks(body)`.

#### Discovered Compiler Interaction: `-C panic=abort` + Foreign / Indirect `extern "C-unwind"` Uses `Cleanup(bb) -> terminate(abi)`, Not Inline `terminate(abi)`

Basis: source (`remove_noop_landing_pads.rs:18`, `abort_unwinding_calls.rs:78-135`) + execution (`support/probe_results.json`).

A non-obvious interaction emerges when compiling a caller of `extern "C-unwind"` foreign functions or function pointers under `-C panic=abort`:
- Because `RemoveNoopLandingPads` has `PassPolicy::optional(ctx.panic_strategy().unwinds())`, it does **not** collapse the pre-existing `bb0 -> [unwind: bb2]` / `bb2 (cleanup): resume;` generated by MIR building.
- When `AbortUnwindingCalls` runs on `call_foreign_c_unwind` or `call_indirect_c_unwind` under `-C panic=abort`, rule 3 computes `call_can_unwind == true` (`is_foreign_item` or `FnPtr`!) and `body_can_unwind == false`, while seeing `unwind == UnwindAction::Cleanup(bb2)` (NOT `Continue`!).
- Therefore, rule 3 leaves `unwind: bb2` intact, rule 1 rewrites `bb2`'s `resume;` into `terminate(abi);`, and `remove_dead_blocks` keeps `bb2` alive.
- At LLVM codegen (`block.rs:225-289`), `UnwindAction::Cleanup(bb2)` emits `invoke ... to label %bb1 unwind label %cleanup` with **`landingpad { ptr, i32 } cleanup`** branching to `%bb2`, where `terminate(abi)` calls `panic_cannot_unwind()`, rather than an Itanium `landingpad { ptr, i32 } filter [0 x ptr] zeroinitializer` block. Semantics are still completely safe (the foreign unwind is intercepted and aborts), but unoptimized LLVM IR retains a `cleanup` landingpad + slot alloca rather than a zeroinitializer `filter` pad.

### 3.4 Structural MIR CFG Invariants (`rustc_mir_transform/src/validate.rs`)

Basis: source (`rust-lang/rust` `960ba7cf7e`, `compiler/rustc_mir_transform/src/validate.rs:118-281`).

`CfgChecker` enforces structural invariants across MIR validation passes:

1. **Block-polarity edge rule (`check_edge`, `lines 139-165`):**
   - `bb == START_BLOCK` must have zero predecessors.
   - Allowed `(src.is_cleanup, dst.is_cleanup, EdgeKind)` triples are **only** `(false, false, Normal)`, `(true, true, Normal)`, and `(false, true, Unwind)`. Any unwind edge into a non-cleanup block, or any transition originating in a cleanup block into a non-cleanup block, or any second unwind edge out of a cleanup block into another cleanup block fails validation (`ICE`).
2. **Scoped `UnwindAction` legality (`check_unwind_edge`, `lines 246-275`):**

| `UnwindAction` | Allowed in normal block (`!is_cleanup`)? | Allowed in cleanup block (`is_cleanup`)? | Requires `self.can_unwind`? | Additional constraint |
| :--- | :---: | :---: | :---: | :--- |
| `Cleanup(target)` | Yes | **Forbidden** | No | `target` must exist and satisfy `target.is_cleanup == true` |
| `Continue` | Yes (iff `self.can_unwind`) | **Forbidden** | **Yes** | Forbidden anywhere when `!self.can_unwind` |
| `Terminate(InCleanup)` | **Forbidden** | Yes | No | Strictly cleanup-block scoped |
| `Terminate(Abi)` | Yes | Yes | No | Always valid (`lines 272-273`) |
| `Unreachable` | Yes | Yes | No | Always valid structurally |

3. **Acyclic single-exit cleanup trees (`check_cleanup_control_flow`, `lines 168-244`):** When `unwind_edge_count > 1`, cleanup blocks are contracted onto their highest cleanup dominator entry (`post_contract_node`) and every contracted cleanup subgraph is checked to have at most one outgoing successor (`parent[bb]`) and zero cycles.
4. **Critical call/cleanup edge splitting (`is_critical_call_edge`, `lines 277-281`):** If `unwind` is `Cleanup(_)` or `Terminate(_)` and `target` has `> 1` predecessors, the normal edge is critical so cleanup/terminate codegen stays isolated.

### 3.5 CodegenSSA, CodegenLLVM, and LLVM `nounwind` Semantics

Basis: source (`rust-lang/rust` `960ba7cf7e`, `compiler/rustc_codegen_ssa/src/mir/block.rs:215-335, 2253-2420`, `compiler/rustc_codegen_llvm/src/abi.rs:654-674, 821-830`; `llvm/llvm-project` `510c32aa35`, `llvm/include/llvm/IR/Attributes.td:265`, `llvm/docs/LangRef.md:2573-2579`, `llvm/docs/ExceptionHandling.md:255-284`).

1. **Function and callsite `nounwind` attribute (`compiler/rustc_codegen_llvm/src/abi.rs:658-660, 826-828`):** Both `apply_attrs_llfn` and `apply_attrs_callsite` emit `llvm::AttributeKind::NoUnwind` whenever `!self.can_unwind` (`FnAbi::can_unwind == false`). In LLVM `Attributes.td:265`:
   ```tablegen
   def NoUnwind : EnumAttr<"nounwind", IntersectAnd, [FnAttr]>;
   ```
   And `llvm/docs/LangRef.md:2573-2579` specifies:
   > "`nounwind`: This function attribute indicates that the function never raises an exception. If the function does raise an exception, its runtime behavior is undefined. However, functions marked nounwind may still trap or generate asynchronous exceptions."
   Furthermore, `llvm/docs/ExceptionHandling.md:256-257` warns: *"Do not allow a new exception to propagate out of the execution of a cleanup. This can corrupt the internal state of the unwinder."*
2. **MIR terminator lowering (`rustc_codegen_ssa/src/mir/block.rs:221-335`):**
   - If `!fn_abi.can_unwind`, `do_call` unconditionally clamps `unwind = mir::UnwindAction::Unreachable` (`line 221-223`) as a second defense-in-depth check matching MIR.
   - `UnwindAction::Cleanup(cleanup)` lowers to `invoke` onto `llbb_with_cleanup(fx, cleanup)` **unless** `fx.nop_landing_pads.contains(cleanup)`, in which case `unwind_block = None` and codegen downgrades `invoke` to a plain `call` (`line 226-231, 312`)! Note that `find_noop_landing_pads_for_instance` (`remove_noop_landing_pads.rs:157-164`) instantiates generic types and resolves `Instance::resolve_drop_glue`: if `ShimKind::DropGlue(_, None)` proves no glue exists or cleanup paths merely move locals and hit `UnwindResume` (as in `may_drop`), codegen emits plain `call` + `ret void` without any landingpad or personality function even at `-C opt-level=0 -Z mir-opt-level=0`!
   - `UnwindAction::Terminate(reason)` emits `fx.terminate_block(reason, ...)` (`lines 235-249`):
     - On **Itanium / DWARF ELF targets**, `bx.filter_landing_pad(llpersonality)` generates `landingpad { ptr, i32 } filter [0 x ptr] zeroinitializer` followed by a call to `reason.lang_item()` (`panic_cannot_unwind` or `panic_in_cleanup`) and `unreachable` (`lines 2385-2416`). (Exception: when `panic = "immediate-abort"` builds `compiler_builtins` or calls upstream monomorphizations under `is_call_from_compiler_builtins_to_upstream_monomorphization`, `bx.abort_immediate()` is emitted directly at `line 2398`.)
     - On **MSVC SEH (`wants_new_eh_instructions` && `wants_msvc_seh`)**, `InCleanup` returns `None` (`plain call` at `lines 240-245`) because Windows SEH terminates automatically on nested exceptions during cleanup; `Abi` emits `catchswitch` -> `catchpad [null, i32 0x40, null]` (`HT_IsStdDotDot` C++ catch-all flag at `line 2360-2368`, specifically chosen so `longjmp` does not trigger panic abort).
     - On **Wasm EH (`wants_wasm_eh`)**, `InCleanup` creates a nested `catchswitch within %outer_cleanuppad` -> `catchpad [null]` (`catch_all` at `lines 236-239, 2341-2376`).
   - `UnwindAction::Continue` and `UnwindAction::Unreachable` emit plain `call` (no `invoke`, no landingpad).

### 3.6 Live `rustc 1.98.0-nightly` + LLVM `22.1.6` MIR/LLVM Matrix and Runtime Executions

Basis: execution (`support/probe_unwind_action_c_unwind_abi.py`, `support/probe_results.json`, `2026-11-23T16:11:30Z`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with LLVM `22.1.6` on `x86_64-unknown-linux-gnu`).

#### Observed MIR & LLVM IR transformation matrix (`-Zdump-mir=AbortUnwindingCalls -Zmir-opt-level=0 -Copt-level=0`)

| Probe function | Mode | MIR `AbortUnwindingCalls` before | MIR `AbortUnwindingCalls` after | LLVM IR function attrs & personality | LLVM IR call/unwind lowering |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `c_abi_panics` | `-Cpanic=unwind` | `bb1`: `from_str(...) -> unwind continue`; `bb2`: `panic_fmt(...) -> unwind continue` | `bb1, bb2`: `-> unwind terminate(abi)` | `nounwind` (`#2`), `personality @rust_eh_personality` | `invoke ... unwind label %terminate`; `%terminate: landingpad filter [0 x ptr] zeroinitializer` -> `call panic_cannot_unwind() #8; unreachable` |
| `c_abi_panics` | `-Cpanic=abort` | `bb1, bb2`: `unwind continue` | `bb1, bb2`: `unwind unreachable` | `nounwind` (`#2`), no personality | Plain `call ...`; `unreachable` |
| `c_unwind_abi_panics` | `-Cpanic=unwind` | `bb1, bb2`: `unwind continue` | `bb1, bb2`: `unwind continue` | **No** `nounwind` (`#3`), no personality | Plain `call ...`; `unreachable` |
| `c_unwind_abi_panics` | `-Cpanic=abort` | `bb1, bb2`: `unwind continue` | **`bb1, bb2`: `unwind unreachable`** | **`nounwind` (`#2`), no personality** | Plain `call ...`; `unreachable` |
| `c_abi_with_drop_calls_c_unwind` | `-Cpanic=unwind` | `bb0: unwind: bb3`; `bb3(cleanup): drop -> unwind terminate(cleanup)`; `bb4(cleanup): resume` | `bb3` unchanged; **`bb4(cleanup): terminate(abi);`** | `nounwind` (`#2`), `personality @rust_eh_personality` | `invoke c_unwind_abi_panics -> unwind %cleanup`; `%bb3: invoke drop_glue -> unwind %terminate (panic_in_cleanup)`; `%bb4: call panic_cannot_unwind()` |
| `c_abi_with_drop_calls_c_unwind` | `-Cpanic=abort` | `bb0: unwind: bb3`; `bb3, bb4` cleanup | **`bb0, bb1: unwind unreachable`; `bb3, bb4` deleted** | `nounwind` (`#2`), no personality | Plain `call c_unwind_abi_panics` + plain `call drop_glue` |
| `trigger_double_panic` | `-Cpanic=unwind` | `bb0: unwind: bb3`; `bb3: drop(_1) -> unwind terminate(cleanup)`; `bb4: resume` | Identical (`is_cleanup` skipped) | No `nounwind` (`#3`), `personality @rust_eh_personality` | `%bb3: invoke drop_glue -> unwind %terminate` (`filter [0 x ptr] zeroinitializer` -> `call panic_in_cleanup()`) |
| `trigger_double_panic` | `-Cpanic=abort` | `bb0..bb4` | **`bb0, bb1: unwind unreachable`; `bb3, bb4` deleted** | `nounwind` (`#2`), no personality | Plain `call helper_may_panic` + plain `call drop_glue` |
| `may_drop` | `-Cpanic=unwind` | `bb0: unwind bb4`; `bb1: unwind bb5`; `bb4,bb5 -> bb6: resume` | Identical in MIR (`-Zmir-opt-level=0`) | No `nounwind` (`#3`), no personality | **Plain `call mem::drop` + `call c_unwind_abi_panics`** (`fx.nop_landing_pads` elides empty cleanup pads in codegen!) |
| `call_foreign_c_unwind` | `-Cpanic=unwind` | `bb0: external_c_unwind_callee() -> unwind continue` | Identical (`unwind continue`) | No `nounwind` (`#3`), no personality | Plain `call void @external_c_unwind_callee()` |
| `call_foreign_c_unwind` | `-Cpanic=abort` | **`bb0: unwind: bb2`; `bb2(cleanup): resume`** | **`bb0: unwind: bb2`; `bb2(cleanup): terminate(abi)`** | **`nounwind` (`#2`), `personality @rust_eh_personality`** | **`invoke @external_c_unwind_callee() unwind label %cleanup` -> `landingpad cleanup` -> `%bb2: call panic_cannot_unwind()`** |
| `call_indirect_c_unwind` | `-Cpanic=abort` | `bb0: unwind: bb2`; `bb2(cleanup): resume` | `bb0: unwind: bb2`; `bb2(cleanup): terminate(abi)` | **`nounwind` (`#2`), `personality @rust_eh_personality`** | **`invoke %f(...) unwind label %cleanup` -> `landingpad cleanup` -> `%bb2: call panic_cannot_unwind()`** |

Comparison across `-C panic=abort -Zpanic_abort_tests` (`panic_abort_mode`) vs. `-C panic=abort` (`panic_abort_plain`): all 14 MIR dump files (`7` functions × `before`/`after`) are byte-for-byte identical, and all LLVM attributes match identically (the only LLVM IR diffs in `c_abi_panics` and `c_unwind_abi_panics` are crate-disambiguator/alloc constant symbols).

#### Verbatim MIR and LLVM IR Specimens (`support/probe_results.json`)

The following verbatim pairs from `probe_results.json` illustrate the two sharpest interactions in `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / LLVM `22.1.6`:

1. **`c_abi_with_drop_calls_c_unwind` (`-C panic=unwind`)**: `bb0`'s `Cleanup(bb3)` edge stays intact, `bb3`'s cleanup drop retains `unwind terminate(cleanup)`, and `bb4 (cleanup): resume;` becomes `bb4 (cleanup): terminate(abi);`, producing LLVM `invoke ... unwind label %cleanup` plus a `filter [0 x ptr] zeroinitializer` `%terminate` block:

```text
// Before AbortUnwindingCalls:
    bb3 (cleanup): {
        drop(_2) -> [return: bb4, unwind terminate(cleanup)];
    }
    bb4 (cleanup): {
        resume;
    }

// After AbortUnwindingCalls:
    bb3 (cleanup): {
        drop(_2) -> [return: bb4, unwind terminate(cleanup)];
    }
    bb4 (cleanup): {
        terminate(abi);
    }
```

```llvm
; Function Attrs: noinline nounwind nonlazybind uwtable
define void @_RNvCsh8INqWOoJ6U_5probe30c_abi_with_drop_calls_c_unwind(i1 zeroext %cond) unnamed_addr #2 personality ptr @rust_eh_personality {
start:
  %0 = alloca [16 x i8], align 8
  %_2 = alloca [0 x i8], align 1
  invoke void @_RNvCsh8INqWOoJ6U_5probe19c_unwind_abi_panics(i1 zeroext %cond)
          to label %bb1 unwind label %cleanup
bb3:
  invoke void @_RINvNtCs8b4M6GsfcPr_4core3ptr9drop_glueNtCsh8INqWOoJ6U_5probe10DropLoggerEBD_(ptr %_2) #12
          to label %bb4 unwind label %terminate
bb4:
  call void @_RNvNtCs8b4M6GsfcPr_4core9panicking19panic_cannot_unwind() #13
  unreachable
terminate:
  %9 = landingpad { ptr, i32 }
          filter [0 x ptr] zeroinitializer
  call void @_RNvNtCs8b4M6GsfcPr_4core9panicking16panic_in_cleanup() #8
  unreachable
}
```

2. **`call_foreign_c_unwind` (`-C panic=abort`)**: skipped `RemoveNoopLandingPads` leaves `bb0 -> unwind: bb2`, `fn_can_unwind` keeps `call_can_unwind = true` (`tcx.is_foreign_item(did)`), and `AbortUnwindingCalls` converts `bb2: resume;` into `bb2: terminate(abi);`, emitting a `landingpad cleanup` rather than a `filter` landingpad:

```text
// After AbortUnwindingCalls (-Cpanic=abort):
    bb0: {
        StorageLive(_1);
        _1 = external_c_unwind_callee() -> [return: bb1, unwind: bb2];
    }
    bb2 (cleanup): {
        terminate(abi);
    }
```

```llvm
; Function Attrs: noinline nounwind nonlazybind uwtable
define void @_RNvCsh8INqWOoJ6U_5probe21call_foreign_c_unwind() unnamed_addr #2 personality ptr @rust_eh_personality {
start:
  %0 = alloca [16 x i8], align 8
  invoke void @external_c_unwind_callee()
          to label %bb1 unwind label %cleanup
bb2:
  call void @_RNvNtCs8b4M6GsfcPr_4core9panicking19panic_cannot_unwind() #10
  unreachable
cleanup:
  %1 = landingpad { ptr, i32 }
          cleanup
  ...
  br label %bb2
}
```

#### Observed native execution receipts (`b_native_catch_unwind_vs_c_abi_abort`)

| Execution case | Flags | Exit / Signal | Stdout | Observed stderr sequence | Verified runtime invariant |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `c_unwind_caught_by_catch_unwind` | `-Cpanic=unwind` | `rc = 0` | `CAUGHT_C_UNWIND=1` | `"unwinding across C-unwind boundary"` | `extern "C-unwind"` unwinds cleanly through FFI frame into `catch_unwind` |
| `extern_c_panic_aborts_process` | `-Cpanic=unwind` | `rc = -6` (`SIGABRT`) | `""` | `"cannot unwind out of extern C"` -> `library/core/src/panicking.rs:225:5: panic in a function that cannot unwind` | `AbortUnwindingCalls` inserts `Terminate(Abi)` barrier instead of LLVM UB |
| `extern_c_with_drop_runs_drop_before_abort` | `-Cpanic=unwind` | `rc = -6` (`SIGABRT`) | `""` | (1) `"unwinding from C-unwind into extern C"` -> (2) **`DROP_RAN_IN_C_ABI`** -> (3) `"panic in a function that cannot unwind"` | `bb0` unwinds via `Cleanup(bb3)` running `DropLogger`, THEN `bb4` `Terminate(Abi)` aborts |
| `double_panic_in_cleanup_aborts_process` | `-Cpanic=unwind` | `rc = -6` (`SIGABRT`) | `""` | (1) `"first panic before drop"` -> (2) `"second panic inside drop"` -> (3) `panic_in_cleanup` abort | `UnwindAction::Terminate(InCleanup)` aborts cleanly upon nested panic inside `Drop::drop` |
| `panic_abort_flag_aborts_process` | `-Cpanic=abort` | `rc = -6` (`SIGABRT`) | `""` | `"panic under -Cpanic=abort"` | Local `extern "C-unwind"` under `-Cpanic=abort` aborts on `panic!` rather than unwinding |

### 3.7 Gaps and Integration Requirements in `joshlf/anneal`

Basis: source (`joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/MirAst.lean:693-795`, `trusted/lean/Trusted/MirSemantics.lean:1568-1569`, `trusted/correspondence/Trusted/Correspondence.lean:2048-2063`, `trusted/rustc-capture/src/driver.rs:25`).

Inspection of `joshlf/anneal` at `c131b320` identifies four concrete unwinding gaps between upstream `rustc` MIR and Anneal's trusted execution/correspondence layer:

1. **Erased termination reason in `Trusted.MirAst.UnwindAction` (`MirAst.lean:693-697`):**
   ```lean
   inductive UnwindAction where
     | continue_
     | unreachable
     | terminate
     | cleanup (block : BasicBlockId)
   ```
   `UnwindAction.terminate` drops `UnwindTerminateReason` (`Abi` vs. `InCleanup`), preventing downstream MIR semantics or correspondence proofs from distinguishing ABI boundary violations (`panic_cannot_unwind`) from nested cleanup panics (`panic_in_cleanup`).
2. **Terminator conflation (`MirAst.lean:785-795`, `MirSemantics.lean:1568-1569`):** `TerminatorKind.unwindTerminate`, `TerminatorKind.drop`, and indirect `TerminatorKind.call` are collapsed into `TerminatorKind.unsupported`, and `evalTerminator` faults on `.unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported` uniformly with `.fault .unsupported`.
3. **Single-frame sentinel remapping (`Correspondence.lean:2048-2063`):** `toMiriTerminatorForDispatch` maps `.unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported` to `{ kind := .UnwindTerminate .Abi }` specifically so single-frame `Miri` evaluation does not classify `.unwindResume` as `.undefinedBehavior`. Supporting multi-frame verification cleanly requires modeling full call-stack unwind propagation (`callerCont.unwindOnCall`) and cleanup depth (`inCleanup`) rather than a sentinel collapse.
4. **Missing function-level ABI/strategy metadata (`FnAbi::can_unwind`):** `driver.rs` captures MIR via `rustc_driver` (`1.98.0-nightly (f8a08b688 2026-05-30)`), while `Trusted.MirAst` does not yet carry per-function `ExternAbi` (`isForeign`, `neverUnwind`) or crate-level `PanicStrategy` needed to express `AbortUnwindingCalls` soundness (`Terminate(Abi)` vs. `Unreachable` vs. foreign `C-unwind`).

### 3.8 Kernel-Checked `Lean v4.34.1` Soundness Development

Basis: source + Lean `v4.34.1` kernel execution (`support/MirUnwindActionAbortUnwindingSoundness.lean`, `6,181` lines, `322` theorems, `680` definitions, zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`, zero `partial def`, zero `_unsafe_rec`).

All definitions are explicitly marked `noncomputable def` on pure structural collections and operational relations so zero compiler-generated `_unsafe_rec` constants exist in the Lean environment and every concrete test evaluates cleanly in-kernel by `rfl`.

#### Model structure (`Sections 1–8`, lines `24–1844`)

- **IR & ABI (`Section 2`, `lines 229–380`):** `FnAbi` (`.rust`, `.c canUnwind`), `PanicStrategy` (`.unwind`, `.abort`), `UnwindTerminateReason` (`.abi`, `.inCleanup`), `UnwindAction` (`.continue_`, `.unreachable`, `.terminate reason`, `.cleanup bb`), `fnCanUnwind` faithfully reproducing all four stages of `layout::fn_can_unwind`, `FnBody` (`abi`, `isForeign`, `neverUnwind`, `localCount`, `blocks`), and `Program` (`strategy`, `targetSupportsUnwinding`, `panicInDropUnwinds`, `entryFn`, `fns`, `foreignSpecs`).
- **Validation predicates (`Section 3`, `lines 381–528`):** `MirPrePassWF` and `MirPostPassWF` faithfully mirror `validate.rs` (`check_edge` block polarity, `check_unwind_edge` cleanup/non-cleanup constraints and `InCleanup` localization, `UnwindResume` validity iff `targetSupportsUnwinding && bodyCanUnwind`, and foreign/non-foreign ABI consistency). `PrePassNoBogusUnreachable` and `PostPassNoBogusUnreachable` encode the reachability assumption guaranteeing unwinding paths do not strike `.unreachable` prematurely.
- **Multi-frame semantics (`Section 4`, `lines 529–806`):** `MirState` tracks `cur : ActiveFrame` (including `bb`, `stmtIdx`, `locals`, `inCleanup`), `stack : List CallerCont` (with `unwindOnCall : UnwindAction`), `cleanupDepth : Nat`, and `trace : List TraceEvent`. Execution outcomes (`MirExecResult`) distinguish `.returned`, `.unwound`, `.terminated (reason : UnwindTerminateReason)`, `.aborted`, `.ub`, `.invalid`, and `.outOfFuel`, allowing soundness theorems to prove `.ub` and `.invalid` unreachable while proving exact `.terminated .abi` / `.terminated .inCleanup` trapping.
- **Transforms (`Sections 5–6`, `lines 807–1329`):**
  - `abortUnwindingCallsProg` faithfully encodes `AbortUnwindingCalls` (`UnwindResume -> Unreachable | UnwindTerminate .abi`, cleanup-block skipping, non-cleanup `!callCanUnwind || !targetSupportsUnwinding -> Unreachable`, `!bodyCanUnwind && Continue -> Terminate .abi`).
  - `eraseDeadCleanupProg` models `super::simplify::remove_dead_blocks` restricted to `-C panic=abort` cleanup block erasure (filtering non-cleanup blocks with index-remapping and proving non-cleanup indices remain preserved).
  - `llvmLowerProg` models LLVM `hasNoUnwind := bnot (bodyCanUnwind prog.strategy fn)`, `llvmLowerCallTerm` (emitting `LlvmTerm.callPlain` for `Continue | Unreachable | !callUnw` and `LlvmTerm.invoke` for `Cleanup(c)` and `Terminate(r)` with `LlvmPad.cleanupPad c` vs. `LlvmPad.filterTerminatePad r`), and explicit LLVM `stepLlvm` where unwinding across `.hasNoUnwind = true` without a landing pad yields `.halted (.ub trace)` per LLVM `LangRef`.

#### Mechanized Main Theorems (`Sections 9–12`, lines `1845–5961`)

1. **Main Theorem 1 — `AbortUnwindingCalls` Exact Soundness (`abortUnwindingCalls_exact_soundness`, `line 3634`, axiom footprint `[propext, Quot.sound]`):**
   For any `prog` satisfying `MirPrePassWF prog`, `ForeignContractOK prog`, and `PrePassNoBogusUnreachable prog`, letting `prog' := abortUnwindingCallsProg prog`:
   - `MirPostPassWF prog'`, `ForeignContractOK prog'`, and `PostPassNoBogusUnreachable prog'`: post-pass MIR passes all `validate.rs` checks and preserves foreign contracts;
   - `evalMirProg_safe`: for all `fuel arg`, `¬ mirIsBad (evalMirProg prog' fuel arg)` (`evalMirProg prog' fuel arg` is neither `.ub _` nor `.invalid _`);
   - **ABI Barrier Guarantee:** for every function `entry` with `bodyCanUnwind prog.strategy entry = false` (`entry` at `prog.entryFn`), `evalMirProg prog' fuel arg ≠ .unwound tr`;
   - **Normal-Return Preservation (`abortUnwindingCalls_preserves_returned`):** every normal `.returned v tr` evaluation in `prog` evaluates to `.returned v tr` identically in `prog'`.
2. **Main Theorem 2 — Double-Panic `InCleanup` Termination (`double_panic_inCleanup_termination`, `line 4106`, plus `double_panic_direct_inCleanup`, `double_panic_foreign_inCleanup`, `[propext, Quot.sound]`):**
   For any `MirRuntimeSafe` state under `MirPostPassWF`, `ForeignContractOK`, and `PostPassNoBogusUnreachable`, entering `cur.inCleanup = true` enforces `cleanupDepth ≥ 1`, any direct panic inside a cleanup block (`panicCall u` under `strategy = .unwind` and `targetSupportsUnwinding = true`) halts immediately with `.terminated .inCleanup st.trace`, and `StackHasCleanupGuard st.stack` guarantees across every step that cleanup execution NEVER produces `.ub`/`.invalid`, NEVER escapes to `.unwound tr`, and NEVER returns normally via `.returned v tr` while cleanup guard frames remain active.
3. **Main Theorem 3 — `-C panic=abort` Cleanup Reachability & Erasure (`eraseDeadCleanup_preserves_WF_and_exec`, `line 4981`, plus `panicAbort_cleanup_unreachable` at `line 4441`, `[propext, Quot.sound]`):**
   Whenever `prog.strategy = .abort` and `NoUnwindingCalls prog` (no unwinding foreign items called in `-C panic=abort`):
   - `panicAbort_cleanup_unreachable`: zero cleanup blocks are reachable (`ReachableBB fn'.blocks b → blk'.isCleanup = false`);
   - `eraseDeadCleanup_zero_cleanup_blocks`: `eraseDeadCleanupProg prog'` contains zero cleanup blocks across all non-foreign functions;
   - `eraseDeadCleanup_preserves_WF_and_exec`: `MirPostPassWF (eraseDeadCleanupProg prog')` holds, neither program ever returns `.unwound tr` or fails `mirIsBad`, and `MirCleanupEraseResultEq (evalMirProg prog' fuel arg) (evalMirProg (eraseDeadCleanupProg prog') fuel arg)` holds identically for every `fuel arg`.
4. **Main Theorem 4 — LLVM `call`/`invoke` & `nounwind` Attribute Soundness (`llvm_nounwind_never_escapes`, `line 5933`, `mir_llvm_lockstep_sim`, `line 5901`, `[propext, Quot.sound]`):**
   Under `MirPrePassWF`, `ForeignContractOK`, and `PrePassNoBogusUnreachable`, for `lprog := llvmLowerProg (abortUnwindingCallsProg prog)`:
   - Zero LLVM UB (`∀ fuel arg, ¬ llvmIsBad (evalLlvmProg lprog fuel arg)`);
   - **Zero `nounwind` unwind escape (`∀ entry lentry, lentry.hasNoUnwind = true → ∀ fuel arg tr, evalLlvmProg lprog fuel arg ≠ .unwound tr`)**, explicitly covering foreign/indirect `extern "C-unwind"` callees inside `-C panic=abort` callers (`invoke` + `landingpad` + `panic_cannot_unwind`);
   - Exact trace, value, and termination lockstep (`MirLlvmResultEq (evalMirProg prog' fuel arg) (evalLlvmProg lprog fuel arg)`).

#### Positive Canaries & Negative Counterexamples (`Section 13`, lines `5971–6173`, verified by `rfl`)

- **6 positive canaries:**
  - `exCAbiPanics_postMir_and_llvm`: `extern "C"` panic converts `Continue -> Terminate .abi`, yields `hasNoUnwind = true` + `invoke`, and halts `.terminated .abi [10, 11]`.
  - `exCUnwindAbiPanics_mir_and_llvm`: `extern "C-unwind"` panic preserves `Continue`, omits `nounwind`, emits `CallPlain`, and yields `.unwound [20]`.
  - `exCAbiWithDropCallsCUnwind_runs_cleanup_then_terminates`: `extern "C"` with local cleanup runs trace `77` in `bb2 (cleanup)` before rewriting `UnwindResume` -> `.terminated .abi [70, 77]`.
  - `exDoublePanicInCleanup_halts_inCleanup`: nested drop panic inside `bb1 (cleanup)` yields `.terminated .inCleanup [30, 31, 32]`.
  - `exPanicAbortCleanupErased_exact`: `-C panic=abort` erases `bb2 (cleanup)` leaving 2 blocks and identical `.returned 99 [40, 41]`.
  - `exForeignCUnwindUnderPanicAbort_traps_no_ub`: foreign `extern "C-unwind"` under `-C panic=abort` preserves unwindability on callee (`hasNoUnwind = false`), traps cleanly at `.terminated .abi [50, 51]` with zero UB.
- **3 negative counterexamples:**
  - `negMissingAbortUnwindingCalls_llvmUb`: omitting `AbortUnwindingCalls` on `exCAbiPanics` pairs `nounwind` with `Continue`, causing **`evalLlvmProg ... = .ub [10, 11]`**.
  - `negForeignCUnwindUnreachable_llvmUb`: mistakenly setting `UnwindAction.unreachable` on a foreign `extern "C-unwind"` call under `-C panic=abort` hits **`evalLlvmProg ... = .ub []`**.
  - `negCleanupContinue_escapesUnwind`: placing `UnwindAction.continue_` inside a cleanup block violates double-panic termination and escapes to **`.unwound []`**.

## Boundaries

- **Windows MSVC SEH & WebAssembly EH runtime execution (not examined):** Probe compilations and native binaries ran strictly on `x86_64-unknown-linux-gnu` (Itanium DWARF EH). MSVC `catchswitch`/`catchpad [null, i32 0x40, null]`, Wasm nested `catchpad [null]`, and Wasm `!target_supports_unwinding` without `exception-handling` are established solely from upstream `rustc` source (`abort_unwinding_calls.rs:47-49`, `block.rs:236-248, 2253-2392`).
- **Optimized IR passes `-C opt-level >= 1` / `-Z mir-opt-level >= 1` (not examined empirically):** Empirical MIR dumps used `-Z mir-opt-level=0` and LLVM IR used `-C opt-level=0`. Consequently, the exact post-opt LLVM IR simplification of `call_foreign_c_unwind`'s `-C panic=abort` `landingpad cleanup` vs. `filter [0 x ptr] zeroinitializer` after LLVM `SimplifyCFG` or inlining is **not examined** (though LLVM `LangRef` UB rules and `NoUnwind` semantics remain independent of optimization level).
- **Pre-`CleanupPostBorrowck` / pre-`ElaborateDrops` passes (not examined empirically via `-Zdump-mir`):** `RemoveNoopLandingPads` and `AbortUnwindingCalls` are covered at source + `AbortUnwindingCalls` MIR dumps; `-Z dump-mir=CleanupPostBorrowck` or `ElaborateDrops` dumps were not emitted separately.
- **Asynchronous exceptions, hardware traps, and C `longjmp` (known not to apply):** LLVM `LangRef.md:2576-2579` explicitly permits `nounwind` functions to trap or raise asynchronous OS signals, and `block.rs:2300-2305` documents that C `setjmp`/`longjmp` deliberately bypasses MSVC `catch(...)` terminate pads while `InCleanup` relies on MSVC SEH. `AbortUnwindingCalls` and `UnwindAction` govern only synchronous stack-unwinding exceptions (Rust panics and foreign C++/Itanium unwinds).
- **`-C panic=immediate-abort` and `-Z panic-in-drop=abort` runtime binaries (not examined empirically):** Source code for both modes was inspected (`layout.rs:1377-1381`, `abort_unwinding_calls.rs:101-104`, `block.rs:2398`, `panicking.rs:59-103, 347-365`), whereas the five native binaries ran `-C panic=unwind` and `-C panic=abort`.
- **`joshlf/anneal` multi-frame call and unwind execution (unsupported):** At `c131b320`, `Trusted.MirAst` and `Trusted.MirSemantics` reject `.call`, `.drop`, `.unwindResume`, and `.unwindTerminate` as `.unsupported` / `.fault .unsupported`. Direct runtime testing of unwinds inside Anneal is therefore **unsupported**.
- **Scope of Lean mechanization (known not to apply beyond IR operational model):** `support/MirUnwindActionAbortUnwindingSoundness.lean` models finite-block MIR and structured LLVM IR (`Program` / `LlvmProg`) with foreign-call oracles (`foreignSpecs`). It does not formalize LLVM instruction selection, DWARF `.eh_frame`/LSDA table encoding, `libunwind` cursor state corruption, or `joshlf/anneal`'s memory/pointer alias model.

## Evidence

### Upstream Git Sources Examined

| Repository | Commit SHA (40-hex) | Path | Symbol / Scope | Lines | Role |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_middle/src/mir/syntax.rs` | `UnwindAction`, `UnwindTerminateReason` | `1010–1038` | normative / source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_middle/src/mir/terminator.rs` | `UnwindAction::cleanup_block`, `UnwindTerminateReason::{as_str, as_short_str, lang_item}` | `136–168` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_middle/src/ty/layout.rs` | `fn_can_unwind` | `1358–1421` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_mir_build/src/builder/scope.rs` | `DropKind::Value` `Terminate(InCleanup)` wiring | `418–431` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_mir_transform/src/lib.rs` | `run_analysis_cleanup_passes`, `run_runtime_lowering_passes`, `run_runtime_cleanup_passes` | `641–698` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs` | `CleanupPostBorrowck` | `24–90` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_mir_transform/src/remove_noop_landing_pads.rs` | `RemoveNoopLandingPads`, `find_noop_landing_pads_for_instance` | `12–185` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_mir_transform/src/elaborate_drops.rs` | `ElaborateDrops` `Unwind::InCleanup` dispatch | `348–380` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs` | `AbortUnwindingCalls` (`PassPolicy::Required`) | `25–147` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_mir_transform/src/validate.rs` | `CfgChecker::{check_edge, check_cleanup_control_flow, check_unwind_edge, is_critical_call_edge}` | `118–281` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_codegen_ssa/src/mir/block.rs` | `do_call`, `terminate_block` | `215–335`, `2253–2420` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `compiler/rustc_codegen_llvm/src/abi.rs` | `apply_attrs_llfn`, `apply_attrs_callsite` (`NoUnwind`) | `650–674`, `821–830` | source |
| `rust-lang/rust` | `960ba7cf7e8666ecb449402ca82b6e9e631bd227` | `library/core/src/panicking.rs` | `panic_fmt`, `panic_cannot_unwind`, `panic_in_cleanup` | `59–103`, `340–370` | source |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_middle/src/ty/layout.rs`, `abort_unwinding_calls.rs`, `builder/scope.rs`, `library/core/src/panicking.rs` | Nightly `1.98.0-nightly (2026-05-31)` version diff | `layout.rs:1236–1297` | source + execution |
| `llvm/llvm-project` | `510c32aa35634c7298181857d7bcd92ca9457d1f` | `llvm/include/llvm/IR/Attributes.td` | `NoUnwind` enum attr | `265` | normative |
| `llvm/llvm-project` | `510c32aa35634c7298181857d7bcd92ca9457d1f` | `llvm/docs/LangRef.md` | `nounwind` undefined-behavior rule | `2573–2579` | normative |
| `llvm/llvm-project` | `510c32aa35634c7298181857d7bcd92ca9457d1f` | `llvm/docs/ExceptionHandling.md` | Cleanup propagation restriction & filters | `250–284` | documentation |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean` | `UnwindAction`, `TerminatorKind` | `693–795` | source |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirSemantics.lean` | `evalTerminator` fault classification | `1568–1569` | source |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/correspondence/Trusted/Correspondence.lean` | `toMiriTerminatorForDispatch` | `2048–2063` | source |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/rustc-capture/src/driver.rs` | `COMPILER_VERSION`, `AnalysisCallbacks` | `25–152` | source |

### Empirical Compiler Probe & Execution Receipts

- **Probe script:** `support/probe_unwind_action_c_unwind_abi.py` (`11,608` bytes, `427` lines, isolated inside `tempfile.TemporaryDirectory()`).
- **Recorded results:** `support/probe_results.json` (`82,788` bytes, recorded `observed_utc = "2026-11-23T16:11:30Z"`):
  - `rustc --version --verbose`: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, host `x86_64-unknown-linux-gnu`, LLVM `22.1.6`.
  - Experiment A (`a_mir_and_llvm_ir_unwind_matrix`): `mir_compile_rc = 0` and `llvm_compile_rc = 0` across all three flag sets (`[-Cpanic=unwind]`, `[-Cpanic=abort, -Zpanic_abort_tests]`, `[-Cpanic=abort]`), capturing 42 MIR dumps (`7` target functions × `2` before/after × `3` modes) and 21 extracted LLVM IR functions plus panic/foreign declarations and function attribute groups.
  - Experiment B (`b_native_catch_unwind_vs_c_abi_abort`): 5 standalone compiled binaries reproducing `catch_unwind` recovery across `extern "C-unwind"` (`rc = 0`) and deterministic `SIGABRT` (`rc = -6`) across `extern "C"` panic, `extern "C"` panic after local `Drop` (`DROP_RAN_IN_C_ABI` preceding `panic_cannot_unwind`), double panic inside `Drop` (`panic_in_cleanup`), and `extern "C-unwind"` panic under `-Cpanic=abort`.

### Mechanized Lean `v4.34.1` Soundness Evidence

- **Development file:** `support/MirUnwindActionAbortUnwindingSoundness.lean` (`290,339` bytes, `6,181` lines), checked against `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Kernel verification flags:** `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/MirUnwindActionAbortUnwindingSoundness.lean` exited with code `0`.
- **Printed axiom signatures:** All five printed top-level theorems depend exclusively on `[propext, Quot.sound]`:
  - `MirUnwindSoundness.abortUnwindingCalls_exact_soundness` (line `3634`)
  - `MirUnwindSoundness.double_panic_inCleanup_termination` (line `4106`)
  - `MirUnwindSoundness.eraseDeadCleanup_preserves_WF_and_exec` (line `4981`)
  - `MirUnwindSoundness.llvm_nounwind_never_escapes` (line `5933`)
  - `MirUnwindSoundness.mir_llvm_lockstep_sim` (line `5901`)
- **Complete environment MetaM audit (`Lean.Elab.runFrontend` + `Lean.collectAxioms`):** Over all `322` theorems and `680` definitions under `MirUnwindSoundness.*`, `unsafeRecs = 0`, `partialOrUnsafe = 0`, and `badAxiomDecls = 0` (`METAM_AUDIT_PASSED`). Zero uses of placeholder stubs, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial def`, `deriving`, or `noncomputable section`, and zero non-`noncomputable def` term definitions.

## Revalidation

1. **Re-run the live `rustc` MIR/LLVM/native probe inside an isolated temporary directory:**

```bash
python3 reports/rustc-mir-unwind-action-abort-unwinding-calls-c-unwind-abi-and-double-panic/support/probe_unwind_action_c_unwind_abi.py \
  --rustc rustc \
  --output /tmp/revalidate_probe_results.json
```

Confirm: (a) `mir_compile_rc == 0` and `llvm_compile_rc == 0` in all modes, (b) `call_foreign_c_unwind` and `call_indirect_c_unwind` retain `unwind: bb2 -> terminate(abi)` and LLVM `invoke ... unwind label %cleanup` under `-C panic=abort`, and (c) `extern_c_with_drop_runs_drop_before_abort` prints `DROP_RAN_IN_C_ABI` strictly before `"panic in a function that cannot unwind"` with `run_returncode == -6`.

2. **Re-verify upstream `rustc` and `anneal` decision sites against newer commits:**
   - Diff `compiler/rustc_middle/src/ty/layout.rs` (`fn_can_unwind`)—specifically whether `!tcx.is_foreign_item(did)` still exempts foreign `extern "C-unwind"` items under `-C panic=abort`.
   - Diff `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs` (`AbortUnwindingCalls`) and `remove_noop_landing_pads.rs` (`RemoveNoopLandingPads::policy`)—specifically whether `AbortUnwindingCalls` still skips `block.is_cleanup` and whether `RemoveNoopLandingPads` still requires `ctx.panic_strategy().unwinds()`.
   - Diff `compiler/rustc_codegen_ssa/src/mir/block.rs` (`do_call`, `terminate_block`) and `compiler/rustc_codegen_llvm/src/abi.rs` (`NoUnwind` emission).
   - Inspect `joshlf/anneal`'s `trusted/lean/Trusted/MirAst.lean` (`UnwindAction`, `TerminatorKind`) and `MirSemantics.lean` (`evalTerminator`) to test whether multi-frame unwinds and `UnwindTerminateReason` are now represented.

3. **Re-check the Lean `v4.34.1` formalization with full kernel verification:**

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  reports/rustc-mir-unwind-action-abort-unwinding-calls-c-unwind-abi-and-double-panic/support/MirUnwindActionAbortUnwindingSoundness.lean
```

Confirm exit code `0`, zero warnings, and `[propext, Quot.sound]` across all `#print axioms` lines.

4. **Re-validate the corpus package:**

```bash
python3 tools/reference.py catalog && python3 tools/reference.py check
```
