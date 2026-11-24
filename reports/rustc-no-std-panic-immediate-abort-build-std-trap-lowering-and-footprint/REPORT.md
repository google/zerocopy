# No-std Panic Strategies: Unwind, Abort, and Immediate-Abort Codegen, Core Rebuild Requirements, `@llvm.trap` Lowering, and Panic-Handler Exemption

## Summary

Basis: `source` (`rust-lang/rust` HEAD `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`, `llvm/llvm-project` HEAD `354891a804ac4eefa45a9a546cceed4404b18b78`, `joshlf/anneal` `main` `c131b320eeeb26ef692e5afd5ec8db49ee518613`), `execution` (`rustc 1.98.0-nightly`, `LLVM 22.1.6`, `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`), `derived` (`NoStdPanicImmediateAbortTrapAndFootprintSoundness.lean`, verified under `leanprover/lean4` `v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52`).

In `#![no_std]` Rust compilation targeting native ELF architectures, the three `PanicStrategy` modes (`unwind`, `abort`, and nightly `immediate-abort`) separate cleanly across **four distinct compiler layers** rather than a single SSA toggle:

1. **Same Normal-Path Codegen (`Runtime` MIR and Fast Paths Agree):** Across all three strategies (`-Cpanic=unwind`, `-Cpanic=abort`, and `-Zunstable-options -Cpanic=immediate-abort`), checked arithmetic, division checks, and slice bounds checks still emit identical normal-path instructions (`udiv` / `mov` load) preceded by the same `TerminatorKind::Assert` guard in optimized MIR (`runtime-optimized`), differing on the MIR edge only in the `UnwindAction` annotation (`unwind terminate(abi)` under `unwind` vs. `unwind unreachable` under `abort` and `immediate-abort`, rewritten by `AbortUnwindingCalls`).
2. **SSA Lowering Does Not Short-Circuit `immediate-abort`:** Contrary to naive assumptions, `rustc_codegen_ssa::mir::block::MirBuilder::codegen_assert_terminator` (`compiler/rustc_codegen_ssa/src/mir/block.rs:753-858`) still materializes a 24-byte `core::panic::Location<'static>` pointer and still emits a direct `tail call` (or `call` at `-O0`) to the corresponding `core::panicking::panic_*` lang-item function even when `-Cpanic=immediate-abort` is active. Immediate-abort trap elimination is delegated entirely to the `core` library's `#[cfg(panic = "immediate-abort")]` gates and LLVM optimization.
3. **Why Rebuilding `core` (`-Zbuild-std=core`) Is Mandatory for Trap Elimination and `cdylib` Linkage:** Prebuilt sysroot `core` crates are compiled with `#[cfg(not(panic = "immediate-abort"))]`, leaving `core::panicking::*` marked `#[inline(never), cold]` and forwarding to `panic_fmt`/`panic_impl`. Consequently, compiling an unlinked library (`--crate-type=lib`/`rlib`) with `-Cpanic=immediate-abort` against the prebuilt sysroot silently emits external `core::panicking::*` symbols and 48 bytes of static `Location` `.data` tables (`text=210 B, data=48 B` for the two-function probe, matching `-Cpanic=abort`'s `2` undefined symbols and `48 B` `.data` while still omitting unwinding landing pads), whereas linkable outputs (`cdylib`) fail deterministically in `rustc_metadata::dependency_format::verify_ok` because `core` lacks `PanicStrategy::ImmediateAbort` (`error: the crate core was compiled with a panic strategy which is incompatible with immediate-abort`), **even if** a `#[panic_handler]` is supplied. Rebuilding `core` with `-Zbuild-std=core` switches `core::panicking::*` to `#[inline]` calling `intrinsics::abort[_immediate]()` (`llvm.trap`), allowing LLVM `-Copt-level=2` (`--release`) + GlobalDCE to collapse every failure path to `tail call void @llvm.trap(); unreachable` (`text=88 B, data=0 B` on `x86_64` with `0f 0b ud2`; `text=100 B, data=0 B` on `aarch64` with `brk #0x1`, **zero** undefined symbols, and **zero** `.data` location tables).
4. **`#[panic_handler]` Signature (`-> !`) and Uniquely Conditional Exemption:** During HIR typechecking (`compiler/rustc_hir_typeck/src/check.rs:165-235`), any defined `#[panic_handler]` (`#[lang = "panic_impl"]`) must unify with `for<'a, 'b> fn(&'a PanicInfo<'b>) -> !`; returning `()` is rejected with `E0308`. During post-resolution weak lang-item checking (`compiler/rustc_resolve/src/late/weak_lang_items.rs:27-61` and `compiler/rustc_middle/src/middle/lang_items.rs:128-137`), `lang_items::required` requires both `PanicImpl` and `EhPersonality` under `unwind`, requires `PanicImpl` alone under `abort`, and returns `false` for both under `immediate-abort`. Linkable `cdylib` probes confirm this split empirically: omitting `#[panic_handler]` fails under `abort` and `unwind`, passes under `-Zbuild-std=core -Zunstable-options -Cpanic=immediate-abort` at both `--release` (inlined `ud2`) and `--profile=dev` (non-inlined local monomorphized `core::panicking` bodies executing `ud2` directly without calling `panic_impl`, albeit retaining `96 B` `.data`), and passes in `rlib` builds only because `rlib` skips weak lang-item and dependency-format linkage checks.
5. **Opt-Level Boundary (`-O0` vs. `-O2`) and Dual `cfg` Trap:** Because `library/core/src/panicking.rs` uses `#[cfg_attr(panic = "immediate-abort", inline)]` (`InlineHint`) rather than `#[inline(always)]`, rebuilding `core` at `-O0` (`--profile=dev`) still calls monomorphized `core::panicking::*` helpers and retains `96 B` `.data` (`Location` tables) and `1,981 B` (lib) / `2,006 B` (cdylib) `.text` in the probe object even though `cdylib` links cleanly without a `#[panic_handler]`. Additionally, `-Cpanic=immediate-abort` sets **both** `cfg(panic = "immediate-abort")` and `cfg(panic = "abort")` (`compiler/rustc_session/src/config/cfg.rs:218-221`), verified live via `cfg_flags_mask() -> ret i32 3`.
6. **Lean v4.34.1 Mechanization (`>= 2,270` LOC, Zero `sorry`, Zero `Classical.choice`, Zero `._unsafe_rec`):** The companion standalone proof in `support/NoStdPanicImmediateAbortTrapAndFootprintSoundness.lean` (`2,278` lines, `67` `noncomputable def`s, `40` explicit `theorem`s, checked strictly via `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and audited via Lean MetaM across `1,204` generated constants) establishes end-to-end kernel-checked theorems for: (1) normal-path MIR/LLVM agreement across all three strategies, (2) zero external symbols and zero `.data` tables under `immediate-abort` + rebuilt `core` + `optLevel >= 1`, (3) prebuilt-core `cdylib` rejection vs. `rlib` bypass symbol/table retention, and (4) `#[panic_handler]` `-> !` signature soundness and weak lang-item exemption soundness.

## Applicability

Basis: `source`, `execution`, `derived`.

- **Primary Upstream Commits Audited:**
  - `rust-lang/rust` HEAD commit `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` (compiler frontend, `rustc_target`, `rustc_session`, `rustc_middle`, `rustc_resolve`, `rustc_hir_typeck`, `rustc_mir_transform`, `rustc_metadata`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, `library/core`).
  - `llvm/llvm-project` HEAD commit `354891a804ac4eefa45a9a546cceed4404b18b78` (`Intrinsics.td`, `X86InstrSystem.td`, `AArch64InstrInfo.td`).
  - `joshlf/anneal` `main` commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirSemantics.lean`).
  - `leanprover/lean4` tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- **Executed Toolchain & Targets:**
  - `rustc 1.98.0-nightly` (`commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `commit-date: 2026-05-31`, `LLVM version: 22.1.6`, `host: x86_64-unknown-linux-gnu`). Note that `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` is the binary's locally reported nightly toolchain hash (not resolved on the default upstream `rust-lang/rust` commit API endpoint at time of audit, which returns HTTP 422), whereas upstream source anchors were resolved live at `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`.
  - Cross-version intrinsic distinction observed directly between the executed toolchain's sysroot `library/core/src/panicking.rs` and upstream HEAD `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`: in `1.98.0-nightly` (`14210df0e`), `core::panicking` calls `super::intrinsics::abort()` (`core/src/intrinsics/mod.rs:369-371`) under `if cfg!(panic = "immediate-abort")`; at `rust-lang/rust` HEAD (`f7da9a423`), the compiler-intrinsic entry point for immediate-abort panics has been separated into `super::intrinsics::abort_immediate()` (`library/core/src/intrinsics/mod.rs:636-638`), dispatched in `rustc_codegen_ssa::mir::intrinsic` (`compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:145,177-178`) -> `BuilderMethods::abort_immediate()` (`compiler/rustc_codegen_llvm/src/intrinsic.rs:1081-1083`). In both toolchains, the emitted LLVM IR intrinsic is identical (`llvm.trap`), yielding identical machine instructions (`ud2` on `x86_64`, `brk #0x1` on `aarch64`).
  - Targets empirically built with `-Zbuild-std=core --offline`: `x86_64-unknown-linux-gnu` (`--release` `-Copt-level=3` default release and `--profile=dev` `-Copt-level=0`, for both `lib` and `cdylib`) and `aarch64-unknown-linux-gnu` (`--release`, `lib` / ELF object emission).
  - Prebuilt sysroot probes executed directly via `rustc --edition 2024` for `-Copt-level=2` across `--crate-type=lib`, `--crate-type=rlib`, and `--crate-type=cdylib`.
- **Module Relocation Note Relative to Older `rustc` Literature:**
  - In `rust-lang/rust` HEAD (`f7da9a423`), weak lang-item missing-symbol enforcement (`MissingPanicHandler`, `PanicUnwindWithoutStd`) does **not** reside in `compiler/rustc_hir_analysis/src/lang_items.rs` (which no longer exists at that path; HTTP 404). It resides across `compiler/rustc_resolve/src/late/weak_lang_items.rs:1-61` and `compiler/rustc_middle/src/middle/lang_items.rs:128-137`, while `#[panic_handler]` typechecking (`fn(&PanicInfo<'_>) -> !`) resides in `compiler/rustc_hir_typeck/src/check.rs:165-235`.

## Findings

### 1. Option Parsing, Nightly/Unstable Gating, and Dual `cfg(panic = ...)` Injection

Basis: `source` (`compiler/rustc_target/src/spec/mod.rs:818-849`, `compiler/rustc_session/src/options.rs:917,1317-1326`, `compiler/rustc_session/src/config.rs:2770-2774`, `compiler/rustc_session/src/config/cfg.rs:214-221`), `execution` (`sysroot_immediate_abort_requires_unstable_options`, `sysroot_lib_cfg_panic_immediate_abort_dual_cfg`).

- **Enum Variants and Parsing:** `PanicStrategy` (`compiler/rustc_target/src/spec/mod.rs:820-824`) defines exactly three strategies: `Unwind = "unwind"`, `Abort = "abort"`, and `ImmediateAbort = "immediate-abort"`. Its helpers `desc_symbol()` and `unwinds()` (`compiler/rustc_target/src/spec/mod.rs:838-848`) map `ImmediateAbort` to `sym::immediate_abort` and return `unwinds() == matches!(self, PanicStrategy::Unwind)` (so `unwinds()` is `false` for both `Abort` and `ImmediateAbort`). CLI option parsing (`parse_opt_panic_strategy`, `compiler/rustc_session/src/options.rs:1317-1326`) recognizes `"unwind"`, `"abort"`, and `"immediate-abort"`.
- **Gate Enforcement (`-Zunstable-options` + Nightly):** In `compiler/rustc_session/src/config.rs:2770-2774`, setting `-Cpanic=immediate-abort` without `-Zunstable-options` triggers `early_dcx.early_fatal`:
  > `` `-Cpanic=immediate-abort` requires `-Zunstable-options` and a nightly compiler ``
  Empirical execution (`probe_results.json`: `sysroot_immediate_abort_requires_unstable_options`) reproduces this exact exit-code-`1` error byte-for-byte when `-Zunstable-options` is omitted.
- **Dual `cfg` Trap (`cfg(panic = "immediate-abort")` AND `cfg(panic = "abort")`):** `compiler/rustc_session/src/config/cfg.rs:218-221` inserts **both** config flags whenever `sess.panic_strategy() == PanicStrategy::ImmediateAbort`:
  ```rust
  ins_sym!(sym::panic, sess.panic_strategy().desc_symbol());
  if sess.panic_strategy() == PanicStrategy::ImmediateAbort {
      ins_sym!(sym::panic, PanicStrategy::Abort.desc_symbol());
  }
  ```
  As the upstream comment notes (`cfg.rs:215-217`), this prevents code testing `cfg(panic = "abort")` for non-unwinding assumptions from having to update; conversely, crates must order `#![cfg(panic = "immediate-abort")]` checks carefully rather than assuming `cfg(panic = "abort")` implies availability of `#[panic_handler]` formatting. Our live probe `cfg_flags_mask()` (`probe_results.json`: `sysroot_lib_cfg_panic_immediate_abort_dual_cfg`) evaluates bitwise mask `(immediate-abort ? 1 : 0) | (abort ? 2 : 0) | (unwind ? 4 : 0)` and compiles at `-Copt-level=2` to constant `ret i32 3` (`b8 03 00 00 00 c3`: `movl $0x3, %eax; retq`).

### 2. MIR Transformation Pipeline (`AbortUnwindingCalls` & `fn_can_unwind`)

Basis: `source` (`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:25-147`, `compiler/rustc_middle/src/ty/layout.rs:1360-1390`), `execution` (`mir_post_cleanup` stages `runtime-post-cleanup` and `runtime-optimized`).

- **Same `AbortUnwindingCalls` Effect Under `Abort` and `ImmediateAbort`:** In `rustc_middle::ty::layout::fn_can_unwind` (`compiler/rustc_middle/src/ty/layout.rs:1371-1373`), whenever `!tcx.sess.panic_strategy().unwinds()` (`false` for both `Abort` and `ImmediateAbort`) and a function is non-foreign, `fn_can_unwind` returns `false`.
- Inside `AbortUnwindingCalls::run_pass` (`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:78-136`):
  - For `TerminatorKind::Assert` and calls whose callee cannot unwind (`!call_can_unwind`), `*cleanup` is rewritten to `UnwindAction::Unreachable` (`L117-123`).
  - Any remaining `TerminatorKind::UnwindResume` inside a non-unwinding body is rewritten to `TerminatorKind::UnwindTerminate(UnwindTerminateReason::Abi)` (`L81-83`).
- **Live MIR Inspection (`runtime-post-cleanup` and `runtime-optimized`):** Across all three `-Cpanic` strategies (`-Zdump-mir=all`, `CORE_PROBE_LIB_RS`), the optimized MIR (`runtime-optimized`) for `div` and `idx` exhibits **identical** computation statements and conditional `assert(...)` predicates, differing **solely** in the unwind target annotation:
  - Under `-Cpanic=unwind`:
    - `div`: `assert(!move _3, "attempt to divide `{}` by zero", copy _1) -> [success: bb1, unwind terminate(abi)];`
    - `idx`: `assert(move _4, "index out of bounds: the length is {} but the index is {}", copy _2, copy _3) -> [success: bb1, unwind terminate(abi)];`
  - Under **both** `-Cpanic=abort` and `-Cpanic=immediate-abort`, `runtime-optimized` IR is **character-for-character identical**:
    - `div`: `assert(!move _3, "attempt to divide `{}` by zero", copy _1) -> [success: bb1, unwind unreachable];`
    - `idx`: `assert(move _4, "index out of bounds: the length is {} but the index is {}", copy _2, copy _3) -> [success: bb1, unwind unreachable];`
- **Verification Implication:** Neither `abort` nor `immediate-abort` removes `TerminatorKind::Assert` from MIR. Both strategies defer panic-implementation specialization to SSA lowering (`UnwindAction::Unreachable` vs. `Terminate`) and core-library monomorphization/inlining.

### 3. Codegen SSA Still Emits `core::panicking` Langcalls; Trap Elimination Happens Inside `core` + LLVM

Basis: `source` (`compiler/rustc_codegen_ssa/src/mir/block.rs:753-889`, `library/core/src/panicking.rs:54-354`, `library/core/src/intrinsics/mod.rs:636-638`, `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:145,177-178`, `compiler/rustc_codegen_llvm/src/intrinsic.rs:1081-1083`), `execution` (`prebuilt_sysroot` and `rebuild_core_via_build_std`).

A central architectural discovery of this audit is that **`rustc_codegen_ssa` has no fast-path bypass that lowers `TerminatorKind::Assert` directly to `llvm.trap` under `-Cpanic=immediate-abort`**:

1. **Unchanged SSA Langcall Emission:** In `MirBuilder::codegen_assert_terminator` (`compiler/rustc_codegen_ssa/src/mir/block.rs:799-858`), `codegen_ssa` unconditionally:
   - Materializes `let location = self.get_caller_location(bx, terminator.source_info).immediate();` (a 24-byte `core::panic::Location<'static>` constant: `{ filename: NonNull<str> (16 B), line: u32 (4 B), col: u32 (4 B) }`);
   - Selects a lang item such as `LangItem::PanicBoundsCheck` or `msg.panic_function()` (`PanicConstDivByZero` etc.);
   - Calls `common::build_langcall(bx, span, lang_item)` and emits `helper.do_call(...)` (`invoke` under `unwind`, `tail call`/`call` under `abort` and `immediate-abort`).
   - Similarly, `codegen_terminate_terminator` (`block.rs:860-889`) calls `common::build_langcall(bx, span, reason.lang_item())` (`PanicCannotUnwind`).
2. **Where Immediate-Abort Actually Lives (`library/core/src/panicking.rs`):** Inside `core::panicking` (`library/core/src/panicking.rs:54-63`, `86-104`, `265-350`), every panic lang-item entry point carries dual attributes and an inline `cfg!` branch:
   ```rust
   #[cfg_attr(not(panic = "immediate-abort"), inline(never), cold, optimize(size))]
   #[cfg_attr(panic = "immediate-abort", inline)]
   #[track_caller]
   #[lang = "panic_bounds_check"]
   fn panic_bounds_check(index: usize, len: usize) -> ! {
       if cfg!(panic = "immediate-abort") {
           super::intrinsics::abort_immediate() // `super::intrinsics::abort()` in 1.98.0-nightly sysroot src
       }
       panic!("index out of bounds: ...")
   }
   ```
   When `core` is compiled with `-Cpanic=immediate-abort`, dead-branch elimination on `if cfg!(panic = "immediate-abort")` reduces each `core::panicking::*` MIR/LLVM body to an `#[inline]` stub executing solely `abort[_immediate]()`, which `rustc_codegen_llvm::intrinsic::BuilderMethods::abort_immediate` (`compiler/rustc_codegen_llvm/src/intrinsic.rs:1081-1083`) lowers via `self.call_intrinsic("llvm.trap", &[], &[])`.
3. **Why Prebuilt Sysroot Fails Trap Elimination and Rejects `cdylib`:**
   - Prebuilt `libcore.rlib` ships compiled with `-Cpanic=unwind` (or `abort` on select targets), **not** `-Cpanic=immediate-abort`. Therefore its compiled `core::panicking::*` symbols remain `#[inline(never), cold]` external calls referencing `panic_impl`, and carry **metadata marker** `required_panic_strategy != Some(ImmediateAbort)`.
   - **Prebuilt Sysroot + `--crate-type=lib` (`rlib`) Explains the Silent Fallback Trap:** For `--crate-type=lib` / `rlib`, `dependency_format::calculate_type` (`compiler/rustc_metadata/src/dependency_format.rs:125`) assigns `Linkage::NotLinked`, causing `verify_ok` (`L417-419`) to return early without checking `core`. As a result, `rustc --crate-type=lib -Copt-level=2 -Zunstable-options -Cpanic=immediate-abort` succeeds (`rc = 0`), **but emits external calls and static `Location` `.data` tables**:
     - `div`: `tail call void @...panic_const_div_by_zero(ptr ... @alloc_...) #3; unreachable`
     - `idx`: `tail call void @...panic_bounds_check(i64 %i, i64 %len, ptr ... @alloc_...) #3; unreachable`
     - `llvm-nm -u`: 2 undefined `core::panicking::*` symbols (`panic_bounds_check`, `panic_const_div_by_zero`).
     - `llvm-size`: `text=210 B, data=48 B` (`2 x 24 B` `Location` records; zero `.data` reduction compared to `-Cpanic=abort`'s `text=182 B, data=48 B`, and identical x86 machine code in `.text.div` and `.text.idx`!).
   - **Prebuilt Sysroot + `--crate-type=cdylib` Is Explicitly Rejected:** For linkable artifacts (`Cdylib`, `Dylib`, `StaticLib`, `ProcMacro`, `Executable`), `verify_ok` (`compiler/rustc_metadata/src/dependency_format.rs:424-444`) detects that a dependency node has `ImmediateAbort` while `core` does not, and immediately calls `sess.dcx().emit_fatal(IncompatibleWithImmediateAbortCore)` (`compiler/rustc_metadata/src/diagnostics.rs:89-99`):
     > `error: the crate core was compiled with a panic strategy which is incompatible with immediate-abort`
     Both without and **with** an explicit `#[panic_handler]` (`sysroot_cdylib_immediate_abort_with_panic_handler_also_rejected`), `cdylib` against prebuilt `core` fails identically with exit code `1`.

### 4. Empirical LLVM IR, Function Attributes, Symbol Elimination, and Hardware Traps

Basis: `source` (`llvm/include/llvm/IR/Intrinsics.td:2093-2096`, `llvm/lib/Target/X86/X86InstrSystem.td:25`, `llvm/lib/Target/AArch64/AArch64InstrInfo.td:11217`), `execution` (`probe_no_std_panic_strategies.py` -> `probe_results.json`).

#### 4.1 Complete Measured Footprint & Symbol Matrix (`rustc 1.98.0-nightly`, `LLVM 22.1.6`)

Running `CORE_PROBE_LIB_RS` (exported `#[unsafe(no_mangle)] pub extern "C" fn div(a: u32, b: u32) -> u32` and `pub unsafe extern "C" fn idx(s: *const u32, len: usize, i: usize) -> u32`) across prebuilt sysroot and `-Zbuild-std=core` yields the exact measured artifact table below:

| Probe Configuration | Crate Type | Profile / Opt | Outcome (`rc`) | `.text` (B) | `.data` (B) | Undefined Panic / Runtime Symbols (`llvm-nm -u` on `.o`) | `@llvm.trap` Count (`div`+`idx`) | Personality (`@rust_eh_personality`) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Sysroot `-Cpanic=unwind` | `lib` | `-Copt-level=2` | `0` (OK) | `265` | `56` | `4` (`panic_bounds_check`, `panic_cannot_unwind`, `panic_const_div_by_zero`, `rust_eh_personality`) | `0` | Present (both fns, `invoke` + `landingpad`) |
| Sysroot `-Cpanic=abort` | `lib` | `-Copt-level=2` | `0` (OK) | `182` | `48` | `2` (`panic_bounds_check`, `panic_const_div_by_zero`) | `0` | Absent |
| Sysroot `-Zunstable-options -Cpanic=immediate-abort` (NO `-Zbuild-std`) | `lib` | `-Copt-level=2` | `0` (OK) | `210` | `48` | `2` (`panic_bounds_check`, `panic_const_div_by_zero`) | `0` | Absent |
| Sysroot `-Zunstable-options -Cpanic=immediate-abort` (NO handler) | `cdylib` | `-Copt-level=2` | `1` (Fatal) | — | — | `IncompatibleWithImmediateAbortCore` | — | — |
| Sysroot `-Zunstable-options -Cpanic=immediate-abort` (WITH handler) | `cdylib` | `-Copt-level=2` | `1` (Fatal) | — | — | `IncompatibleWithImmediateAbortCore` | — | — |
| `-Zbuild-std=core` `-Cpanic=unwind` (`x86_64`) | `lib` | `--release` | `0` (OK) | `211` | `56` | `4` (`panic_bounds_check`, `panic_cannot_unwind`, `panic_const_div_by_zero`, `rust_eh_personality`) | `0` | Present (both fns, `invoke` + `landingpad`) |
| `-Zbuild-std=core` `-Cpanic=abort` (`x86_64`) | `lib` | `--release` | `0` (OK) | `129` | `48` | `2` (`panic_bounds_check`, `panic_const_div_by_zero`) | `0` | Absent |
| `-Zbuild-std=core` `-Cpanic=immediate-abort` (`x86_64`) | `lib` | `--release` | `0` (OK) | `88` | `0` | `0` (`[]`) | `2` (`1 + 1`) | Absent |
| `-Zbuild-std=core` `-Cpanic=immediate-abort` (NO handler, `x86_64`) | `cdylib` | `--release` | `0` (OK) | `88` (`.o`) / `904` (`.so`) | `0` (`.o`) / `440` (`.so`) | `0` on `.o` (`.so` has only CRT weak refs `_ITM_*`, `__cxa_finalize`, `__gmon_start__`) | `2` (`1 + 1`) | Absent |
| `-Zbuild-std=core` `-Cpanic=immediate-abort` (`x86_64`) | `lib` | `--profile=dev` (`-O0`) | `0` (OK) | `1981` | `96` | `2` non-panic `const_ptr::{is_aligned_to, is_null}`; calls local `panic_const_*` / `panic_bounds_check` | `0` in `div`/`idx` (`declare @llvm.trap` present in `.ll`) | Absent |
| `-Zbuild-std=core` `-Cpanic=immediate-abort` (NO handler, `x86_64`) | `cdylib` | `--profile=dev` (`-O0`) | `0` (OK) | `2006` (`.o`) / `4087` (`.so`) | `96` (`.o`) / `600` (`.so`) | `0` panic symbols; monomorphized `panic_*` stubs emit `ud2` locally | `0` in `div`/`idx` (inside local stubs) | Absent |
| `-Zbuild-std=core` `-Cpanic=immediate-abort` (`aarch64`) | `lib` | `--release` | `0` (OK) | `100` | `0` | `0` (`[]`) | `2` (`1 + 1`) | Absent |

#### 4.2 Exact LLVM IR Transformation & Attribute Inference

With `-Zbuild-std=core --release -Zunstable-options -Cpanic=immediate-abort`, inlining `core::panicking` followed by LLVM's Dead Argument Elimination / GlobalDCE removes all references to both `core::panicking::*` functions and `@alloc_*` `Location` globals:

```llvm
define noundef i32 @div(i32 noundef %a, i32 noundef %b) unnamed_addr #0 {
start:
  %_3 = icmp eq i32 %b, 0
  br i1 %_3, label %panic, label %bb1

bb1:                                              ; preds = %start
  %_0 = udiv i32 %a, %b
  ret i32 %_0

panic:                                            ; preds = %start
  tail call void @llvm.trap()
  unreachable
}
```

And for `idx`:

```llvm
define noundef i32 @idx(ptr noundef readonly captures(none) %s, i64 noundef %len, i64 noundef %i) unnamed_addr #1 {
start:
  %_4 = icmp ult i64 %i, %len
  br i1 %_4, label %bb1, label %panic

bb1:                                              ; preds = %start
  %0 = getelementptr inbounds nuw i32, ptr %s, i64 %i
  %_0 = load i32, ptr %0, align 4, !noundef !4
  ret i32 %_0

panic:                                            ; preds = %start
  tail call void @llvm.trap()
  unreachable
}
```

- **Module-Level Declarations:** The entire `llvm_decls` set collapses to a single declaration: `declare void @llvm.trap() #2` (`[]` undefined symbols in `llvm-nm -u`).
- **Precise Memory-Effect Refinement (`FunctionAttrs` + `Intrinsics.td`):** Upstream `llvm/include/llvm/IR/Intrinsics.td:2093-2096` declares:
  ```tablegen
  def int_trap : Intrinsic<[], [],
                    [IntrNoReturn, IntrCold, IntrInaccessibleMemOnly,
                     IntrWriteMem]>,
                 ClangBuiltin<"__builtin_trap">;
  ```
  Because `int_trap` carries `IntrInaccessibleMemOnly` and `IntrWriteMem` rather than arbitrary memory clobbers (contrast prebuilt `panic_const_div_by_zero`, whose `#0` carries no restricted `memory(...)` attribute), LLVM `FunctionAttrs` infers strictly tighter signatures verified live in `probe_results.json`:
  - `div` (`#0` on `x86_64`): `attributes #0 = { nounwind nonlazybind memory(inaccessiblemem: write) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }`
  - `idx` (`#1` on `x86_64`): `attributes #1 = { nounwind nonlazybind memory(argmem: read, inaccessiblemem: write) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }`
  - Same `memory(inaccessiblemem: write)` / `memory(argmem: read, inaccessiblemem: write)` inference holds identically on `aarch64` (`"target-cpu"="generic" "target-features"="+v8a,+outline-atomics"`).

#### 4.3 Exact Target ISA Lowering (`x86_64` `ud2` vs. `aarch64` `brk #0x1`)

In LLVM target backends:
- On `x86_64` (`llvm/lib/Target/X86/X86InstrSystem.td:25`), `def TRAP : I<0x0B, RawFrm, (outs), (ins), "ud2", [(trap)]>, TB;` emits the 2-byte illegal instruction `0f 0b ud2`:
  ```asm
  0000000000000000 <div>:
         0: 85 f6                        testl   %esi, %esi
         2: 74 07                        je      0xb <div+0xb>
         4: 89 f8                        movl    %edi, %eax
         6: 31 d2                        xorl    %edx, %edx
         8: f7 f6                        divl    %esi
         a: c3                           retq
         b: 0f 0b                        ud2

  0000000000000000 <idx>:
         0: 48 39 f2                     cmpq    %rsi, %rdx
         3: 73 04                        jae     0x9 <idx+0x9>
         5: 8b 04 97                     movl    (%rdi,%rdx,4), %eax
         8: c3                           retq
         9: 0f 0b                        ud2
  ```
- On `aarch64` (`llvm/lib/Target/AArch64/AArch64InstrInfo.td:11217`), `def : Pat<(trap), (BRK 1)>;` emits the 4-byte trap `d4200020 brk #0x1`:
  ```asm
  0000000000000000 <div>:
         0: 34000061     cbz     w1, 0xc <div+0xc>
         4: 1ac10800     udiv    w0, w0, w1
         8: d65f03c0     ret
         c: d4200020     brk     #0x1

  0000000000000000 <idx>:
         0: eb01005f     cmp     x2, x1
         4: 54000062     b.hs    0x10 <idx+0x10>
         8: b8627800     ldr     w0, [x0, x2, lsl #2]
         c: d65f03c0     ret
        10: d4200020     brk     #0x1
  ```
- Contrast this with `-Zbuild-std=core -Cpanic=unwind` and `-Cpanic=abort` on `x86_64`:
  - `-Cpanic=unwind` emits `pushq %rax`, `leaq` for `&Location`, `callq *(%rip)` (`panic_const_div_by_zero` / `panic_bounds_check`), a post-call `ud2`, plus the `terminate` landingpad call `callq *(%rip)` (`panic_cannot_unwind`) and `rust_eh_personality` unwind table, costing `211 B` `.text` and `56 B` `.data` (`div` takes 34 bytes, `idx` takes 38 bytes).
  - `-Cpanic=abort` removes the stack spill on the fast path, emitting `pushq %rax`, `leaq`, `callq *(%rip)` in the cold tail (`div`: 25 bytes, `idx`: 29 bytes), costing `129 B` `.text` and `48 B` `.data`.
  - `-Cpanic=immediate-abort` with rebuilt `core` eliminates `pushq %rax`, eliminates `leaq`, eliminates the GOT indirect `callq`, and places a bare 2-byte `0f 0b ud2` at the end of `div` (`13 B` total) and `idx` (`11 B` total), yielding `88 B` total `.text` and `0 B` `.data`.

### 5. Opt-Level (`-O0` / `--profile=dev`) Inlining Threshold Behavior

Basis: `source` (`library/core/src/panicking.rs:54-55,265-266`, `library/core/src/panicking.rs:95-105`), `execution` (`build_std_core_lib_immediate_abort_opt0`, `build_std_core_cdylib_immediate_abort_opt0_no_handler_ok`).

Because `core::panicking::*` uses `#[cfg_attr(panic = "immediate-abort", inline)]` (`InlineHint`) rather than `#[inline(always)]`:

- When compiling `-Zbuild-std=core --profile=dev -Zunstable-options -Cpanic=immediate-abort` (`-Copt-level=0`):
  - LLVM does not run the CGSCC inliner on `InlineHint` functions, nor does it inline `#[track_caller] core::slice::from_raw_parts`.
  - Consequently, `div` calls `@...panic_const_div_by_zeroCs..._11panic_probe(ptr @alloc_...)` and `idx` calls `@...from_raw_parts...` and `@...panic_bounds_checkCs..._11panic_probe(i64 %i, i64 %slice.1, ptr @alloc_...)`, with **zero** `@llvm.trap()` instructions inside `div` or `idx` (`llvm_trap_count: 0`) and `96 B` `.data` (`text=1,981 B` for `lib`, `2,006 B` for `cdylib`).
  - **Critically, `cdylib` still links with zero `#[panic_handler]` (`rc = 0`, `libpanic_probe.so` `text=4,087 B, data=600 B, bss=2,865 B`):** The monomorphized generic/local `panic_*` wrappers emitted into the local object unit call `core::panicking::panic_nounwind_fmt::runtime`, whose disassembly executes `0f 0b ud2` (`panic_const_div_by_zero` -> `panic_nounwind_fmt::runtime`: `12: 0f 0b ud2`) rather than calling `panic_impl`. Thus `--profile=dev` trades away **code-size and `.data` elimination**, not linkability!

### 6. `#[panic_handler]` HIR Typechecking, Weak Lang-Item Exemption, and Unsoundness Hazards

Basis: `source` (`compiler/rustc_hir_typeck/src/check.rs:165-235`, `compiler/rustc_resolve/src/late/weak_lang_items.rs:27-61`, `compiler/rustc_middle/src/middle/lang_items.rs:128-137`), `execution` (`b_no_std_panic_handler_abi_and_omission`).

1. **Non-Returning Signature Requirement (`-> !`):** `check_panic_info_fn` (`compiler/rustc_hir_typeck/src/check.rs:173-235`) verifies that a `#[panic_handler]` item is a function (`DefKind::Fn`), has `0` own type parameters and `0` own const parameters, emits lint `UNSAFE_PANIC_HANDLERS` if marked `unsafe`, and checks its signature via `ObligationCauseCode::LangFunctionType(sym::panic_impl)` against:
   `for<'a, 'b> fn(&'a PanicInfo<'b>) -> !` (`tcx.types.never`).
   Supplying `fn ph(_: &core::panic::PanicInfo) -> () {}` fails deterministically (`probe_results.json`: `invalid_panic_handler_unit_return_rejected_e0308`, `rc=1`):
   ```text
   error[E0308]: `#[panic_handler]` function has wrong type
    --> ...
     | fn ph(_: &core::panic::PanicInfo) -> () {}
     |                                      ^^ expected `!`, found `()`
   ```
   Supplying `-> !` on a `cdylib` with `-Cpanic=abort` succeeds (`valid_panic_handler_never_return_cdylib_ok`, `rc=0`).
2. **Exact Condition for Omitting `#[panic_handler]` (`lang_items::required`):** In `compiler/rustc_resolve/src/late/weak_lang_items.rs:30-59`, weak lang-item verification runs **only** when outputting a linkable artifact (`Dylib | ProcMacro | Cdylib | Executable | StaticLib | Sdylib`; skipped for `CrateType::Rlib`), checking:
   `if missing.contains(&item) && required(tcx, item) && items.get(item).is_none()`
   where `rustc_middle::middle::lang_items::required` (`L128-137`) evaluates:
   - `PanicStrategy::Unwind => true` (requires both `PanicImpl` and `EhPersonality`);
   - `PanicStrategy::Abort => lang_item != LangItem::EhPersonality` (requires `PanicImpl`, exempts `EhPersonality`);
   - `PanicStrategy::ImmediateAbort => false` (exempts **both** `PanicImpl` and `EhPersonality`).
   Live probes confirm all four cells:
   - `cdylib` + `abort` + missing handler -> `error: #[panic_handler] function required, but not found` (`rc = 1`);
   - `cdylib` + `unwind` + missing handler -> two errors (`#[panic_handler] function required, but not found` AND `error: unwinding panics are not supported without std`, `rc = 1`);
   - `rlib` + `abort` + missing handler -> passes (`rc = 0`) because `needs_check == false`;
   - `cdylib` + `-Zbuild-std=core -Zunstable-options -Cpanic=immediate-abort` + missing handler -> passes (`rc = 0`) cleanly with `0` undefined panic symbols because `core` never references `panic_impl` when built with `cfg!(panic = "immediate-abort")`.

### 7. Lean v4.34.1 Mechanization (`support/NoStdPanicImmediateAbortTrapAndFootprintSoundness.lean`)

Basis: `derived` (`NoStdPanicImmediateAbortTrapAndFootprintSoundness.lean`, `2,278` lines, `0` errors/warnings, `0` `sorry`, `0` `._unsafe_rec`).

To connect compiler flags, MIR `AbortUnwindingCalls`, `rustc_codegen_ssa` lowering, `core::panicking` inlining, `dependency_format`, weak lang-item validation, and target ISA traps in a single kernel-checked artifact, `support/NoStdPanicImmediateAbortTrapAndFootprintSoundness.lean` models the end-to-end compilation pipeline using strictly total constructive Lean (`noncomputable def`, zero `deriving`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`, verified across `1,204` MetaM constants):

- **Section 1 (`L79–L395`):** Models `PanicStrategy`, `cfgHasPanic`, `CrateType`, `needsLinkCheck`, `CoreBuildMode`, `langItemRequired`, `checkPanicHandlerSig`, `checkSessionGate`, `verifyDependencyFormat`, `checkWeakLangItems`, and `compileAdmitted`.
- **Section 2–3 (`L397–L1095`):** Formalizes MIR with `Assert`, `UnwindAction`, `UnwindResume`, `UnwindTerminate`, `AbortUnwindingCalls` (`abortUnwindingCallsTransform`), operational semantics (`evalMirBodyFuel`), `rustc_codegen_ssa` langcall+`CallerLoc` emission (`lowerMirBodyToLlvmGuarded`), `core::panicking` inlining + GlobalDCE + `FunctionAttrs` (`optimizeLlvmModule`), `evalLlvmFuncFuel`, and target ISA lowering (`x86Ud2`, `aarch64Brk1`).
- **Theorem 1 (`nonPanicking_behavioral_agreement_all_strategies`, `L1305`, and `mir_to_llvm_fastpath_agreement`, `L1350`):** Proves by induction on bounded execution `fuel` that for every `ExecutionPanicFree` program trace (where every reached `Assert` condition evaluates to `expected` and no `UnwindResume`/`UnwindTerminate` is hit), `.unwind`, `.abort`, and `.immediateAbort` agree bit-for-bit on returned values and updated machine states in both MIR and optimized LLVM IR across all `CoreBuildMode`s and optimization levels.
- **Theorem 2 (`immediateAbort_rebuiltCore_eliminates_all_panic_symbols_and_data`, `L1624`):** Proves that for any MIR body lowered with `.immediateAbort` and optimized against `.rebuiltImmediateAbort` at `optLevel = n + 1 >= 1`, `optMod.decls = []` (`0` undefined external panic/formatting/personality symbols), `optMod.rodataLocs = []`, `dataFootprintBytes optMod = 0`, every function carries `hasPersonality = false` and `nounwind = true`, `blocksImmediateTrapOnly f.blocks = true`, and ISA trap lowering emits exclusively `x86Ud2` (`x86_64`) or `aarch64Brk1` (`aarch64`).
- **Theorem 3 (`prebuiltCore_linkable_immediateAbort_rejected`, `L1819`; `prebuiltCore_cdylib_immediateAbort_compile_rejected`, `L1844`; `prebuiltCore_rlib_immediateAbort_admitted_but_retains_syms`, `L1883`):** Proves both halves of the prebuilt-sysroot architectural split: (a) linkable artifacts (`cdylib`, etc.) fail-closed reject prebuilt sysroot `core` with `errIncompatibleImmediateAbortCore` regardless of `#[panic_handler]` presence; (b) unlinked `rlib`s bypass `verifyDependencyFormat` (`compileAdmitted = .ok`) yet retain `countPanicSinkSites body.blocks` unresolved `core::panicking::*` declarations (`optMod.decls ≠ []`) and `24 * countPanicSinkSites body.blocks` `.data` bytes whenever `countPanicSinkSites > 0`.
- **Theorem 4 (`panicHandler_unit_return_rejected`, `L1948`; `checkPanicHandlerSig_sound_implies_never`, `L1956`; `panicHandler_omission_cdylib_sound_under_immediateAbort_rebuiltCore`, `L2012`; `missing_panicHandler_linkable_abort_or_unwind_rejected`, `L2046`; `missing_panicHandler_rlib_admitted`, `L2072`):** Mechanizes `E0308` rejection of `-> ()`, necessity of `-> !`, link-time soundness of omitting `#[panic_handler]` on `cdylib` under `immediateAbort + rebuiltImmediateAbort` at `optLevel >= 1`, and rejection of missing handlers on linkable `abort`/`unwind` outputs.
- **Boundary & Concrete Specimen Checks (`L2083–L2278`):** Proves dual-`cfg` activation (`dual_cfg_immediateAbort_activates_both`), failure of caller-site `tailCallLlvmTrap` inlining at `-O0` (`opt0_defeats_core_panicking_inline`), Anneal fail-closed gap semantics (`immediateAbort_failing_assert_still_traps_not_returns`), and kernel-evaluated witnesses (`divProbe_safe_exec_agrees`, `idxProbe_safe_exec_agrees`, `div_and_idx_footprint_contrast_exact`) matching the observed `48 B` vs. `0 B` `.data` contrast.

## Boundaries

Basis: `source`, `execution`, `derived`.

- **Explicit Anneal / TCB Implications (`unsupported`):**
  - **Anneal Fails Closed on `Assert` and `UnwindResume` Regardless of Panic Strategy:** As inspected in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirSemantics.lean:1568`), Anneal's MIR semantics maps `.unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported => .fault .unsupported`. Switching compilation flags to `-Cpanic=immediate-abort` does **not** magically eliminate `TerminatorKind::Assert` from MIR (`runtime-optimized` retains `assert(...) -> [success: bb1, unwind unreachable]`), nor does it make unsafe failing paths valid returns: on failing assertions, `-Cpanic=immediate-abort` transitions to a hardware trap (`ud2` / `brk #0x1`, `.trappedImmediate` in Theorem `immediateAbort_failing_assert_still_traps_not_returns`), not normal completion. Therefore, any future Anneal support for panicking MIR items still requires discharging `Assert` guard conditions and modeling `TerminatorKind::Assert` explicitly (while benefiting from `immediate-abort` eliminating panic formatting / unwinding paths if termination-via-trap is ever permitted, though for panic-freedom verification `Assert` predicates remain mandatory proof obligations).
- **Non-Exhaustive Coverage / Known Negative & Unchecked Regimes:**
  - **`known not to apply` — Prebuilt-Sysroot Inlining:** `-Cpanic=immediate-abort` does **not** eliminate external `core::panicking::*` calls or `CallerLoc` `.data` tables unless `core` itself was compiled with `cfg(panic = "immediate-abort")` (`-Zbuild-std=core`). Using prebuilt sysroot `core` silently bloats `.rlib` objects (`210 B` `.text`, `48 B` `.data`, `2` external symbols in our probe) and aborts `cdylib` compilation.
  - **`known not to apply` — `--profile=dev` (`-O0`) Call-Site Inlining:** At `-Copt-level=0`, LLVM ignores `#[inline]` (`InlineHint`) on `core::panicking::*`; caller functions still invoke monomorphized wrappers (`96 B` `.data` and debug `.text` bloat in our probe), even though `cdylib` links cleanly without `#[panic_handler]`.
  - **`known not to apply` — `panic!()` Calls Passing Non-Trivial Formatting Arguments at `-O0`:** While `#[track_caller]` / constant checks work cleanly, custom formatting arguments evaluated *before* calling `core::panicking::panic_fmt` can still emit argument-preparation instructions in unoptimized builds if side effects or drops occur before the call.
  - **`not examined` — Runtime Signal Capture & Hardware Execution Under QEMU/Hardware Traps:** We verified static ELF objects, LLVM IR, symbol tables, shared objects (`libpanic_probe.so`), and machine instructions (`ud2`, `brk #0x1`), rather than executing faulting binaries in a Linux signal harness to record `SIGILL`/`SIGTRAP` wait statuses or core dumps.
  - **`not examined` — `no_core` Crates, `panic_abort` / `panic_unwind` with `#[no_std]` Bins Calling `alloc`, and `std` Rebuilds (`-Zbuild-std=std`):** Our probes isolate minimal `#![no_std]` `core`-only crates (`lib`/`rlib`/`cdylib`); behavior with `alloc`, `extern "C-unwind"` foreign unwind boundaries (e.g., `UnwindTerminate`), or full `std` with `-Zbuild-std=std,panic_immediate_abort` legacy flags (`core/src/panicking.rs:35-41` explicitly turns `#[cfg(feature = "panic_immediate_abort")]` into `compile_error!`) beyond inspecting the `compile_error!` gate was not executed.
  - **`not examined` — Non-ELF Linker / LTO Interactions (`-Clto=fat`, COFF/Mach-O/WASM):** On `wasm32`, `abort_unwinding_calls.rs:47-49` and `core::intrinsics::abort` follow WASM-specific unreachable/trap rules (`exception-handling` feature checks); only ELF `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu` were probed locally.
  - **`unknown` — Multi-Crate Workspace Cross-Compilation Mixing `immediate-abort` with Third-Party Precompiled Rlibs:** By inspection of `dependency_format.rs:424-444`, any upstream crate in `DependencyList` lacking `required_panic_strategy == Some(ImmediateAbort)` fails with `IncompatibleWithImmediateAbort`; exact Cargo feature-unification edge cases across proc-macros built with host strategy vs. target crates built with `-Cpanic=immediate-abort` were not empirically probed (and would be a good follow-up if proc-macros are used in target workspaces).

## Evidence

Basis: `source`, `execution`, `derived`.

### 1. Upstream Primary-Source Anchors Resolved Live

| Repository & Commit SHA | File Path & Line Range | Key Symbol(s) & Audited Fact |
| --- | --- | --- |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_target/src/spec/mod.rs:818-849` | Defines `PanicStrategy::{Unwind, Abort, ImmediateAbort}` (`"immediate-abort"`), `desc_symbol() -> sym::immediate_abort`, `unwinds() -> matches!(self, PanicStrategy::Unwind)`. |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_session/src/options.rs:917,1317-1326` | `parse_opt_panic_strategy` parses `"immediate-abort"` to `PanicStrategy::ImmediateAbort`. |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_session/src/config.rs:2770-2774` | `early_fatal` requires `-Zunstable-options` and a nightly compiler whenever `cg.panic == Some(PanicStrategy::ImmediateAbort)`. |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_session/src/config/cfg.rs:214-221` | Injects both `cfg(panic = "immediate-abort")` and `cfg(panic = "abort")` when `sess.panic_strategy() == PanicStrategy::ImmediateAbort`. |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_middle/src/middle/lang_items.rs:128-137` | `required(tcx, lang_item)`: `Unwind => true`, `Abort => lang_item != LangItem::EhPersonality`, `ImmediateAbort => false`. |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_resolve/src/late/weak_lang_items.rs:14-61` | `verify`: skips `CrateType::Rlib`; emits `MissingPanicHandler` or `PanicUnwindWithoutStd` only if `missing.contains(&item) && required(tcx, item) && items.get(item).is_none()`. |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_hir_typeck/src/check.rs:165-235` | `check_panic_info_fn`: rejects type/const generics and checks signature against `for<'a, 'b> fn(&'a PanicInfo<'b>) -> !` (`tcx.types.never`) via `ObligationCauseCode::LangFunctionType(sym::panic_impl)`. |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:25-147`, `compiler/rustc_middle/src/ty/layout.rs:1360-1390` | `AbortUnwindingCalls`: queries `!fn_can_unwind` (false when `!panic_strategy().unwinds()`); rewrites `Assert` unwind actions to `UnwindAction::Unreachable` and `UnwindResume` to `UnwindTerminate`. |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_metadata/src/dependency_format.rs:84-126,409-444`, `compiler/rustc_metadata/src/diagnostics.rs:89-99` | `calculate_type` sets `Linkage::NotLinked` for `CrateType::Rlib` so `verify_ok` returns early; for linked artifacts, checks every crate has `Some(ImmediateAbort)` or emits fatal `IncompatibleWithImmediateAbortCore` if `core` mismatches. |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `compiler/rustc_codegen_ssa/src/mir/block.rs:753-889` | `codegen_assert_terminator` and `codegen_terminate_terminator` unconditionally build `Location` and call `common::build_langcall(..., lang_item)` even under `ImmediateAbort`. |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `library/core/src/panicking.rs:35-41,54-105,265-355` | `compile_error!` on legacy Cargo feature `panic_immediate_abort`; marks `panic_fmt`, `panic_nounwind_fmt`, `panic_bounds_check`, etc. `#[cfg_attr(panic = "immediate-abort", inline)]` calling `super::intrinsics::abort_immediate()` (`abort()` in `1.98.0-nightly`). |
| `rust-lang/rust` (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`) | `library/core/src/intrinsics/mod.rs:636-638`, `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:145,177-178`, `compiler/rustc_codegen_llvm/src/intrinsic.rs:1081-1083` | `pub const fn abort_immediate() -> !;` lowered via `bx.abort_immediate()` -> `self.call_intrinsic("llvm.trap", &[], &[])`. |
| `llvm/llvm-project` (`354891a804ac4eefa45a9a546cceed4404b18b78`) | `llvm/include/llvm/IR/Intrinsics.td:2093-2096` | `def int_trap : Intrinsic<[], [], [IntrNoReturn, IntrCold, IntrInaccessibleMemOnly, IntrWriteMem]>`. |
| `llvm/llvm-project` (`354891a804ac4eefa45a9a546cceed4404b18b78`) | `llvm/lib/Target/X86/X86InstrSystem.td:25`, `llvm/lib/Target/AArch64/AArch64InstrInfo.td:11217` | X86 `def TRAP` lowers `trap` to `"ud2"` (`0x0F 0x0B`); AArch64 `Pat<(trap), (BRK 1)>` lowers `trap` to `brk #0x1`. |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `trusted/lean/Trusted/MirSemantics.lean:1568-1569` | Fail-closed `.unwindResume \| .assert _ _ _ _ _ \| .call _ _ _ _ _ \| .unsupported => .fault .unsupported`. |

### 2. Support Artifacts in Package Directory

1. **`support/probe_no_std_panic_strategies.py`:** Self-contained reproducible harness running inside `with tempfile.TemporaryDirectory():` using the local `rustc`/`cargo`/`llvm-nm`/`llvm-size`/`llvm-objdump` toolchain to execute all 12 Experiment A probes (prebuilt sysroot, `-Zdump-mir=all`, dual `cfg(panic = ...)`, `-Zbuild-std=core` across `unwind`/`abort`/`immediate-abort`, `--release` vs. `--profile=dev`, `lib` vs. `cdylib`, `x86_64-unknown-linux-gnu` vs. `aarch64-unknown-linux-gnu`) and all 5 Experiment B `#[panic_handler]` ABI / omission probes.
2. **`support/probe_results.json` (`129,545` bytes):** Raw sanitized empirical artifact containing compiler stdout/stderr, return codes, extracted `runtime-post-cleanup` and `runtime-optimized` MIR dumps, extracted LLVM IR functions and resolved `FunctionAttrs`, `llvm-nm -u` symbol lists, `llvm-size` section byte metrics (both `.o` and `.so`), and full `llvm-objdump -d` disassemblies.
3. **`support/NoStdPanicImmediateAbortTrapAndFootprintSoundness.lean` (`2,278` lines, `97,063` bytes):** Standalone Lean `v4.34.1` formalization encoding `67` `noncomputable def` functions/predicates and `40` explicit `theorem`s verified strictly under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with exit code `0`, zero warnings, and zero output; Lean MetaM environment audit across all `1,204` generated namespace constants confirms `unsafe_rec=0`, `bad_safety=0`, and `disallowed_axioms=0` (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`, and `0` `omega`/`bv_decide`/`native_decide`/`partial def`).

### 3. Selected Verbatim Disassemblies and Error Diagnostics from `support/probe_results.json`

- **Sysroot `cdylib` Rejection With `#[panic_handler]` Still Triggered (`sysroot_cdylib_immediate_abort_with_panic_handler_also_rejected`):**
  `compile_returncode = 1`; `compile_stderr`:
  `error: the crate core was compiled with a panic strategy which is incompatible with immediate-abort`
- **`-Zbuild-std=core` `--release` (`-O3`) `cdylib` With Omitted `#[panic_handler]` (`build_std_core_cdylib_immediate_abort_no_panic_handler_ok`):**
  `compile_returncode = 0`; `llvm_decls = ["declare void @llvm.trap() #2"]`; `.o` `section_sizes = {text_bytes: 88, data_bytes: 0, bss_bytes: 0}`; `.so` `llvm-size`: `text=904, data=440, bss=2113, dec=3457`; `.so` `llvm-nm -u`: strictly CRT weak symbols (`w _ITM_deregisterTMCloneTable`, `w _ITM_registerTMCloneTable`, `w __cxa_finalize`, `w __gmon_start__`).
- **`-Zbuild-std=core` `--release` `x86_64` `lib` Disassembly (`build_std_core_lib_panic_abort` vs. `build_std_core_lib_panic_immediate_abort`):**
  Under `-Cpanic=abort` (`text=129 B, data=48 B`):
  `div` ends with `b: 50 pushq %rax; c: 48 8d 3d 00 00 00 00 leaq (%rip), %rdi; 13: ff 15 00 00 00 00 callq *(%rip)`.
  Under `-Cpanic=immediate-abort` (`text=88 B, data=0 B`):
  `div` ends directly at `b: 0f 0b ud2` (`13` bytes total vs. `25` bytes), and `idx` ends directly at `9: 0f 0b ud2` (`11` bytes total vs. `29` bytes).

## Revalidation

Basis: `source`, `execution`, `derived`.

Re-run both empirical and mechanized checks from inside this report package directory without modifying any git worktree:

1. **Re-execute all `rustc` / `-Zbuild-std=core` / `llvm-*` empirical probes:**
   ```bash
   python3 support/probe_no_std_panic_strategies.py
   ```
   Confirm exit code `0`, regeneration of `support/probe_results.json`, `compile_returncode == 0` for all `build_std_core_*` probes and `sysroot_lib_*` probes, `compile_returncode == 1` for `sysroot_cdylib_immediate_abort_*` (`IncompatibleWithImmediateAbortCore`), `sysroot_immediate_abort_requires_unstable_options`, and `invalid_panic_handler_unit_return_rejected_e0308` (`E0308`), `data_bytes == 0` and `undefined_symbols_llvm_nm == []` for `build_std_core_lib_panic_immediate_abort` (`x86_64` and `aarch64`), and `ret i32 3` for `cfg_flags_mask`. (Note: requires `rust-src` component and `llvm-tools` preview component installed on the active nightly toolchain.)

2. **Re-verify the standalone Lean `v4.34.1` mechanization:**
   ```bash
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/NoStdPanicImmediateAbortTrapAndFootprintSoundness.lean
   ```
   (On cgroup-managed hosts, run inside `~/.local/bin/anneal-lean-run --mode file -- ...`.) Confirm exit code `0`, zero warnings/errors, zero banned tokens (`sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial def`, `noncomputable section`, `deriving`, `._unsafe_rec`), and zero disallowed axioms in Lean MetaM.

3. **Re-check upstream HEAD drift (`rust-lang/rust`, `llvm/llvm-project`, `joshlf/anneal`):**
   - Resolve current HEAD SHAs via GitHub API (`repos/rust-lang/rust/commits/HEAD`, `repos/llvm/llvm-project/commits/HEAD`, `repos/joshlf/anneal/commits/HEAD`) and verify whether `-Cpanic=immediate-abort` has stabilized (`config.rs:2770-2774`), whether `core::panicking` changes `#[inline]` to `#[inline(always)]` (which would eliminate the `-O0` call-site retention boundary), and whether Anneal (`MirSemantics.lean:1568`) adds `TerminatorKind::Assert` handling.

4. **Validate corpus schema and catalog integrity from the corpus root:**
   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```
   Confirm `reference check passed` with exit code `0`.
