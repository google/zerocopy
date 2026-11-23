# Compiling and Capturing the Rust Standard Library (`core`, `alloc`, `std`) for MIR Verification: Compiler Seams, `unsafe` Census, and Ecosystem Comparison

## Summary

Compiling `library/core`, `library/alloc`, and `library/std` directly through an in-process `rustc_driver` tool and hooking `Runtime(PostCleanup)` MIR (`mir_drops_elaborated_and_const_checked`) is **mechanically viable at the compiler-session level**—host `librustc_driver` linkage does not conflict with `#![no_core]` target compilation—but **differs from ordinary third-party crate capture across seven soundness- and admission-critical compiler seams**:

1. **In-Process `TyCtxt` Isolation vs. Strict Toolchain Lockstep:** Because `#![no_core]` suppresses `rustc`'s implicit `extern crate std` / `extern crate core` injection, compiling `library/core/src/lib.rs` (`163,724` non-test LOC) inside a `rustc_driver` process linked against host `libstd-*.so` loads zero external crates into `tcx.crates(())` and completes analysis cleanly (`50,789,114`-byte `libcore.rmeta` at `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, even without `-Zforce-unstable-if-unmarked` because `core` carries `#![stable(feature = "core", since = "1.6.0")]`). However, `core` is lockstep-coupled to compiler-internal built-in macros, language items, and intrinsic signatures: compiling `rust-lang/rust@8006091eb71ae7d9e9bccb66c6122c9d68af4466` `library/core` under `rustc@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` fails immediately (`191,717` diagnostic lines starting with missing built-in macros `offload_kernel`, `test_binder_constraints`, `direct_const_arg`, and `Reborrow`).
2. **Crate-Graph, Out-of-Tree Source, and File-Loader Gates:** Unlike self-contained third-party crates:
   - `library/core/src/lib.rs` mounts sibling repository trees via `#[path = "../../stdarch/crates/core_arch/src/mod.rs"]`, `#[path = "../../portable-simd/crates/core_simd/src/mod.rs"]`, and `include_str!("../../std/...")` documentation includes; source-staging shortcuts restricted to a single crate root directory reject `..` traversal or miss sibling directories.
   - `library/alloc` compiles cleanly in raw `rustc_driver` mode against precompiled sysroot `core` + `compiler_builtins`, whereas `library/std` requires explicit `--extern` bindings (`alloc`, `hashbrown`, `cfg_if`, `libc`, `panic_unwind`/`panic_abort`, `rustc_demangle`, `std_detect`, `unwind`), `-Zforce-unstable-if-unmarked` for unstaged dependencies, and `--env STD_ENV_ARCH=...`.
   - When `rustc` formats any warning, lint, or error span pointing into a precompiled sysroot macro (such as `/rustc/<commit>/library/core/src/panic.rs`), `SourceMap` invokes `FileLoader::read_file` on that virtual remapped path; a closed allowlist `FileLoader` that records denied reads as `unsupported` refusals before checking compiler diagnostics masks the underlying diagnostic.
   - Because `anneal-rustc-capture` (`google/zerocopy@e5a9824d87f7daa5282969a25a8bbca9af985400`) passes `--emit=metadata,obj` and continues through LLVM codegen after `after_analysis`, any non-generic item in the crate that violates backend codegen invariants (for example, calling nullary `intrinsics::align_of::<T>()` outside a `const { ... }` block) triggers a codegen ICE even when excluded from `--select`.
3. **Language-Item (`#[lang = "..."]`) and Intrinsic (`#[rustc_intrinsic]`) Admission:**
   - `core`, `alloc`, and `std` define **`182`**, **`3`**, and **`6`** `#[lang = "..."]` items respectively. A crate-wide gate that refuses all local `LangItem` definitions (`trusted/rustc-capture/src/capture.rs:922-931`, except `PanicImpl` in `Bin` selected-unit mode) aborts even a minimal 7-line `#![no_core]` crate (`"crate-local language item Sized is unsupported"`). Additionally, local ADTs in `core` (`Option`, `Result`, `NonZero`, `Ordering`) have `adt.did().is_local() == true` when compiling `core` itself versus `false` when compiling downstream crates.
   - `core` declares **`311` `#[rustc_intrinsic]`** items (`alloc` declares `1`, `const_deallocate`; `std` declares `0`). Verifying an intrinsic's Rust fallback body does *not* verify what callers execute because `LowerIntrinsics` and codegen intercept calls by `InstanceKind::Intrinsic`. Across 24 representative `core::intrinsics::*` calls tested at `Runtime(PostCleanup)`, **8 already lower before `PostCleanup` into standard scalar MIR** (`wrapping_add`, `add_with_overflow`, `three_way_compare`, `unreachable`, `forget`, `const { size_of::<T>() }`, `const { align_of::<T>() }`, and diverging `abort`), while **16 require explicit MIR operator, statement, operand, cast, or intrinsic-call semantics** (`AddUnchecked`, `ShlUnchecked`, `Assume`, `UbChecks`, `CastKind::Transmute`, `CopyNonOverlapping`, pointer types, or `TerminatorKind::Call` to pure bit/math intrinsics such as `ctlz`, `ctpop`, `bswap`, `rotate_left`, `saturating_add`, `exact_div`, `disjoint_bitor`, `is_val_statically_known`, and `select_unpredictable`).
4. **Three Distinct Runtime-Check Mechanisms in `Runtime(PostCleanup)` MIR (`ub_checks`, `#[rustc_inherit_overflow_checks]`, and `core::contracts`):**
   - **`assert_unsafe_precondition!` + `#![rustc_preserve_ub_checks]` (`66` sites in `core`, `3` in `alloc`):** `LowerIntrinsics` lowers `intrinsics::ub_checks()` to `Operand::RuntimeChecks(RuntimeChecks::UbChecks)` (`_3 = UbChecks; switchInt(move _3)`). Because `core`, `alloc`, and `std` all carry `#![rustc_preserve_ub_checks]` (`core/src/lib.rs:77`, `alloc/src/lib.rs:200`, `std/src/lib.rs:227`), `InstSimplify` (`instsimplify.rs:33-36`) **refuses to fold `UbChecks` even at `-Copt-level=3 -Zub-checks=no` in `Runtime(Optimized)` MIR**. Modeling `UbChecks` as `true` would create **false safety** (aborting in `precondition_check` before reaching `unsafe` operations that execute unguarded in release builds); modeling `UbChecks` as `false` (for release soundness) or demonic `{false, true}` (simultaneously proving release safety and absence of spurious debug panics under `# Safety` preconditions) is required.
   - **`#[rustc_inherit_overflow_checks]` (`55` sites in `core`):** Even when `-Coverflow-checks=no` is passed, `Builder::new` (`rustc_mir_build/src/builder/mod.rs:758-760`) forces `check_overflow = true`, emitting `(T, bool)` `AddWithOverflow` locals and `TerminatorKind::Assert { msg: AssertKind::Overflow(..), .. }` in both `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR. During backend codegen (`rustc_codegen_ssa/src/mir/block.rs:714-716`), when `!sess.overflow_checks() && msg.is_optional_overflow_check()`, codegen **deletes the panic branch and falls through with the wrapped result**. Treating `AssertKind::Overflow` / `OverflowNeg` inside `core` as an unconditional panic is therefore **unsound for release callers**; it must be modeled with demonic nondeterminism between panic and wrapped continuation (or parameterized by caller `overflow_checks`).
   - **`#![feature(contracts)]` (`core::contracts`, `rust-lang/rust#128044`):** Under default `-Zcontract-checks=no`, AST lowering (`rustc_ast_lowering/src/contract.rs:36-110`) emits `_3 = const false; switchInt(move _3)` in `Runtime(PostCleanup)` MIR while leaving dead blocks containing `'static` closure types (`move |ret: &Ret| ...`), `Option<{closure}>` locals, and `contract_check_requires` / `contract_check_ensures` calls; even in `Runtime(Optimized)` at `-O3`, `#[ensures]` leaves a live `Option::<{closure}>::None` assignment and static allocation.
5. **Stratified Standard-Library Verification Surface (`1,532` `unsafe fn`, `4,547` `unsafe` blocks) and `verify-rust-std` Pitfalls:**
   - Across `946` non-test source files (`362,502` LOC) in `core` (`668` `unsafe fn`, `1,378` `unsafe {}`), `alloc` (`268` `unsafe fn`, `1,017` `unsafe {}`), and `std` (`596` `unsafe fn`, `2,152` `unsafe {}`), verification obligations partition cleanly into **Tier 0** (scalar/slice/layout/UTF-8/endian slices in `core::{num,ascii,char,cmp,str,slice,ptr,mem,array}`), **Tier 1** (polymorphic `<T>`, core intrinsics, `UbChecks`, and optional overflow assertions), and **Tier 2** (`UnsafeCell` interior mutability, `Allocator`/`RawVec`/`Rc`/`Arc` + unwind/drop glue, `core::sync::atomic` weak memory, `std::sys` OS syscalls, and `stdarch` SIMD/`asm!`).
   - Primary-source audit of `model-checking/verify-rust-std` (`1feeadd937956b8067ec2fb147ef55469361dab4`) documents six concrete specification and tool hazards: over-strong zero-length `NonNull::copy_to` postconditions (`non_null.rs:1150-1151`), vacuous `*const ()` casts in `NonNull::{as_ref,as_mut,drop_in_place}` (`model-checking/verify-rust-std#783`), inconsistent Flux bitvector axioms (`flux_info.rs:17-27`, `model-checking/verify-rust-std#782`), disabled uninitialized/validity checks in default bounded model-checking workflows (`model-checking/verify-rust-std#775`, `model-checking/verify-rust-std#777`), finite monomorphization missing `> 1 KiB` `RawVec` branches (`model-checking/verify-rust-std#734`), and no-op runtime predicate stubs (`ub_checks.rs:192-243`) paired with `if const { true }` CTFE branches (`ub_checks.rs:138, 168`).

## Applicability

This report relates five pinned upstream artifacts listed in `REPORT.json`:

- **Compiler and Standard Library Under Primary Observation:** `rust-lang/rust` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`rustc 1.98.0-nightly`, `2026-05-30`, `x86_64-unknown-linux-gnu`, LLVM `22.1.6`), covering both its `compiler/` passes (`rustc_mir_build`, `rustc_mir_transform`, `rustc_ast_lowering`, `rustc_const_eval`, `rustc_codegen_ssa`) and its `library/{core,alloc,std}` source tree.
- **Newer Upstream Standard-Library Snapshot (Version-Drift Check):** `rust-lang/rust` at `8006091eb71ae7d9e9bccb66c6122c9d68af4466`, used specifically to test cross-revision compilation of `library/core` against `rustc@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`.
- **MIR Capture and Verification Pipeline:** `google/zerocopy` at `e5a9824d87f7daa5282969a25a8bbca9af985400` (`anneal/` workspace: `trusted/rustc-capture` Schema v4 with `--select`, `--instantiate`, and `--scope=crate`; `trusted/cargo-anneal` Receipt Schema v3; `trusted/lean/Trusted/MirAst.lean` and `MirSemantics.lean`), pinned to `rustc@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` and Lean 4 `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) on `x86_64-unknown-linux-gnu`.
- **Standard-Library Verification Benchmark & Ecosystem Fork:** `model-checking/verify-rust-std` at `1feeadd937956b8067ec2fb147ef55469361dab4` (tracking `nightly-2026-11-19`), including its `library/contracts/safety` macro crate, `library/core/src/{ub_checks.rs,flux_info.rs,ptr/non_null.rs}`, `verifast-proofs/`, `kmir-proofs/`, `testable-simd-models/`, and public challenge/tool records.

### Shared vs. Version-Specific Behavior

- **Shared across `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `rust-lang/rust@8006091eb71ae7d9e9bccb66c6122c9d68af4466`, and `model-checking/verify-rust-std@1feeadd937956b8067ec2fb147ef55469361dab4`:**
  - `#![no_core]` on `library/core/src/lib.rs`, `#![rustc_preserve_ub_checks]` on `core`, `alloc`, and `std`, `LowerIntrinsics` lowering of `ub_checks`/`contract_checks`/`overflow_checks` to `Operand::RuntimeChecks`, `Builder::new`'s `RustcInheritOverflowChecks` override with `is_optional_overflow_check()` codegen erasure, and `core`'s out-of-directory `#[path = "../../stdarch/..."]` / `#[path = "../../portable-simd/..."]` module mounts hold across all examined revisions.
- **Revision-specific:**
  - Exact LOC, `unsafe` item counts, `#[lang]` counts (`182` in `core` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), and internal built-in macros (`offload_kernel`, `Reborrow`, etc. added by `8006091eb71ae7d9e9bccb66c6122c9d68af4466`) vary with each nightly revision.
  - Exact capture admission and rejection diagnostics reflect `anneal-rustc-capture` at `google/zerocopy@e5a9824d87f7daa5282969a25a8bbca9af985400` (`x86_64-unknown-linux-gnu` scalar/enum/monomorphized profile).

## Findings

### 1. Mechanical Differences Between Third-Party Crates and `library/{core,alloc,std}`

Basis: source + execution

#### 1.1 Sysroot Bootstrapping, `#![no_core]`, and Toolchain Lockstep

A natural concern when running an in-process `rustc_driver` binary (`anneal-rustc-capture`) to compile `library/core` is symbol or crate-metadata collision: the capture binary itself links dynamically against host `librustc_driver-*.so` and `libstd-*.so` (`readelf -d` shows `NEEDED librustc_driver-5d5a3c5207375ffc.so`), while compiling a crate also named `core`.

Direct execution and compiler-source inspection establish that **host dynamic linking and target `TyCtxt` crate resolution are completely orthogonal**, subject to strict version lockstep:

- **Zero `TyCtxt` collision for `#![no_core]` (`core`):** Host `libstd-*.so` lives solely in the driver's host ELF address space. Inside `TyCtxt`, `#![no_core]` (`library/core/src/lib.rs:75`) suppresses `rustc`'s automatic prelude injection of `extern crate std` and `extern crate core`, leaving `tcx.crates(())` empty (`0` external crates loaded from `--sysroot`). Running `anneal-rustc-capture -- <sysroot-src>/library/core/src/lib.rs --crate-name=core --crate-type=rlib --edition=2024 --sysroot=<sysroot> --emit=metadata -Copt-level=0 -Cdebug-assertions=no -Coverflow-checks=no -Zmir-preserve-ub` exits **`0`** and emits a `50,789,114`-byte `libcore.rmeta` plus `note: anneal-rustc-capture: compiler analysis callback reached`.
- **When `-Zforce-unstable-if-unmarked` and `RUSTC_BOOTSTRAP=1` are required:**
  - On a `-nightly` compiler (`1.98.0-nightly`), `#![feature(...)]` attributes are accepted without `RUSTC_BOOTSTRAP=1`; `RUSTC_BOOTSTRAP=1` (or `-Zallow-features=...`) is required only when building `core`/`alloc`/`std` with a stable or beta `rustc` binary.
  - `library/core/src/lib.rs:46` and `library/alloc/src/lib.rs` carry crate-level `#![stable(...)]` staged-API markers, so both `core` and `alloc` pass `rustc` analysis in raw driver mode *without* `-Zforce-unstable-if-unmarked`. By contrast, Cargo `build-std` and `x.py` pass `-Zforce-unstable-if-unmarked` when compiling unstaged sysroot support crates (`compiler_builtins`, `libc`, `cfg_if`, `hashbrown`, `rustc_demangle`, `unwind`) so that `std` can link them under `#![feature(staged_api)]`.
- **Mandatory compiler–library commit lockstep:** Running the `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` capture driver against `rust-lang/rust@8006091eb71ae7d9e9bccb66c6122c9d68af4466` `library/core/src/lib.rs` fails with exit code `1` and `191,717` stderr lines because `library/core` references compiler built-in macros (`offload_kernel`, `test_binder_constraints`, `direct_const_arg`, `Reborrow`) and lang items added after `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`. Auditing unmodified upstream `core`/`alloc`/`std` therefore requires capturing the exact `rust-src` tree paired with the active `rustc` commit.

#### 1.2 Crate-Graph, Source-Namespace, and `anneal-rustc-capture` Admission Gates

Running `anneal-rustc-capture` (`google/zerocopy@e5a9824d87f7daa5282969a25a8bbca9af985400`) and inspecting `trusted/rustc-capture/src/{main,capture,extract,identity}.rs` and `trusted/cargo-anneal/src/verify.rs` identifies six mechanical gates separating `core`/`alloc`/`std` from ordinary single-crate captures:

| Gate | Location in `google/zerocopy@e5a9824d87` | Observed Effect on `library/{core,alloc,std}` |
| --- | --- | --- |
| **G1. Out-of-root `#[path]` & `include_str!` mounts** | `capture.rs:124-162` (`RecordingLoader`), `verify.rs:1016-1028, 1119-1124` | `core/src/lib.rs:376` (`mod core_arch;`) and `portable_simd` resolve `../../stdarch/crates/core_arch/src/mod.rs`, `../../portable-simd/...`, and `../../std/...` markdown docs. Passing only `library/core/src/**/*.rs` fails with `undeclared compiler read: .../stdarch/crates/core_arch/src/mod.rs: undeclared source directory`, and `cargo-anneal --manifest-path` rejects `[features]`/`[dependencies]`/`build.rs` and `..` path components. |
| **G2. Crate-local `#[lang = "..."]` refusal** | `capture.rs:922-931` | After declaring all `library/{core,portable-simd,stdarch,std}` `.rs`/`.md` files, `library/core` compiles through `after_analysis` with zero `rustc` errors and fails at `capture.rs:928` with `{"status":"unsupported","diagnostics":["crate-local language item Sized is unsupported"]}` (identical failure on a 7-line `#![no_core]` reproducer). |
| **G3. Forbidden `--extern` / `-L` and `dylib` crate types** | `capture.rs:417-421, 463-484, 552-564, 638-677` | `std/Cargo.toml:13` declares `crate-type = ["dylib", "rlib"]` and requires `--extern` for `alloc`, `hashbrown`, `cfg_if`, `libc` (sysroot contains multiple `liblibc-*.rmeta` hashes -> `E0464` without `--extern`), plus `--env STD_ENV_ARCH=x86_64` (`std/src/env.rs:1051`). |
| **G4. Virtual `/rustc/<sha>/...` diagnostic snippet reads** | `capture.rs:147-162, 1370-1376` | When `rustc` emits any diagnostic or lint note referencing a span inside precompiled sysroot `libcore` (`/rustc/f8a08b688.../library/core/src/panic.rs`), `SourceMap` calls `RecordingLoader::read_file`, pushing an `undeclared compiler read` refusal that overrides `compiler_failed`. |
| **G5. Whole-crate `--emit=metadata,obj` codegen continuation** | `capture.rs:408-414, 1309` | Because capture continues through LLVM codegen to force `required_consts` evaluation, any uncalled/unselected item in the crate that fails backend codegen aborts `--select` captures for unrelated pure functions. |
| **G6. Local vs. external ADT & codegen-attribute classification** | `extract.rs:145-199, 784-950` | `extract.rs:159` admits only fieldless local enums (`adt.did().is_local() && args.is_empty()`), rejecting generic or payload enums (`Option<T>`, `Result<T, E>`) and structs (`NonZero<T>`). `codegen_attrs` (`extract.rs:800-949`) refuses `#[rustc_force_inline]`, `#[rustc_nounwind]` (`NEVER_UNWIND`, used on `assert_unsafe_precondition!`'s `precondition_check`), `#[rustc_std_internal_symbol]`, `#[target_feature]`, and `#[no_builtins]`. |

#### 1.3 Compiler-Internal Stdlib Attributes at `Runtime(PostCleanup)`

Basis: source + execution

Inspecting `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` establishes which internal attributes affect MIR semantics versus pure frontend gating:

- **Purely frontend/coherence/stability attributes (zero post-typecheck MIR divergence):**
  - `#[rustc_const_stable]` / `#[rustc_const_unstable]` / `#[rustc_const_stable_indirect]` (`compiler/rustc_hir/src/stability.rs:45-90`, `rustc_passes/src/stability.rs`): gate downstream stable `const` callers only; runtime MIR is unchanged.
  - `#[rustc_allow_incoherent_impl]` + `#[rustc_has_incoherent_inherent_impls]` (`compiler/rustc_hir_analysis/src/coherence/`): permit split inherent `impl` blocks across `core` and `alloc`/`std` (for example on primitive types and slices); resolved statically to ordinary `DefId`s before MIR construction.
  - `#![rustc_coherence_is_core]` (`library/core/src/lib.rs:76`): coherence orphan-rule marker only.
- **Attributes that materially alter MIR or CTFE vs. runtime equivalence:**
  - `#[rustc_do_not_const_check]` (`compiler/rustc_const_eval/src/const_eval/machine.rs:225-269`, `rustc_hir_typeck/src/callee.rs:1034`): skips `check_consts` on the body and requires CTFE (`hook_special_const_fn`) to intercept calls (such as `PanicDisplay`, `BeginPanic`, and `PanicFmt -> ConstPanicFmt`). Runtime MIR executes the unhooked body, whereas CTFE executes the interpreter hook.
  - `#[rustc_force_inline]` (`InlineAttr::Force`) and `#[rustc_nounwind]` (`CodegenFnAttrFlags::NEVER_UNWIND`): alter inlining guarantees and unwind-edge codegen (`abort_unwinding_calls::AbortUnwindingCalls` runs before `Runtime(Initial)` at `rustc_mir_transform/src/lib.rs:637`).
  - `#![rustc_preserve_ub_checks]` and `#[rustc_inherit_overflow_checks]`: alter MIR pass folding and backend assertion emission, analyzed in §2 below.

### 2. `ub_checks`, `#[rustc_inherit_overflow_checks]`, `core::contracts`, and `#[rustc_intrinsic]` Lowering

Basis: source + execution + derived

#### 2.1 `assert_unsafe_precondition!` and `#![rustc_preserve_ub_checks]`

In `library/core/src/ub_checks.rs:53-108` (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `assert_unsafe_precondition!(check_library_ub | check_language_ub, msg, (...) => pred)` defines a nested `#[rustc_no_mir_inline] #[inline] #[rustc_nounwind] #[track_caller] const fn precondition_check(...)` and guards its call behind `intrinsics::ub_checks()` (for `check_language_ub`, conjoined with a `const_eval_select!` returning `false` in `const` and `!cfg!(miri)` at runtime).

During `run_runtime_cleanup_passes` (`compiler/rustc_mir_transform/src/lib.rs:650-663`), `LowerIntrinsics` (`lower_intrinsics.rs:26-42`) rewrites `intrinsics::ub_checks()` into:

```text
_3 = UbChecks;
switchInt(move _3) -> [0: bb_unchecked, otherwise: bb_precond_check];
```

Empirical MIR dumps (`rustc -Copt-level=3 -Cdebug-assertions=no -Coverflow-checks=no -Zub-checks=no -Zdump-mir="runtime-post-cleanup | runtime-optimized"`) confirm two critical behaviors:

1. **At `Runtime(PostCleanup)`:** `_3 = UbChecks;` (`mir::Operand::RuntimeChecks(RuntimeChecks::UbChecks)`) is **always present**, regardless of `-Zub-checks=no` or `#![rustc_preserve_ub_checks]`. `anneal-rustc-capture` currently rejects it at `extract.rs:397` (`"unsupported operand: UbChecks"`).
2. **At `Runtime(Optimized)`:** Without `#![rustc_preserve_ub_checks]`, `InstSimplify` (`SimplifyUbCheck`, `instsimplify.rs:33-36, 461-471`) replaces `UbChecks` with `const false` and dead-code-eliminates `bb_precond_check`. **With `#![rustc_preserve_ub_checks]`**—which is active at the crate root of `core` (`lib.rs:77`), `alloc` (`lib.rs:200`), and `std` (`lib.rs:227`) so prebuilt `.rmeta` generics preserve UB checks for downstream debug callers—**`switchInt(UbChecks)` survives intact even in `Runtime(Optimized)` at `-Copt-level=3 -Zub-checks=no`**.

**Soundness consequence (derived from source + execution):**
- Evaluating `UbChecks` to `true` during verification is **unsound for release builds**: invalid inputs trigger `precondition_check`'s `panic_nounwind_fmt` (aborting cleanly) instead of reaching the `unsafe` operation that executes unguarded when `sess.ub_checks() == false`.
- Evaluating `UbChecks` to `false` verifies exact release-mode (`-Zub-checks=no`) behavior without false safety, and makes `bb_precond_check` dynamically unreachable (so an unmodeled `precondition_check` call lowered to `TerminatorKind.unsupported` never faults).
- Evaluating `UbChecks` via **demonic nondeterministic choice (`Choice {false, true}`)** in `MirSemantics` is strictly stronger: under the function's `# Safety` precondition, the `false` branch proves the unguarded release path is UB-free and meets its postcondition, while the `true` branch proves `precondition_check` never panics on any input satisfying `# Safety` (catching precondition drift between documentation/specs and `assert_unsafe_precondition!`).

#### 2.2 `#[rustc_inherit_overflow_checks]` Soundness Trap

`core` contains **`55` `#[rustc_inherit_overflow_checks]` annotations** (`33` in `core::iter`, `11` in `core::ops`, `8` in `core::num`, plus `3` in other modules). Unlike `ub_checks()`, this attribute does **not** emit `Operand::RuntimeChecks(OverflowChecks)`. Instead:

- In `Builder::new` (`compiler/rustc_mir_build/src/builder/mod.rs:758-760`), `check_overflow` is initialized to `find_attr!(tcx.hir_attrs(hir_id), RustcInheritOverflowChecks) || tcx.sess.overflow_checks()`.
- Consequently, **even under `-Coverflow-checks=no`**, both `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR contain:
  ```text
  _5 = AddWithOverflow(copy _3, copy _4);
  assert(!move (_5.1: bool), "attempt to compute `{} + {}`, which would overflow", ...) -> [success: bb1, unwind continue];
  bb1: { _0 = move (_5.0: u32); return; }
  ```
- During codegen (`compiler/rustc_codegen_ssa/src/mir/block.rs:710-721`, mirrored in `rustc_codegen_cranelift/src/base.rs:368`), `AssertKind::is_optional_overflow_check()` (`terminator.rs:164-168`: `OverflowNeg` and `Overflow(Add | Sub | Mul | Shl | Shr)`) causes the backend to check `if !bx.sess().overflow_checks() && msg.is_optional_overflow_check() { const_cond = Some(expected); }`, **erasing the panic branch and continuing to `bb1` with wrapped `_5.0`** whenever compiled or inlined into a `-Coverflow-checks=no` crate.

**Soundness consequence (derived from source + execution):** Modeling `TerminatorKind::Assert` with `msg.is_optional_overflow_check() == true` as a guaranteed panic in `core` is **unsound** for release callers that rely on `-Coverflow-checks=no` (where execution continues into `bb1` with wrapped arithmetic). A sound `core` MIR model must treat `is_optional_overflow_check()` assertions either as parameterized by caller `overflow_checks : Bool` or as demonic `Choice` between unwinding/aborting and continuing to `target` with wrapped `(_5.0)`.

#### 2.3 `core::contracts` (`#![feature(contracts)]`, `rust-lang/rust#128044`) Interaction

Live MIR dumps of `#[core::contracts::requires(x < 100)]` and `#[core::contracts::ensures(move |ret: &u32| *ret == x + 1)]` under `-Zcontract-checks=no` vs. `-Zcontract-checks=yes` show:

1. **`'static` closure capture restriction (`E0597`):** `core::contracts::build_check_ensures<Ret, C: Fn(&Ret) -> bool + Copy + 'static>` (`library/core/src/contracts.rs:19-24`) rejects borrowing scalar parameter `x` (`|ret: &u32| *ret == x + 1` fails with `error[E0597]: x does not live long enough; requires that x is borrowed for 'static`), requiring `move` capture (`Copy` inputs only) and blocking non-`'static` `&T` / `&mut T` parameters.
2. **`Runtime(PostCleanup)` pollution even under `-Zcontract-checks=no`:** AST lowering (`compiler/rustc_ast_lowering/src/contract.rs:36-110`) folds `-Zcontract-checks=no` directly to `_3 = const false; switchInt(move _3) -> [0: bb_skip, otherwise: bb1]`, leaving dead `bb1` with closure construction (`{closure@...}`), `Option<{closure}>` locals, and `contract_check_requires` / `contract_check_ensures` calls in `Runtime(PostCleanup)` MIR. In `Runtime(Optimized)` at `-O3 -Zcontract-checks=no`, `#[requires]` is fully eliminated, whereas `#[ensures]` still retains `_2 = const Option::<{closure}>::None` and an 8-byte constant allocation. Thus a `Runtime(PostCleanup)` extractor cannot treat `-Zcontract-checks=no` as transparent unless it strips dead `const false` contract blocks and unused closure locals (or models closures and `Option`).

#### 2.4 Empirical Classification of 24 `core::intrinsics::*` Calls Under `anneal-rustc-capture`

Executing `anneal-rustc-capture capture` (`google/zerocopy@e5a9824d87f7daa5282969a25a8bbca9af985400`) on a `#![no_std]` `#![feature(core_intrinsics)]` probe covering 24 representative intrinsics partitions them into three exact compiler-lowering classes:

| Lowering Class at `Runtime(PostCleanup)` | Tested `core::intrinsics::*` Items | Live `anneal-rustc-capture` Outcome (`e5a9824d87`) |
| --- | --- | --- |
| **Class A: Lowered before `PostCleanup` into admitted scalar MIR (`8 / 24` captured today, `rc = 0`)** | `wrapping_add` (`BinOp::Add`), `add_with_overflow` (`BinOp::AddWithOverflow` -> `OverflowPair`), `three_way_compare` (`BinOp::Cmp` -> `Ordering`), `unreachable` (`TerminatorKind::Unreachable`), `forget` (`Assign(ZeroSized Unit)`), `const { size_of::<u64>() }` & `const { align_of::<u64>() }` (CTFE scalar const), `abort` (diverging `Call { target: None }` -> `Terminator::Unsupported`) | **`status: "captured"`** (`selected_count: 8`, `326`-line `Captured.lean` also verified with `--instantiate` on `align_up_mask::<8>` and `inline_const_size_of::<[u64; 4]>`) |
| **Class B: Lowered before `PostCleanup` into dedicated MIR nodes currently refused (`6 / 24`)** | `unchecked_add` (`BinOp::AddUnchecked`), `unchecked_shl` (`BinOp::ShlUnchecked`), `assume` (`StatementKind::Intrinsic(Assume)`), `ub_checks` (`Operand::RuntimeChecks(UbChecks)`), `transmute_unchecked` (`CastKind::Transmute`), `copy_nonoverlapping` (`StatementKind::Intrinsic(CopyNonOverlapping)` + `*const u8`/`*mut u8`) | Refused fail-closed with exact per-construct diagnostics (`unsupported binary operator: AddUnchecked`, `unsupported statement: assume(...)`, `unsupported operand: UbChecks`, `unsupported cast kind: Transmute`, `unsupported type: *const u8`) |
| **Class C: Survive `PostCleanup` as `TerminatorKind::Call` to `InstanceKind::Intrinsic` (`10 / 24`)** | `ctlz`, `ctpop`, `bswap`, `rotate_left`, `saturating_add`, `exact_div`, `disjoint_bitor`, `is_val_statically_known`, `select_unpredictable`, `offset` (`*const u8`) | Refused fail-closed at `extract.rs:680` (`unsupported terminator: _0 = core::intrinsics::<name>::<u32>(...) -> [return: bb1, unwind unreachable]`) or `extract.rs:200` (`unsupported type: *const u8`) |

Note also `extract.rs:995-1000`: selecting an `#[rustc_intrinsic]` *declaration* itself (inside `library/core/src/intrinsics/`) is intentionally and soundly refused (`"intrinsic ... is unsupported: calls need not execute its fallback body"`).

### 3. Empirical `unsafe` Surface Census and Capability Tiers Across `core`, `alloc`, and `std`

Basis: source + derived

Comment- and string-stripped lexical scanning across all **`946` non-test, non-bench `.rs` files (`362,502` LOC)** under `library/{core,alloc,std}/src` at `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (reproducible via `support/stdlib_mir_probe.py`) yields the exact crate and subsystem inventory:

| Crate / Subsystem | Files | LOC | `unsafe fn` | `unsafe {}` | `unsafe trait` | `unsafe impl` | `# Safety` Docs | `#[rustc_intrinsic]` Decls | `intrinsics::*` Calls | `ub_checks` Preconds | `inherit_overflow` | `#[lang]` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **`core` (total)** | **274** | **163,724** | **668** | **1,378** | **37** | **334** | **291** | **311** | **466** | **66** | **55** | **182** |
| `core::num` | 39 | 29,636 | 31 | 174 | 1 | 3 | 38 | 0 | 180 | 23 | 8 | 0 |
| `core::slice` | 23 | 15,436 | 80 | 266 | 2 | 70 | 34 | 0 | 42 | 13 | 0 | 1 |
| `core::ptr` | 6 | 8,889 | 110 | 150 | 2 | 7 | 50 | 0 | 32 | 17 | 0 | 4 |
| `core::str` | 9 | 8,891 | 40 | 112 | 1 | 28 | 13 | 0 | 4 | 5 | 0 | 0 |
| `core::mem` | 8 | 5,379 | 22 | 61 | 1 | 3 | 21 | 0 | 34 | 1 | 0 | 8 |
| `core::array` | 6 | 2,131 | 10 | 52 | 0 | 3 | 6 | 0 | 3 | 0 | 0 | 0 |
| `core::char` | 4 | 3,446 | 6 | 12 | 0 | 6 | 3 | 0 | 0 | 1 | 0 | 0 |
| `core::ascii` | 2 | 1,408 | 2 | 7 | 0 | 0 | 2 | 0 | 0 | 1 | 0 | 0 |
| `core::cell` | 3 | 3,519 | 6 | 32 | 1 | 14 | 7 | 0 | 0 | 0 | 0 | 1 |
| `core::sync::atomic` | 1 | 4,508 | 18 | 69 | 0 | 3 | 3 | 0 | 100 | 0 | 0 | 0 |
| `core::intrinsics` | 7 | 5,686 | 159 | 14 | 0 | 8 | 41 | 311 | 14 | 0 | 0 | 3 |
| `core::iter` | 46 | 16,859 | 60 | 101 | 5 | 98 | 12 | 0 | 4 | 0 | 33 | 4 |
| **`alloc` (total)** | **68** | **53,010** | **268** | **1,017** | **3** | **115** | **145** | **1** | **19** | **3** | **0** | **3** |
| `alloc::raw_vec` | 1 | 902 | 22 | 42 | 0 | 1 | 19 | 0 | 0 | 0 | 0 | 0 |
| `alloc::vec` | 16 | 6,824 | 20 | 136 | 1 | 26 | 9 | 0 | 4 | 3 | 0 | 0 |
| `alloc::boxed` | 4 | 3,871 | 15 | 71 | 0 | 6 | 10 | 0 | 2 | 0 | 0 | 1 |
| `alloc::rc` | 1 | 4,607 | 33 | 108 | 0 | 10 | 14 | 0 | 3 | 0 | 0 | 0 |
| `alloc::sync` | 1 | 4,976 | 34 | 113 | 0 | 18 | 16 | 0 | 1 | 0 | 0 | 0 |
| `alloc::string` | 1 | 3,619 | 3 | 36 | 0 | 3 | 3 | 0 | 0 | 0 | 0 | 1 |
| `alloc::collections` | 30 | 21,227 | 108 | 408 | 0 | 46 | 64 | 0 | 1 | 0 | 0 | 0 |
| **`std` (total)** | **604** | **145,768** | **596** | **2,152** | **8** | **174** | **124** | **0** | **48** | **0** | **0** | **6** |
| `std::sync` | 26 | 13,343 | 24 | 156 | 1 | 39 | 10 | 0 | 0 | 0 | 0 | 0 |
| `std::io` | 17 | 9,731 | 4 | 46 | 0 | 2 | 1 | 0 | 0 | 0 | 0 | 0 |
| `std::sys` (all) | 348 | 60,674 | 484 | 1,673 | 4 | 115 | 81 | 0 | 13 | 0 | 0 | 5 |

Note that `81.2%` (`484 / 596`) of `std`'s `unsafe fn` declarations and `77.7%` (`1,673 / 2,152`) of `std`'s `unsafe` blocks reside inside `std::sys` platform abstraction layers (`pal`, `sync`, `fs`, `net`), whereas `core` concentrates pure algorithmic, bit-level, layout, pointer, and slice `unsafe` foundations with **zero active inline assembly on `x86_64` and `aarch64`** outside `core::arch` (`stdarch`).

Combining the census with the MIR capture gates above yields three concrete verification capability tiers:

1. **Tier 0 — Pure Scalar, Layout-Arithmetic, UTF-8, and Endian/Slice Slices (Near-Term MIR Reach):**
   - *Targets:* `core::num` (`midpoint`, `abs_diff`, checked/wrapping/overflowing/carrying/borrowing ops, `NonZero` niche constructors, integer `ilog`), `core::ascii`, `core::char` (`from_u32_unchecked`, UTF-8/UTF-16 width & encoding math), `core::str::validations` (UTF-8 state-machine validation), `core::cmp`, `core::mem` (`align_of`/`size_of` layout math), `core::ptr` (`is_aligned`, `align_offset`), and `core::slice` bounds-checked / `split_at_unchecked` / `chunks` index arithmetic.
   - *Exact prerequisites beyond today's scalar profile:* (a) relaxing `capture.rs:922-931` to permit non-semantic crate-local `LangItem` definitions in `SelectedUnit` mode on `core`, (b) adding `-Zforce-unstable-if-unmarked` / multi-root `library/` staging support, (c) modeling pure scalar intrinsics (`ctlz`, `cttz`, `ctpop`, `bitreverse`, `bswap`, `rotate_left/right`, `saturating_add/sub`, `unchecked_add/sub/mul/shl/shr`, `exact_div`, `disjoint_bitor`, `is_val_statically_known`, `select_unpredictable`), (d) modeling `Operand::RuntimeChecks(UbChecks)` + `#[rustc_nounwind]`, and (e) shared/mutable reference, raw-pointer, aggregate/ADT (`Option`, `Result`, `NonZero`), and direct interprocedural `Call` semantics.
2. **Tier 1 — Parametric `<T>` Generics, Memory-Copy/Pointer Intrinsics, and Inherited Overflow Semantics:**
   - *Targets:* Polymorphic `core::slice`, `core::ptr` (`NonNull`, `read`, `write`, `copy`, `copy_nonoverlapping`, `swap`), `core::array`, `core::option`/`core::result`, and `core::iter` adapters (`trusted_len`, `InPlaceIterable`).
   - *Exact prerequisites:* (a) either sound shape-covering monomorphization (`--instantiate` already implemented at `mono.rs:1030-1133`) or parametric polymorphism over layout/validity-abstracted `T`, (b) memory-intrinsic semantics (`CopyNonOverlapping`, `write_bytes`, `offset`/`arith_offset`, `raw_eq`, `CastKind::Transmute`, `const_eval_select`), and (c) demonic/parameterized `is_optional_overflow_check()` semantics for `#[rustc_inherit_overflow_checks]`.
3. **Tier 2 — Interior Mutability, Heap Allocators, Unwind/Drop Glue, Weak-Memory Atomics, OS Syscalls, and SIMD:**
   - *Targets:* `core::cell` (`UnsafeCell`, `Cell`, `RefCell`), `alloc::{raw_vec,vec,boxed,rc,sync,collections}`, `core::sync::atomic` (`100` atomic intrinsic call sites), `std::sync` (`Mutex`, `RwLock`, `Condvar`, `Once`), `std::sys` OS PAL (`libc`/syscall FFI), and `stdarch` (`#[target_feature]`, `#[repr(simd)]`, vendor intrinsics, `asm!`).
   - *Exact prerequisites:* Tree Borrows / `UnsafeCell` aliasing invariants, `Allocator` / `GlobalAlloc` heap contracts, `TerminatorKind::Drop` and cleanup-pad unwinding (`is_cleanup` blocks), RC11 weak-memory concurrency semantics, foreign C-ABI / OS syscall specifications, and ISA/SIMD correspondence.

### 4. `model-checking/verify-rust-std` Ecosystem Comparison and Soundness Pitfalls

Basis: source + documentation + derived

At `model-checking/verify-rust-std@1feeadd937956b8067ec2fb147ef55469361dab4`, six tools are integrated in CI (`Kani`, `ESBMC` v8.7 over Kani GOTO binaries, `Flux`, `VeriFast`, `KMIR` over `stable-mir-json`, and `RAPx`), with open tool-integration applications for `Verus` (`model-checking/verify-rust-std#554`, `model-checking/verify-rust-std#761`) and `Creusot` (`model-checking/verify-rust-std#493`). Out of 29 numbered challenges in `README.md`, 9 are marked resolved (`7` via Kani, `2` via VeriFast on `LinkedList` and `RawVec`, plus `1` testable-SIMD model suite on Challenge 15).

Primary-source inspection of the repository's contracts, harnesses, and open audit issues reveals six structural pitfalls that directly inform MIR-level theorem-proving design:

1. **Over-Strong Zero-Count Postconditions (`library/core/src/ptr/non_null.rs:1147-1188`):**
   `NonNull::copy_to` and `copy_to_nonoverlapping` specify:
   ```rust
   #[requires(count.checked_mul(core::mem::size_of::<T>()).map_or_else(|| false, |size| size <= isize::MAX as usize)
       && ub_checks::can_dereference(NonNull::slice_from_raw_parts(self, count).as_ptr())
       && ub_checks::can_write(NonNull::slice_from_raw_parts(dest, count).as_ptr()))]
   #[ensures(|result: &()| ub_checks::can_dereference(self.as_ptr() as *const u8)
       && ub_checks::can_dereference(dest.as_ptr() as *const u8))]
   ```
   When `count == 0` (or `size_of::<T>() == 0`), `ptr::copy` permits aligned dangling pointers (`NonNull::dangling()`), which satisfy the `0`-byte slice precondition `NonNull::slice_from_raw_parts(self, 0)`, yet **violate the `1`-byte `as *const u8` postcondition**!
2. **Vacuous `*const ()` Precondition Casts (`non_null.rs:482, 528, 1256-1257`; `model-checking/verify-rust-std#783`):**
   In Challenge 6 (marked resolved), `NonNull::as_ref`, `NonNull::as_mut`, and `NonNull::drop_in_place` wrote `ub_checks::can_dereference(self.as_ptr() as *const ())`. Because `()` has size `0` and alignment `1`, `can_dereference` holds for **every non-null pointer** (including misaligned, out-of-bounds, and dangling pointers), causing callers verified against `kani::stub_verified(NonNull::drop_in_place)` to pass while dropping through dangling pointers.
3. **Unchecked Solver Axioms Deriving `False` (`library/core/src/flux_info.rs:17-27`; `model-checking/verify-rust-std#782`):**
   `flux_info.rs` declares global unchecked refinement-solver axioms `ShiftRightByFour` (`16 * (x >> 4) == x`, false whenever `x % 16 != 0`), `MaskLess` (`(x & y) <= x && (x & y) <= y`, false for negative signed integers such as `x = -2, y = 3`), and `ShiftLeft` (`0 < k => n <= (n << k)`, false on wrapping shifts such as `128u8 << 1 == 0`), enabling Flux to prove false runtime postconditions after bit shifts or masks.
4. **Omitted Uninitialized-Memory, Invalid-Value, and Immutable-Aliasing Checks (`model-checking/verify-rust-std#733`, `model-checking/verify-rust-std#775`, `model-checking/verify-rust-std#777`):**
   Default Kani CI runs omit `-Z uninit-checks` and `-Z valid-value-checks` (`can_dereference` treats uninitialized bytes as valid without `-Z uninit-checks`), and CBMC lacks a Rust borrow/aliasing model (`&T` immutability across caller lifetimes cannot be expressed; `model-checking/verify-rust-std#733`).
5. **Finite Monomorphization Blindness (`model-checking/verify-rust-std#734`):**
   Bounded harnesses instantiate generic `<T>` over a small hand-picked list of concrete types; in `RawVec` (`model-checking/verify-rust-std#681`), all 7 chosen types had size `<= 16` bytes, leaving `RawVec::min_non_zero_cap`'s `size_of::<T>() > 1024` branch completely unexercised.
6. **No-Op Runtime Stubs, `if const { true }`, and Source-Copy Drift:**
   - Outside `cfg(kani)`, `library/contracts/safety/src/runtime.rs:4-20` expands `#[safety::{requires,ensures,loop_invariant}]` to no-ops and `library/core/src/ub_checks.rs:192-243` defines `can_dereference`, `can_write`, `same_allocation`, etc. to return `true` unconditionally; inside `ub_checks::{maybe_is_aligned, maybe_is_nonoverlapping}` (`ub_checks.rs:138, 168`), the compile-time `const_eval_select!` arm evaluates `if const { true }`.
   - Deductive tools that cannot ingest unmodified upstream stdlib syntax either maintain edited shadow copies (`verifast-proofs/alloc/{collections/linked_list.rs,raw_vec/mod.rs}/verified/` checked via a separate `refinement-checker` binary and `-ignore_unwind_paths`, trusting ~130 axiomatized stdlib specs) or require rewriting target code inside custom macros (`verus! { ... }`, `model-checking/verify-rust-std#733`, `model-checking/verify-rust-std#755`).

**Architectural fit for kernel-checked MIR verification (`google/zerocopy:anneal`):**
Operating directly on unmodified `Runtime(PostCleanup)` MIR with external Lean 4 specifications (`TargetRole::Specification` separated from `TargetRole::Proof`), zero user/theory axioms (`TrustedBoundary.lean` enforcing only `{propext, Quot.sound, Classical.choice}`), Pass-2 operational correspondence against an independent Miri model (`lean-miri`), and cryptographic Receipt v3 source-hash binding directly eliminates Pitfalls 3 (unsound bitvector axioms), 4 (unchecked uninit/validity bit patterns), and 6 (edited source-copy drift or `verus!` macro rewrites), while requiring explicit anti-vacuity/inhabitation witnesses and `count == 0` / ZST boundary discipline to prevent Pitfalls 1 and 2.

## Boundaries

- **Unsupported in `anneal-rustc-capture` at `google/zerocopy@e5a9824d87f7daa5282969a25a8bbca9af985400`:** Direct capture of `#![no_core]` crates defining `#[lang = "..."]` items, `--extern` / `-L` multi-crate flags, `dylib`/`proc-macro` crate types, `Operand::RuntimeChecks` (`UbChecks`, `ContractChecks`, `OverflowChecks`), `TerminatorKind::Assert`, returning `TerminatorKind::Call`, pointers/references/slices, payload ADTs, floats, closures, coroutines, inline assembly, and targets other than `x86_64-unknown-linux-gnu`.
- **Known not to apply:**
  - Verifying the Rust fallback body of a `#[rustc_intrinsic]` item in `library/core/src/intrinsics/` does **not** verify callers of that intrinsic (`LowerIntrinsics` and backend codegen replace the call).
  - Treating `AssertKind::Overflow` / `OverflowNeg` in `#[rustc_inherit_overflow_checks]` functions as an unconditional runtime panic does **not** hold when inlined or codegen'd into `-Coverflow-checks=no` callers.
  - Passing `-Zub-checks=no` does **not** eliminate `Operand::RuntimeChecks(UbChecks)` from `Runtime(PostCleanup)` or `Runtime(Optimized)` MIR in crates carrying `#![rustc_preserve_ub_checks]` (`core`, `alloc`, `std`).
  - Passing `-Zcontract-checks=no` does **not** leave `Runtime(PostCleanup)` MIR free of closure/Option locals on functions annotated with `#[core::contracts::{requires,ensures}]`.
- **Not examined:**
  - Compilation of `library/std` on Windows (`msvc`/`gnu`) or macOS (`darwin`) targets, or full `x.py` multi-stage bootstrap build times.
  - Empirical execution of Kani, ESBMC, VeriFast, Flux, KMIR, or RAPx binaries on the benchmark challenges (tool behavior is established from pinned repository sources, CI scripts, and primary upstream reproducer records).
- **Unknown:**
  - Upstream `rust-lang/rust`'s final stabilization design for `core::contracts` (`rust-lang/rust#128044`) regarding non-`'static` reference postconditions and `old(...)` pre-state expressions.

## Evidence

- **Rust Compiler & Standard Library (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, observed `2026-11-23`):**
  - `library/core/{Cargo.toml,src/lib.rs:46-120,src/ub_checks.rs:51-185,src/contracts.rs:1-24,src/intrinsics/mod.rs:2680-2750}`: `#![stable]`, `#![no_core]`, `#![rustc_preserve_ub_checks]`, `assert_unsafe_precondition!`, `build_check_ensures`, `contract_check_requires`, `contract_check_ensures`.
  - `library/alloc/{Cargo.toml,src/lib.rs:200}` and `library/std/{Cargo.toml:1-40,src/lib.rs:227,src/env.rs:1051}`: `#![rustc_preserve_ub_checks]`, crate dependencies, `dylib`+`rlib`, and `env!("STD_ENV_ARCH")`.
  - `compiler/rustc_middle/src/mir/{syntax.rs:1334,1578-1600,terminator.rs:162-185}`: `Operand::RuntimeChecks`, `RuntimeChecks::{UbChecks,ContractChecks,OverflowChecks}`, and `AssertKind::is_optional_overflow_check`.
  - `compiler/rustc_mir_build/src/builder/{mod.rs:755-766,expr/as_rvalue.rs:102-123,456-505}`: `RustcInheritOverflowChecks` forcing `check_overflow = true` under `-Coverflow-checks=no`.
  - `compiler/rustc_mir_transform/src/{lib.rs:495-670,lower_intrinsics.rs:12-95,instsimplify.rs:28-64,456-473}`: `Runtime(PostCleanup)` pass pipeline, `LowerIntrinsics`, and `RustcPreserveUbChecks` gating `SimplifyUbCheck`.
  - `compiler/rustc_codegen_ssa/src/mir/{block.rs:708-722,intrinsic.rs:129}`: release-caller erasure of `is_optional_overflow_check()` assertions and codegen ICE on non-`const` nullary `align_of`.
  - `compiler/rustc_ast_lowering/src/contract.rs:25-115` and `compiler/rustc_const_eval/src/const_eval/machine.rs:225-269`: AST contract desugaring and `#[rustc_do_not_const_check]` CTFE hooks.
- **Version-Drift Comparison (`rust-lang/rust@8006091eb71ae7d9e9bccb66c6122c9d68af4466`, observed `2026-11-23`):**
  - `library/core/src/{macros/mod.rs:1677,internal_macros.rs:116,marker.rs:1085,1361}`: built-in macro incompatibilities when compiled by `rustc@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`.
- **Anneal Capture & Verification Implementation (`google/zerocopy@e5a9824d87f7daa5282969a25a8bbca9af985400`, observed `2026-11-23`):**
  - `anneal/flake.nix:17-36`: pinned `rustDate = "2026-05-31"` and Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`).
  - `anneal/trusted/rustc-capture/src/{main.rs:76-180,226-357,driver.rs:48-177,capture.rs:46-234,271-333,345-743,847-1406,extract.rs:115-212,337-685,784-1179,mono.rs:1030-1133}`: CLI flags, `RecordingLoader`, sysroot `(st_dev, st_ino)` checks, `LangItem` gate, `codegen_attrs` gate, `Runtime(PostCleanup)` extraction, and `--instantiate` monomorphization.
  - `anneal/trusted/cargo-anneal/src/{verify.rs:44-256,896-1250,target.rs:54-199}`: Receipt Schema v3, `cargo_request` single-crate restrictions, `verify rustc` subcommand, and `TargetRole` separation.
- **`model-checking/verify-rust-std` (`1feeadd937956b8067ec2fb147ef55469361dab4`, observed `2026-11-23`):**
  - `README.md:1-90`, `rust-toolchain.toml:1-6`, `doc/src/{general-rules.md:1-110,tools.md:1-19,tools/{kani,verifast,kmir,flux,esbmc,rapx}.md}`, `verifast-proofs/{README.md,alloc/raw_vec/mod.rs/README.md}`, `kmir-proofs/README.md`.
  - `library/contracts/safety/src/{lib.rs:1-258,kani.rs:1-39,runtime.rs:1-22}`, `library/core/src/{ub_checks.rs:186-306,flux_info.rs:12-61,ptr/non_null.rs:480-536,609-820,1142-1188}`.
  - Public upstream issue and pull-request records on `model-checking/verify-rust-std`: `model-checking/verify-rust-std#493`, `model-checking/verify-rust-std#554`, `model-checking/verify-rust-std#681`, `model-checking/verify-rust-std#733`, `model-checking/verify-rust-std#734`, `model-checking/verify-rust-std#755`, `model-checking/verify-rust-std#761`, `model-checking/verify-rust-std#775`, `model-checking/verify-rust-std#777`, `model-checking/verify-rust-std#782`, and `model-checking/verify-rust-std#783`.
- **Preserved Package Support:**
  - `support/stdlib_mir_probe.py`: standalone Python 3.10+ script reproducing the `library/{core,alloc,std}` comment-stripped census, `Runtime(PostCleanup)` vs. `Runtime(Optimized)` MIR checks (`UbChecks` + `#![rustc_preserve_ub_checks]`, `#[rustc_inherit_overflow_checks]`, and `#![feature(contracts)]`), and live `anneal-rustc-capture` checks.

## Revalidation

Run the preserved standalone probe in `support/stdlib_mir_probe.py` against any target `rustc` nightly, sysroot, `library/` source tree, and optional `anneal-rustc-capture` binary:

```console
python3 reports/rust-standard-library-mir-capture-unsafe-census-and-verification-tiers/support/stdlib_mir_probe.py \
  --rustc <SYSROOT>/bin/rustc \
  --sysroot <SYSROOT> \
  --rust-library <RUST_SRC>/library \
  --anneal-rustc-capture <PATH_TO_ANNEAL_RUSTC_CAPTURE>
```

What this check establishes and its limits:
- **Census reassessment (`--rust-library`):** Recomputes exact non-test file, LOC, `unsafe fn`, `unsafe {}`, `unsafe trait`, `unsafe impl`, `# Safety`, `#[rustc_intrinsic]`, `intrinsics::*`, `assert_unsafe_precondition!`, `#[rustc_inherit_overflow_checks]`, and `#[lang]` counts for a newer `library/` revision.
- **Compiler MIR-pass reassessment (`--rustc --sysroot`):** Asserts whether `UbChecks` still survives `Runtime(Optimized)` under `#![rustc_preserve_ub_checks]` at `-Copt-level=3 -Zub-checks=no`, whether `#[rustc_inherit_overflow_checks]` still emits `AddWithOverflow` + `assert(...)` under `-Coverflow-checks=no`, and whether `#[core::contracts::requires]` / `#[core::contracts::ensures]` still retain closure/Option state in `Runtime(PostCleanup)` / `Runtime(Optimized)` MIR under `-Zcontract-checks=no`. It does *not* check backend LLVM IR erasure (`rustc_codegen_ssa/src/mir/block.rs`), which requires inspecting `block.rs` (`is_optional_overflow_check`) or `--emit=llvm-ir`.
- **Capture-driver reassessment (`--anneal-rustc-capture`):** Verifies whether `#![no_core]` `LangItem` admission or lowered-intrinsic capture behavior has changed in a newer `anneal-rustc-capture` build.
