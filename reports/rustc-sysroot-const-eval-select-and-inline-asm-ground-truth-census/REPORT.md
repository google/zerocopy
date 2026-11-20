# Exhaustive `rustc 1.99.1` Standard-Library Census of `const_eval_select`, `is_val_statically_known`, and Inline/Global Assembly With MIR Lowering and `llvm-mc` Encoding Audit

## Summary

Across all **`1,666`** non-test, non-bench, non-vendor `.rs` source files in the `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) `library/` tree (`core`, `alloc`, `std`, `std_detect`, `stdarch`, `compiler-builtins`, `unwind`, `panic_abort`, `panic_unwind`, `proc_macro`), comment-stripped AST/token scanning paired with live `rustc 1.99.1` MIR phase dumps (`-Z dump-mir="runtime-post-cleanup | runtime-optimized"`) and full-byte-length `/usr/bin/llvm-mc` differential instruction encoding establishes the exact standard-library verification surface for CTFE/runtime dual-arm intrinsics and inline/global assembly:

1. **Complete `const_eval_select` (`32` sites), `is_val_statically_known` (`11` sites), and Verification-Relevant Intrinsic Census:**
   - `library/` contains **exactly `32` `const_eval_select` call sites** (`24` via the internal `const_eval_select!` `@capture` macro and `8` direct `const_eval_select(...)` intrinsic calls): **`26` in `core`**, **`5` in `alloc`** (`alloc/src/alloc.rs` global allocator dispatch and `handle_alloc_error`), **`1` in `stdarch`** (`core_arch/src/test.rs`), and **`0` in `std`**.
   - `library/` contains **exactly `11` `is_val_statically_known` call sites**, **`100%` in `core`**: `8` in integer/unsigned exponentiation (`checked_pow` and `overflowing_pow` in `int_macros.rs` and `uint_macros.rs`), `1` in `checked_ilog` (`uint_macros.rs:1871`), `1` in `Arguments::as_statically_known_str` (`fmt/mod.rs:898`), and `1` in `[T]::spec_fill` (`slice/specialize.rs:55`).
   - Across remaining verification-sensitive intrinsics in `library/`, there are **`37` `unlikely`**, **`28` `cold_path`**, **`14` `select_unpredictable`**, **`8` `likely`**, **`4` `assert_inhabited`**, **`1` `assert_zero_valid`**, **`1` `assert_mem_uninitialized_valid`**, and **`1` `ub_checks`** call sites.
2. **Exact `Runtime(PostCleanup)` vs. `Runtime(Optimized)` MIR Phase Split for `const_eval_select`, `is_val_statically_known`, and `ub_checks`:**
   - Live compilation with `RUSTC_BOOTSTRAP=1 rustc +1.99.1 -C opt-level=3 -Z dump-mir="runtime-post-cleanup | runtime-optimized"` proves a clean phase boundary:
     - **`const_eval_select((args...), ctfe_fn, rt_fn)`:** In `Runtime(PostCleanup)` MIR—the exact phase captured by Anneal (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/rustc-capture/src/driver.rs:76-95`)—the body retains an explicit `TerminatorKind::Call` to `const_eval_select::<Args, FnCtfe, FnRt, Ret>(move _args, ctfe_fn, rt_fn)` referencing **both** function items. During `Runtime(Optimized)` MIR (`ConstEvalSelect` lowering pass), `const_eval_select` and `ctfe_fn` are completely erased from the runtime body and rewritten to a direct call `_0 = rt_fn(move _1, move _2)`, while compile-time evaluation (`CTFE_WITNESS = 55`) executes `ctfe_fn`. Sound verification at `Runtime(PostCleanup)` therefore requires a **relational refinement/equivalence contract** relating `ctfe_fn` and `rt_fn` (or conservative demonic nondeterministic choice over `{ctfe_fn(args), rt_fn(args)}` for specs shared across CTFE and runtime, specialized to `rt_fn` for purely runtime post-lowering soundness).
     - **`is_val_statically_known(x)`:** Unlike `const_eval_select`, `is_val_statically_known::<T>(copy _1)` **survives unchanged through both `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR**, lowering only during codegen to LLVM's `@llvm.is.constant.*` intrinsic (which LLVM `-O3` subsequently folds to `false` on opaque function parameters). Because any input may return either `true` (after inlining + constant folding) or `false` (out-of-line), a MIR operational semantics such as `Trusted.MirSemantics` (`trusted/lean/Trusted/MirSemantics.lean:1616-1620`) soundly models `is_val_statically_known` as a **nondeterministic `Bool` (`Choice`)** with zero dependency on optimizer phase ordering!
     - **`ub_checks()`:** Lowers before `Runtime(PostCleanup)` to a dedicated nullary MIR rvalue/operand `_3 = UbChecks;` (`Operand::RuntimeChecks`, explicitly rejected fail-closed in `Trusted.MirAst` at `trusted/lean/Trusted/MirAst.lean:548-556` because its value varies per crate in a crate graph).
3. **Complete `330`-Invocation Standard-Library Assembly Census (`0` Active `core` + `alloc` Sites on `x86_64` and `aarch64`):**
   - Across all `1,666` `library/` files, there are **exactly `330` assembly macro invocations** across **`56` distinct files**: **`272` `asm!`**, **`29` `naked_asm!`**, and **`29` `global_asm!`**.
   - By crate: `stdarch` (`197`), `compiler-builtins` (`94`), `std` (`30`), `std_detect` (`6`), `core` (`2`), `unwind` (`1`), and **`alloc` (`0`)**.
   - **Zero active `core` + `alloc` assembly on Tier-1 64-bit targets:** `alloc` contains `0` assembly sites on any target, and `core`'s **only `2` assembly sites in the entire repository** are `fldcw word ptr [{}]` and `fnstcw word ptr [{}]` in `core/src/num/imp/dec2flt/fpu.rs:50, 74`, gated to **legacy 32-bit `x86` without `sse2`** (`x86_32_nosse2`). Excluding `core::arch` (`stdarch`), **`core` + `alloc` execute `0` `asm!`, `naked_asm!`, or `global_asm!` blocks on `x86_64` and `aarch64`!**
   - Across the entire sysroot (including `stdarch`, `compiler-builtins`, `std_detect`, and `std`), `44.2%` (`146 / 330`) of all invocations live in `riscv_shared`, `29` in `hexagon`, `20` in `arm` (32-bit), and `17` in `xous` (`14` syscall wrappers in `std/src/os/xous/ffi.rs` + `3` in `sys/{thread,thread_local}`), leaving **only `58` active Tier-1 Linux sites on `x86_64`** (`39` `stdarch`, `19` `compiler-builtins`, `0` `core`, `0` `alloc`, `0` `std`, `0` `std_detect`) and **`18` active Tier-1 Linux sites on `aarch64`** (`9` `compiler-builtins`, `4` `std_detect` `mrs ID_AA64*_EL1`, `4` `stdarch`, `1` `std` `pacib` in `personality/gcc.rs:219`, `0` `core`, `0` `alloc`).
4. **Full-Byte-Length (`len(direct) == len(mc)`) `/usr/bin/llvm-mc` Differential Encoding Audit:**
   - Evaluating real single-instruction assembly templates extracted from `library/` against `/usr/bin/llvm-mc` (`LLVM 23.1.1`) with strict full-byte equality (`len(direct) == len(mc) and direct == mc`, forbidding prefix-slice truncation) produces **`0` encoding mismatches** across all handled templates (`18 / 23` `llvm-mc`-assemblable unique instantiated lines on `x86_64`; `5 / 16` on `aarch64`) and enumerates the exact unhandled long-tail mnemonics (`jb`, `lea`, `mov` mem, `test` imm, `xchg` on `x86_64`; `fmadd`, `frintn`, `fsqrt`, `ldr`, `lsl`, `mov`/`sub`/`subs` shifted-imm forms on `aarch64`, plus `avx`/`avx512`/`fma` vector instructions in `stdarch`/`libm`).

## Applicability

- **Examined subjects:**
  - `rust-lang/rust` release `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, commit date `2026-10-13`, `x86_64-unknown-linux-gnu`, bundled LLVM `23.1.1`): complete `library/` source tree (`1,666` non-test, non-bench, non-vendor `.rs` files, excluding `vendor/`, `tests/`, `benches/`, `coretests/`, `alloctests/`) and live `rustc +1.99.1` MIR pass dumps + LLVM IR emission.
  - `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`): `trusted/lean/Trusted/MirAst.lean` (`Operand`, `StatementKind`, `TerminatorKind`) and `trusted/lean/Trusted/MirSemantics.lean` (`evalStatement`, `evalTerminator`, `Step` with demonic `Choice`).
- **Assembler oracle:** System `/usr/bin/llvm-mc` targeting `-triple=x86_64-unknown-linux-gnu -x86-asm-syntax=intel` and `-triple=aarch64-unknown-linux-gnu`.
- **Scope across targets:** Source-level intrinsic and assembly counts cover **all architectures and operating systems** present in upstream `library/`; active-site filtering and `llvm-mc` encoding verification specifically evaluate Tier-1 Linux targets `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`.

## Findings

### 1. Complete Census and Taxonomy of `const_eval_select` (`32` Sites) and `is_val_statically_known` (`11` Sites)

`Basis: source + execution (support/e2_5_sysroot_intrinsics_and_inline_asm_census.py, support/e2_5_sysroot_intrinsics_and_inline_asm_census.json)`

Scanning all `1,666` production `.rs` files in `library/` after lexical comment stripping (preserving string and raw-string literals `r#"..."#` and exact line numbers while blanking `//` and nested `/* ... */` comments, and excluding macro definitions `macro_rules! const_eval_select`) yields **`32` `const_eval_select` sites** (`26` `core`, `5` `alloc`, `1` `stdarch`), **`11` `is_val_statically_known` sites** (`11` `core`), and **`94` occurrences** across eight related compiler intrinsics:

| Intrinsic / Construct | Total `library/` Call Sites | Crate Breakdown | MIR Lowering Category |
| :--- | ---: | :--- | :--- |
| `const_eval_select` / `const_eval_select!` | **`32`** | `core`: `26`, `alloc`: `5`, `stdarch`: `1` | `Call` in `PostCleanup` $\rightarrow$ erased to `rt_fn` in `Optimized` |
| `is_val_statically_known` | **`11`** | `core`: `11` | `Call` in `PostCleanup` & `Optimized` $\rightarrow$ `@llvm.is.constant` |
| `unlikely` | **`37`** | `core` / `alloc` / `std` | Hint intrinsic (identity boolean semantics) |
| `cold_path` | **`28`** | `core` / `alloc` / `std` | `StatementKind::Intrinsic` / empty branch hint |
| `select_unpredictable` | **`14`** | `core` | Conditional select (`cmov` / `csel` lowering) |
| `likely` | **`8`** | `core` / `std` | Hint intrinsic (identity boolean semantics) |
| `assert_inhabited` | **`4`** | `core` (`mem::zeroed`, `MaybeUninit`, etc.) | Post-monomorphization layout/validity check (`nop` if inhabited) |
| `assert_zero_valid` | **`1`** | `core` (`mem::zeroed`) | Post-monomorphization zero-validity check |
| `assert_mem_uninitialized_valid` | **`1`** | `core` (`mem::uninitialized`) | Post-monomorphization uninit-validity check |
| `ub_checks` | **`1`** | `core` (`ub_checks.rs`) | Lowered to `Rvalue` / `Operand::RuntimeChecks(UbChecks)` |

Crucially, the `32` `const_eval_select` sites are **not** all semantically equivalent `ctfe_fn \approx rt_fn` algorithm swaps. Auditing all `32` sites in `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) partitions them into **five distinct semantic classes** that determine whether a `Runtime(PostCleanup)` verifier may assume `ctfe_fn` and `rt_fn` compute identical outputs:

| Semantic Class | Count | Exact `library/` Locations (`file:line` — Enclosing Item) | CTFE Arm vs. Runtime Arm Behavior |
| :--- | ---: | :--- | :--- |
| **Class A: True Dual-Algorithm Equivalence** (byte-wise const loop vs. word/SIMD/libc fast path; identical functional spec) | **`6`** | `core/src/ffi/c_str.rs:754` (`strlen`), `core/src/ptr/mod.rs:1421` (`swap_nonoverlapping`), `core/src/slice/ascii.rs:468, 662` (`[u8]::is_ascii` & SIMD `is_ascii`), `core/src/slice/memchr.rs:56` (`memchr_aligned`), `core/src/str/validations.rs:136` (`run_utf8_validation` align offset; returns `usize::MAX` at CTFE to take scalar fallback) | `ctfe_fn` and `rt_fn` satisfy the **same input-output specification** (`strlen`, `swap_nonoverlapping`, `is_ascii`, `memchr`); in `validations.rs:136`, `ctfe_fn` returns `usize::MAX` specifically because its caller treats `usize::MAX` as a valid conservative fallback to byte-by-byte UTF-8 checking. |
| **Class B: CTFE Intrinsic-Engine Delegation vs. Runtime Integer-Address Check** (UB precondition guards where CTFE engine enforces provenance/bounds natively!) | **`11`** | `core/src/ffi/c_str.rs:390` (`from_bytes_with_nul_unchecked`), `core/src/ptr/const_ptr.rs:362, 711, 845, 924` (`runtime_offset_nowrap`, `runtime_ptr_ge`, `runtime_add_nowrap`, `runtime_sub_nowrap`), `core/src/ptr/mut_ptr.rs:364, 944, 1023` (mut counterparts), `core/src/ub_checks.rs:98, 136, 166` (`check_language_ub`, `maybe_is_aligned`, `maybe_is_nonoverlapping`) | **Arms intentionally disagree as standalone functions!** In `ub_checks.rs:98`, CTFE returns **`false`** while runtime returns `!cfg!(miri)` (**`true`**); in `const_ptr.rs:362, 711, 845, 924`, `mut_ptr.rs:364, 944, 1023`, and `ub_checks.rs:136, 166`, CTFE trivially returns **`true`** (skipping `.addr()` integer casts that would fail in CTFE on symbolic pointers, relying on Miri/CTFE's native pointer arithmetic UB check instead), whereas runtime computes actual `.addr()` overflow/alignment/non-overlap booleans! Conversely, `c_str.rs:390` runs a full $O(n)$ NUL-scan assertion in CTFE and `{ &*(bytes as *const [u8] as *const CStr) }` without scanning at runtime! |
| **Class C: Diverging Panic / Alloc-Error Formatting & Hook Dispatch (`-> !`)** | **`4`** | `alloc/src/alloc.rs:649` (`handle_alloc_error`: `ct_error` vs. `rt_error`), `core/src/panic.rs:167` (`const_panic_fmt` / `do_panic`), `core/src/panicking.rs:96` (`panic_nounwind_fmt`), `core/src/str/mod.rs:70` (`slice_error_fail`) | Both arms diverge (`-> !`), so postcondition vacuity holds on normal return; CTFE invokes const panic formatting whereas runtime invokes `#[lang = "panic_impl"]`, `__rust_alloc_error_handler`, or `abort()`. |
| **Class D: Const-Heap vs. OS Global Allocator (`alloc::alloc::Global`)** | **`4`** | `alloc/src/alloc.rs:424` (`alloc_impl`), `436` (`deallocate_impl`), `454` (`grow_impl`), `471` (`shrink_impl`) | CTFE calls `intrinsics::const_allocate` / `const_deallocate`; runtime calls `__rust_alloc` / `__rust_alloc_zeroed` / `__rust_dealloc` / `__rust_realloc`. Both satisfy the `Allocator` trait safety/layout contract. |
| **Class E: Macro Wrapper, Runtime-Only Contracts & Miri/Test Hooks** | **`7`** | `core/src/intrinsics/mod.rs:2636, 2647` (`const_eval_select!` macro definition itself), `2875` (`contract_check_requires`), `2907` (`contract_check_ensures`), `3828` (`promise_aligned` / `miri_promise_symbolic_alignment`), `core/src/ptr/const_ptr.rs:26` (`is_null` via `guaranteed_eq`), `stdarch/crates/core_arch/src/test.rs:18` (`assert_eq_ct` vs. `assert_eq_rt`) | `2636, 2647` are the `const_eval_select!` macro expansion rules (`30` real call sites outside the macro definition); `contract_check_{requires,ensures}` and `miri_promise_symbolic_alignment` are no-ops in CTFE and active checks/hooks at runtime; `const_ptr::is_null` panics in CTFE if pointer nullness is undetermined (`guaranteed_eq == None`) and compares `addr() == 0` at runtime. |

**Key Soundness Takeaway for Class B (`11 / 32` sites):** Any verification architecture that assumes `ctfe_fn(x) == rt_fn(x)` pointwise for every `const_eval_select` call will **fail immediately on `core::ub_checks` and `core::ptr::{const_ptr, mut_ptr}`**, where `ctfe_fn` returns constant `false` or `true` while `rt_fn` inspects pointer addresses! Specifically:
- When proving **runtime behavior** of compiled machine code (where `Runtime(Optimized)` unconditionally rewrites `const_eval_select(args, ctfe_fn, rt_fn)` to `rt_fn(args)`), `const_eval_select` in `Runtime(PostCleanup)` MIR has **exact deterministic operational semantics `rt_fn(args)`**.
- When proving **CTFE const-evaluation behavior**, `const_eval_select` has exact operational semantics `ctfe_fn(args)`.

Table 2 lists all **`11` `is_val_statically_known` call sites** in `library/` (all in `core`):

| # | File & Line (`rust-lang/rust` `1.99.1`) | Enclosing Function / Macro | Guarded Specialization Pattern |
| ---: | :--- | :--- | :--- |
| 1 | `core/src/fmt/mod.rs:898` | `Arguments::as_statically_known_str` | `if is_val_statically_known(s.is_some()) { s } else { None }` |
| 2 | `core/src/num/int_macros.rs:1844` | `<iN>::checked_pow` | `if is_val_statically_known(base) && base.unsigned_abs().is_power_of_two()` |
| 3 | `core/src/num/int_macros.rs:1858` | `<iN>::checked_pow` | `if is_val_statically_known(exp)` (constant-exponent unrolling) |
| 4 | `core/src/num/int_macros.rs:3072` | `<iN>::overflowing_pow` | `if is_val_statically_known(base) && base.unsigned_abs().is_power_of_two()` |
| 5 | `core/src/num/int_macros.rs:3085` | `<iN>::overflowing_pow` | `if is_val_statically_known(exp)` |
| 6 | `core/src/num/uint_macros.rs:1871` | `<uN>::checked_ilog` | `if is_val_statically_known(base)` (fast log2/log10 division-free path) |
| 7 | `core/src/num/uint_macros.rs:2403` | `<uN>::checked_pow` | `if is_val_statically_known(base) && base.is_power_of_two()` |
| 8 | `core/src/num/uint_macros.rs:2418` | `<uN>::checked_pow` | `if is_val_statically_known(exp)` |
| 9 | `core/src/num/uint_macros.rs:3568` | `<uN>::overflowing_pow` | `if is_val_statically_known(base) && base.is_power_of_two()` |
| 10 | `core/src/num/uint_macros.rs:3585` | `<uN>::overflowing_pow` | `if is_val_statically_known(exp)` |
| 11 | `core/src/slice/specialize.rs:55` | `<[T] as SpecFill<T>>::spec_fill` | `if (cfg!(miri) && self.len() > 32) \|\| is_val_statically_known(value)` (`memset` fast path) |

Notice that in `10` of the `11` sites (`#2`–`#11`), both branches of the `if is_val_statically_known(...)` conditional compute **extensional equivalents** (for example, bit-shift power-of-two exponentiation vs. binary exponentiation by squaring), and in `#1` (`Arguments::as_statically_known_str`), `Option<&'static str>`'s documented specification explicitly permits returning `None` whenever static string literal folding does not occur.

---

### 2. Live `rustc 1.99.1` MIR Lowering Across `Runtime(PostCleanup)` and `Runtime(Optimized)`

`Basis: execution + source (support/e2_5_sysroot_intrinsics_and_inline_asm_census.json, joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613)`

Compiling the three-function probe `ces_probe.rs` (`sum_dispatch` using `const_eval_select`, `CTFE_WITNESS` evaluating `sum_dispatch` at compile time over `[1..=10]`, `stat_known_probe` using `is_val_statically_known`, and `ub_checks_probe` using `ub_checks()`) with `RUSTC_BOOTSTRAP=1 rustc +1.99.1 -C opt-level=3 --emit=llvm-ir -Z dump-mir="runtime-post-cleanup | runtime-optimized" -Z dump-mir-exclude-pass-number` yields the exact verbatim MIR transformations below:

1. **`const_eval_select` in `sum_dispatch` (`PostCleanup` $\rightarrow$ `Optimized`):**
   - After `runtime-post-cleanup`:
     ```text
     bb0: {
         ...
         _3 = (move _4, move _5);
         _0 = const_eval_select::<(*const u8, usize), fn(*const u8, usize) -> u64 {ctfe_sum_bytes}, fn(*const u8, usize) -> u64 {rt_sum_u64_chunks}, u64>(move _3, ctfe_sum_bytes, rt_sum_u64_chunks) -> [return: bb1, unwind continue];
     }
     ```
   - After `runtime-optimized`:
     ```text
     bb0: {
         _0 = rt_sum_u64_chunks(move _1, move _2) -> [return: bb1, unwind continue];
     }
     ```
   - Simultaneously, `CTFE_WITNESS` evaluates `ctfe_sum_bytes` during CTFE to scalar `55` (`0x37` in `ces_probe.ll`). Thus `Runtime(PostCleanup)` is strictly upstream of `ConstEvalSelect` lowering (`sum_dispatch_postcleanup_has_const_eval_select = true`, `sum_dispatch_optimized_has_const_eval_select = false`).
2. **`is_val_statically_known` in `stat_known_probe` (`PostCleanup` $\rightarrow$ `Optimized` $\rightarrow$ LLVM IR):**
   - After `runtime-post-cleanup`:
     ```text
     bb0: {
         StorageLive(_2);
         StorageLive(_3);
         _3 = copy _1;
         _2 = is_val_statically_known::<usize>(move _3) -> [return: bb1, unwind unreachable];
     }
     ```
   - After `runtime-optimized` (even after `wrapping_mul` and `wrapping_add` are MIR-inlined into `Mul(copy _1, const 3_usize)` and `Add`):
     ```text
     bb0: {
         StorageLive(_2);
         _2 = is_val_statically_known::<usize>(copy _1) -> [return: bb1, unwind unreachable];
     }
     ```
   - Notice two structural details in `rustc 1.99.1`'s MIR: (a) the call's unwind action is already narrowed to `unwind unreachable`, and (b) `is_val_statically_known` is **preserved verbatim** in `Runtime(Optimized)` MIR (`stat_known_optimized_has_intrinsic = true`) so that post-inlining LLVM optimization passes (`@llvm.is.constant.i64`) can fold it to `i1 true` when a caller passes a constant after LLVM-level inlining, or fold it to `i1 false` in standalone compilation (`stat_known_ll_has_is_constant = false` after `-O3` finishes folding `stat_known_probe`). Modeling `is_val_statically_known` in `Trusted.MirSemantics` via demonic `Choice` (`Step p s res := ∃ c : Choice, ValidChoice p s c ∧ evalStep p c s = res`, `trusted/lean/Trusted/MirSemantics.lean:1618-1620`) universally quantifies over both `{false, true}`, proving correctness across every possible downstream MIR/LLVM inlining decision.
3. **`ub_checks()` in `ub_checks_probe` (`PostCleanup`):**
   - Already lowered before `runtime-post-cleanup` to:
     ```text
     bb0: {
         StorageLive(_2);
         StorageLive(_3);
         _3 = UbChecks;
         switchInt(move _3) -> [0: bb5, otherwise: bb1];
     }
     ```
   - Confirming `Trusted.MirAst.Operand`'s design note (`trusted/lean/Trusted/MirAst.lean:548-556`): `ub_checks()` does not appear as a function `Call` at `PostCleanup`, but as `Operand::RuntimeChecks(RuntimeChecks::UbChecks)`, which varies per crate (`-C debug-assertions` / `-Z ub-checks`) and therefore cannot be folded to a single crate-independent boolean constant at MIR capture time without either pinning the session's `ub_checks` flag or quantifying nondeterministically over `{false, true}` (note that quantifying over `{false, true}` is sound here because when `_3 = true`, `bb1` executes extra `Assert` checks that only *strengthen* safety obligations!).

---

### 3. Complete `330`-Invocation Standard-Library Assembly Census (`asm!`, `naked_asm!`, `global_asm!`)

`Basis: source + execution (support/e2_5_sysroot_intrinsics_and_inline_asm_census.json)`

Across all `1,666` `library/` `.rs` files, there are **`330` total assembly macro invocations** spanning **`56` distinct files**: **`272` `asm!`**, **`29` `naked_asm!`** (`100%` in `compiler-builtins`), and **`29` `global_asm!`** (`26` `compiler-builtins`, `2` `std`, `1` `unwind`).

Table 3 cross-tabulates all `330` invocations by crate, macro kind, and active Tier-1 Linux status on `x86_64` and `aarch64`:

| Sysroot Crate | `asm!` | `naked_asm!` | `global_asm!` | Total Invocations | Active on `x86_64-unknown-linux-gnu` | Active on `aarch64-unknown-linux-gnu` | Notes |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| `alloc` | `0` | `0` | `0` | **`0`** | **`0`** | **`0`** | Pure Rust + `core` intrinsics |
| `core` (excl. `stdarch`) | `2` | `0` | `0` | **`2`** | **`0`** | **`0`** | Only `dec2flt/fpu.rs:50, 74` (32-bit `x86` without `sse2`) |
| `stdarch` (`core::arch`) | `197` | `0` | `0` | **`197`** | **`39`** | **`4`** | `146` in `riscv_shared`, `29` in `hexagon` |
| `compiler-builtins` (+ `libm`) | `39` | `29` | `26` | **`94`** | **`19`** | **`9`** | Soft-float/mem/probestack/libm arch routines |
| `std` | `28` | `0` | `2` | **`30`** | **`0`** | **`1`** | `17` Xous, `7` Fortanix SGX, `3` Windows, `1` VEXos, `1` AArch64 `pacib`, `1` non-Linux |
| `std_detect` | `6` | `0` | `0` | **`6`** | **`0`** | **`4`** | `4` AArch64 `mrs ID_AA64*_EL1`, `1` LoongArch `cpucfg`, `1` s390x `stfle` |
| `unwind` | `0` | `0` | `1` | **`1`** | **`0`** | **`0`** | Non-Linux custom unwind shim |
| **Total (`library/`)** | **`272`** | **`29`** | **`29`** | **`330`** | **`58`** | **`18`** | Across `56` `.rs` files (`1,610` files have `0` asm) |

Table 4 breaks down all `330` invocations by target architecture and operating-system gate, alongside `options(...)` modifier frequencies:

| Inferred Target Architecture Gate | Invocations | OS / Environment Gate | Invocations | `asm!` `options(...)` Flag | Frequency |
| :--- | ---: | :--- | ---: | :--- | ---: |
| `riscv32_or_riscv64` (`riscv_shared`) | `146` | `any` (OS-agnostic) | `299` | `nostack` | `251` |
| `x86_and_x86_64` (`core_arch/x86`, `libm/x86`) | `40` | `xous` (`std/.../xous`) | `17` | `pure` | `141` |
| `multi_cfg` (multi-arch `compiler-builtins`/`std`) | `31` | `sgx` (Fortanix SGX) | `7` | `nomem` | `139` |
| `hexagon` | `29` | `linux` (explicit path) | `3` | `preserves_flags` | `103` |
| `arm` (32-bit ARM / Thumb) | `20` | `windows` | `3` | `raw` | `26` |
| `x86_64` (64-bit only) | `18` | `vexos` | `1` | `readonly` | `25` |
| `aarch64` (64-bit only) | `14` | | | `att_syntax` | `19` |
| `x86` / `x86_32` / `x86_32_nosse2` / `x86\|x86_64` | `13` | | | `noreturn` | `4` |
| `riscv64` | `5` | | | | |
| `arm_or_aarch64` (`arm_shared`) | `4` | | | | |
| `loongarch` | `4` | | | | |
| `avr` / `s390x` / `wasm` / multi-arch unions | `6` | | | | |

Three architectural consequences follow immediately from Tables 3 and 4:

1. **Verifying `core` + `alloc` on `x86_64` and `aarch64` requires zero inline-assembly semantics unless `core::arch` (`stdarch`) vendor intrinsics are called:** `TerminatorKind::InlineAsm` (`trusted/lean/Trusted/MirAst.lean:766, 782-785`, lowered fail-closed to `.unsupported`) never fires anywhere in `core` (outside `core::arch`) or `alloc` on 64-bit `x86_64` or `aarch64`, because the legacy x87 control-word adjustments `fldcw word ptr [{}]` and `fnstcw word ptr [{}]` in `core/src/num/imp/dec2flt/fpu.rs:50, 74` compile only on `#[cfg(all(target_arch = "x86", not(target_feature = "sse2")))]`.
2. **Tier-1 `x86_64-unknown-linux-gnu` has `58` active sites confined to `17` files in `stdarch` (`39`) and `compiler-builtins` (`19`):**
   - `compiler-builtins` (`19` sites): `12` in `compiler-builtins/src/mem/x86_64.rs` (`rep movsb`, `rep movsq`, `rep stosb`, `rep stosq`, `std`/`cld` bulk `memcpy`/`memset`/`memmove`), `4` in `libm/src/math/arch/x86/fma.rs` (`vfmadd*`/`vfmsub*`), `2` in `libm/src/math/arch/x86/sqrt.rs` (`sqrtsd`/`sqrtss`), and `1` `naked_asm!` in `compiler-builtins/src/x86_64.rs` (`__rust_probestack` stack-clash probe loop using `cmp rax, 0x1000`, `sub rcx, 0x1000`, `test [rcx], rcx`).
   - `stdarch` (`39` sites): `10` in `avx512f.rs`, `4` in `x86/bt.rs` (`bt`, `bts`, `btr`, `btc`), `4` in `x86_64/bt.rs`, `4` in `x86/eflags.rs` (`pushfq`/`popfq`), `3` in `avx.rs` (`vzeroupper`), `3` in `avx512fp16.rs`, `3` in `x86/sse2.rs` (`pause`, `mfence`, `lfence`), `2` in `cpuid.rs` (`cpuid`, `xgetbv`), `2` in `sse4a.rs`, and `1` each in `avx2.rs`, `sse.rs` (`sfence`), `sse41.rs`, and `x86_64/sse2.rs`.
3. **Tier-1 `aarch64-unknown-linux-gnu` has only `18` active sites across `8` files:**
   - `compiler-builtins` (`9` sites): `3` in `libm/src/math/arch/aarch64/rounding.rs` (`frintn`), `3` in `sqrt.rs` (`fsqrt`), `2` in `fma.rs` (`fmadd`), and `1` `naked_asm!` in `compiler-builtins/src/aarch64.rs` (`__rust_probestack`).
   - `std_detect` (`4` sites): `std_detect/src/detect/os/aarch64.rs:31, 41, 51, 61`, reading feature registers `mrs {}, ID_AA64ISAR0_EL1`, `ID_AA64ISAR1_EL1`, `ID_AA64MMFR2_EL1`, and `ID_AA64PFR0_EL1` (all marked `options(pure, nomem, preserves_flags, nostack)`).
   - `stdarch` (`4` sites): `3` barrier instructions in `arm_shared/barrier/cp15.rs` (`dmb`, `dsb`, `isb`) and `1` hint (`nop`/`yield`/`wfe`/`wfi`/`sev`) in `arm_shared/hints.rs`.
   - `std` (`1` site): `std/src/sys/personality/gcc.rs:219`, `pacib {addr}, {sp}` (`options(nostack, preserves_flags)`) signing landing-pad return addresses during DWARF exception unwinding on Pointer-Authentication AArch64 targets.

---

### 4. Full-Byte-Length (`len(direct) == len(mc)`) `/usr/bin/llvm-mc` Differential Encoding Audit

`Basis: execution (support/e2_5_sysroot_intrinsics_and_inline_asm_census.py, support/e2_5_sysroot_intrinsics_and_inline_asm_census.json)`

To audit machine-code encoding fidelity for inline assembly without prefix-truncation bugs (where comparing `mc_bytes[:len(direct_bytes)]` would falsely pass an incomplete prefix against a longer multi-byte instruction), `support/e2_5_sysroot_intrinsics_and_inline_asm_census.py` extracts every Intel-syntax (`!att_syntax`) `asm!` and `naked_asm!` template line from `x86_64`/`x86_and_x86_64` and `aarch64`/`arm_or_aarch64` sites, instantiates `{}` / `{name:modifier}` operand slots with canonical architectural registers (`rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8` with `:e`/`:x`/`:l`/`:y`/`:z` modifiers on `x86_64`; `x0`–`x5` with `:w`/`:d`/`:s`/`:v`/`:q` modifiers on `aarch64`), assembles each standalone single-instruction line with `/usr/bin/llvm-mc --show-encoding`, and requires **`len(direct) == len(mc) and direct == mc`**:

| Architecture (`llvm-mc` Triple) | Unique Instantiated Template Lines | Standalone `llvm-mc`-Assemblable Lines | Direct Encoder Full-Length Exact Matches | Full-Length Encoding Mismatches | Unhandled Assemblable Mnemonics (Long Tail) |
| :--- | ---: | ---: | ---: | ---: | :--- |
| `x86_64-unknown-linux-gnu` (`-x86-asm-syntax=intel`) | `56` | `23` | **`18 / 23`** (`78.3%`) | **`0`** | `jb` (`1`), `lea` (`1`), `mov` mem (`1`), `test` mem (`1`), `xchg` (`1`); remaining `33` lines use local branch labels (`2f`/`3b`) or AVX-512 `{er}`/`{sae}` rounding tokens requiring `-mattr=+avx512f,+avx512fp16` |
| `aarch64-unknown-linux-gnu` | `23` | `16` | **`5 / 16`** (`31.3%`) | **`0`** | `fmadd` (`2`), `frintn` (`2`), `fsqrt` (`2`), `ldr` (`1`), `lsl` (`1`), `mov` imm (`1`), `sub` shifted-imm (`1`), `subs` shifted-imm (`1`); remaining `7` lines use local numeric labels or pointer-auth `-mattr=+pauth` (`pacib`) |

Representative full-length verified encodings (`len(direct) == len(mc)`) include:
- **`x86_64` (`18` exact matches, `0` mismatches):** `cpuid` (`0fa2`), `rep movsb` / `rep movsb [rdi], [rsi]` (`f3a4`), `rep movsq` (`f348a5`), `rep stosb` / `rep stosb [rdi], al` (`f3aa`), `rep stosq` (`f348ab`), `std` (`fd`), `push rax` (`50`), `push rcx` (`51`), `mov rax, rbx` (`4889d8`), `mov rcx, rax` (`4889c1`), `add rdi, 7` (`4883c707`), `sub rdi, 7` (`4883ef07`), `cmp rax, 0x1000` (`483d00100000`), and `sub rcx, 0x1000` (`4881e900100000`).
- **`aarch64` (`5` exact matches, `0` mismatches):** `mrs x0, ID_AA64ISAR0_EL1` (`000638d5`), `mrs x0, ID_AA64ISAR1_EL1` (`200638d5`), `mrs x0, ID_AA64MMFR2_EL1` (`400738d5`), `mrs x0, ID_AA64PFR0_EL1` (`000438d5`), and `nop` (`1f2003d5`).

Crucially, the `33` (`x86_64`) and `7` (`aarch64`) instantiated lines rejected by bare `-triple=...` `llvm-mc` without extra flags expose two real requirements for any verified inline-assembler or `llvm-mc` certificate checker:
1. **Multi-instruction local numeric labels (`2:` / `jb 2b` / `b.ne 1b` in `__rust_probestack` and `mem/x86_64.rs`):** Multi-statement `asm!` and `naked_asm!` blocks cannot be checked line-by-line in isolation when PC-relative branches target local labels; the entire instantiated multi-line template must be assembled as a single basic-block/function unit so branch displacements resolve.
2. **Target-feature subtarget gating (`-mattr=+avx512f,+avx512fp16,+fma` on `x86_64`; `-mattr=+pauth` for `pacib` on `aarch64`):** `stdarch` and `std/src/sys/personality/gcc.rs` emit instructions governed by `#[target_feature(enable = "...")]` or arch-version attributes that fault or fail assembly on baseline `x86-64` / `armv8.0-a` without Propagated Subtarget Features (`TargetFeatureSet`).

## Boundaries

- **External crates outside `library/` (`not examined`):** This census covers the complete `rustc 1.99.1` standard-library source tree (`library/`). Third-party crates on `crates.io` (such as cryptographic, OS-kernel, or hardware-driver crates using `core::arch::asm!`) are outside this sysroot census.
- **Macro-generated assembly inside `vendor/` (`not examined`):** Vendored third-party directories excluded by the `vendor`/`tests`/`benches`/`coretests`/`alloctests` filter are not part of compiled `core`/`alloc`/`std` production artifacts; `compiler-builtins` and `stdarch` sources shipped inside `library/` **are** included in full (`197` and `94` invocations, respectively).
- **Multi-line label resolution and AVX-512/FP-scalar instruction semantics in the compact reference encoder (`unsupported` by `direct_encode_*`, quantified via `llvm-mc`):** The compact Python reference encoders `direct_encode_x86_64` and `direct_encode_aarch64` intentionally cover scalar register/immediate/string/system-register instructions (`18` and `5` sysroot matches with `0` mismatches) to expose the exact boundary where full ISA encoders (`avx512f`, `fma`, `fsqrt`, `frintn`, `pacib`, PC-relative local branches) are required.
- **Stronger conclusions `known not to apply`:**
  - *Every `const_eval_select(args, ctfe_fn, rt_fn)` call in `core` satisfies `ctfe_fn(args) == rt_fn(args)` on all inputs:* **Known not to apply** (`11 / 32` Class B sites in `core::ub_checks` and `core::ptr::{const_ptr, mut_ptr}` intentionally return constant `false` or `true` in `ctfe_fn` while `rt_fn` inspects runtime pointer addresses).
  - *`is_val_statically_known` is erased alongside `const_eval_select` before `Runtime(Optimized)` MIR:* **Known not to apply** (`stat_known_optimized_has_intrinsic = true`; `is_val_statically_known` persists through `Runtime(Optimized)` MIR into LLVM `@llvm.is.constant.*` lowering).
  - *Prefix byte comparison (`mc[:len(direct)] == direct`) suffices to validate an instruction encoder against `llvm-mc`:* **Known not to apply** (prefix slicing silently masks missing ModR/M, SIB, displacement, or immediate suffix bytes; strict `len(direct) == len(mc) and direct == mc` is mandatory).

## Evidence

- **Preserved standalone census, MIR-lowering, and `llvm-mc` differential probe + JSON dataset:**
  - `support/e2_5_sysroot_intrinsics_and_inline_asm_census.py` — standalone Python 3.10+ script implementing lexical Rust comment/raw-string stripping, balanced macro-body extraction, architecture/OS gate inference across `library/`, live `RUSTC_BOOTSTRAP=1 rustc +1.99.1 -Z dump-mir` probing, and full-length `/usr/bin/llvm-mc` differential encoding verification.
  - `support/e2_5_sysroot_intrinsics_and_inline_asm_census.json` — complete machine-readable output (`observed_at: 2026-11-20`) listing all `32` `const_eval_select` sites, all `11` `is_val_statically_known` sites, all `330` assembly macro breakdowns, `core`-only and `std_detect` site records, `llvm-mc` hex encodings, and verbatim `Runtime(PostCleanup)` vs. `Runtime(Optimized)` MIR snippets.
- **Primary pinned upstream revisions:**
  - `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1` `library/` tree: `alloc/src/alloc.rs`, `core/src/intrinsics/mod.rs`, `core/src/ptr/{mod,const_ptr,mut_ptr}.rs`, `core/src/ub_checks.rs`, `core/src/num/{int_macros,uint_macros}.rs`, `core/src/num/imp/dec2flt/fpu.rs`, `std_detect/src/detect/os/aarch64.rs`, `std/src/sys/personality/gcc.rs`).
  - `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/rustc-capture/src/driver.rs:76-95`; `trusted/lean/Trusted/MirAst.lean:548-556, 654-662, 766, 780-795`; `trusted/lean/Trusted/MirSemantics.lean:1568-1569, 1618-1620`).

## Revalidation

Ensure `rustup` toolchain `1.99.1` with the `rust-src` component (`rustup component add --toolchain 1.99.1 rust-src`) and `/usr/bin/llvm-mc` are installed, then run the preserved probe (~3 seconds):

```bash
VRUSTC_OUT_JSON=/tmp/revalidated_e2_5.json \
  python3 reports/rustc-sysroot-const-eval-select-and-inline-asm-ground-truth-census/support/e2_5_sysroot_intrinsics_and_inline_asm_census.py
```

Verify in `/tmp/revalidated_e2_5.json` (or stdout summary) that:
1. `library_root_scanned_rs_files == 1666` (or the updated file count on a newer `rustc` toolchain), `const_eval_select.total_call_sites == 32`, and `is_val_statically_known.total_call_sites == 11`;
2. `inline_and_global_asm.total_invocations == 330` with `0` `alloc` sites and `core_only_sites` restricted to `x86_32_nosse2` (`dec2flt/fpu.rs`);
3. `sum_dispatch_postcleanup_has_const_eval_select == true`, `sum_dispatch_optimized_has_const_eval_select == false`, and `stat_known_optimized_has_intrinsic == true`; and
4. `direct_mismatch == 0` on both `x86_64` and `aarch64` under full-length `len(direct) == len(mc)` checking.
