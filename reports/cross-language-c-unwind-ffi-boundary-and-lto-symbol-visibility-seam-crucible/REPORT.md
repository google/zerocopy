# Cross-Language Rust ↔ C++17 / C17 `C-unwind` FFI, `i128` SysV ABI, and ThinLTO Symbol Visibility Seam Crucible

## Summary

`Basis: execution + source + normative + derived`

Verifying a mixed Rust and C/C++ program end-to-end cannot treat foreign-function boundaries as opaque scalar calls, because runtime soundness depends simultaneously on **five cross-language contracts spanning MIR `AbortUnwindingCalls`, LLVM `nounwind`/`uwtable` attribute emission, Itanium two-step exception unwinding, RFC 3435 `i128`/`__int128` data layout and GPR-pair spilling, and ELF `.dynsym` / `--version-script` LTO internalization**. By auditing `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `rust-lang/llvm-project` (`08c84e69a84d95936296dfcab0e38b34100725d5`), `llvm/llvm-project` (`35990504507d79e0b9deb809c8ee5e1b34ceef20`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), executing a live multi-language `rustc 1.98.0-nightly` × `clang 22.1.4` (`-x c++ -std=c++17`) × `gcc 15.2.0` (`-std=c17`) × `rust-lld 22.1.6` execution crucible across `4` compilation profiles (`28` linked-harness runs + `2` uncaught C++ `main()` `staticlib` runs + `7` ELF visibility/linker targets, [probe_cross_lang_ffi_crucible.py](support/probe_cross_lang_ffi_crucible.py)), and mechanizing the full two-language unwinder, ABI layout/spilling model, and LTO visibility semantics in kernel-checked `Lean v4.34.1` ([CrossLangCUnwindAndAbiCrucible.lean](support/CrossLangCUnwindAndAbiCrucible.lean)), we establish six core findings:

1. **Bidirectional `extern "C-unwind"` RAII / `Drop` preservation under `-C panic=unwind`:** Under `ExternAbi::C { unwind: true }` (`"C-unwind"`, `compiler/rustc_abi/src/extern_abi.rs:23-25, 178`), `layout::fn_can_unwind` returns `true` (`compiler/rustc_middle/src/ty/layout.rs:1270`), suppressing LLVM `nounwind` (`compiler/rustc_codegen_llvm/src/abi.rs:441-443, 602-604`) and emitting `personality ptr @rust_eh_personality` with a `.gcc_except_table` LSDA `Cleanup` record. Across native `-O2` and cross-language ThinLTO (`-Clinker-plugin-lto`), a C++ `throw CppEx{42}` unwinding through a Rust `extern "C-unwind"` function executes `RustGuard::drop` (`RUST_DROPS=1`, `trace=['cpp_throwing', 'rust_c_unwind_guard_drop', 'cpp_caught_ex']`, `RC=142`, exit `0`), and a Rust `panic!` unwinding through a C++ `-fexceptions` frame executes `CppGuard::~CppGuard()` (`CPP_DTORS=1`, `trace=['rust_panicking_in_c_unwind', 'cpp_raii_guard_dtor', 'rust_caught_panic']`, `CAUGHT=true`, exit `0`).
2. **Foreign-exception `catch_unwind` claiming in step 1 and cleanup-before-abort determinism:** Because `rust_eh_personality_impl` (`library/std/src/sys/personality/gcc.rs:212, 227`) leaves `_exception_class` uninspected during Itanium step 1 (`_UA_SEARCH_PHASE`), any `EHAction::Catch` landing pad (`std::panic::catch_unwind`) returns `_URC_HANDLER_FOUND` for **both** `MOZ\0RUST` and foreign C++ exceptions (`GNUCC++\0`). Consequently, step 2 (`_UA_CLEANUP_PHASE`) unwinds and executes **every intermediate C++ RAII destructor and Rust `Drop`**, installs `catch_unwind`'s catch pad, calls `_Unwind_DeleteException` (`library/panic_unwind/src/gcc.rs:88-90`, running `CppEx::~CppEx`!), and deterministically aborts via `__rust_foreign_exception` (`SIGABRT`, `rc = -6`, `"fatal runtime error: Rust cannot catch foreign exceptions, aborting"`), bypassing every outer C++ `try { ... } catch (...)` handler (`trace=['cpp_throwing', 'cpp_inner_guard_dtor', 'rust_inner_catch_guard_drop', 'cpp_ex_dtor']`).
3. **Critical `-C panic=abort` `AbortUnwindingCalls` cleanup-vs-filter asymmetry (`Cell 4a/4b` vs. `Cell 4c`):** Under `-C panic=abort`, `layout::fn_can_unwind` returns `false` for all non-foreign Rust definitions regardless of `extern "C-unwind"` (`layout.rs:1247-1249`), while returning `true` for foreign `extern "C-unwind"` declarations. In MIR (`2-2-006.AbortUnwindingCalls`), calls to unwinding FFI functions sit in functions that already have a `bb_cleanup { resume; }` block (`before_has_resume = true`), so `AbortUnwindingCalls` (`abort_unwinding_calls.rs:77-83`) rewrites `resume;` -> `terminate(abi);` inside the cleanup block. Crucially, `rustc_codegen_ssa` (`mir/block.rs:1920-1932`) lowers MIR cleanup blocks to `landingpad { ptr, i32 } cleanup` (`cs_action = 0`, `EHAction::Cleanup`) calling `core::panicking::panic_cannot_unwind`, **not** `filter [0 x ptr] zeroinitializer` (`EHAction::Filter`, `ttype_index = -1`). Therefore:
   - When an outer handler exists on the stack (Rust `std::rt::lang_start` `catch_unwind` or an enclosing C++ `try/catch`, **Cells 4a & 4b**), step 1 finds the outer handler, step 2 enters the Rust `cleanup` pad, **runs `RustGuard::drop` when present** (`trace=['cpp_throwing', 'rust_c_unwind_guard_drop']`), and aborts inside `panic_cannot_unwind` (`rc = -6`).
   - When **C++ `main()` with NO enclosing `try/catch`** calls a `-C panic=abort` Rust `staticlib` `extern "C-unwind"` function (**Cell 4c**), `rust_eh_personality_impl` (`gcc.rs:226`) returns `_URC_CONTINUE_UNWIND` on `EHAction::Cleanup`, `_Unwind_RaiseException` hits `_URC_END_OF_STACK`, and **`__cxa_throw` triggers `std::terminate()` in step 1 without executing `StaticlibGuard::drop` or `panic_cannot_unwind`** (`rc = -6`, `trace=['cpp_throwing_bare']`).
4. **`extern "C"` `nounwind uwtable` silent drop-skipping UB vs. `-C force-unwind-tables=no` (`Cell 5` vs. `Cell 6`):** Because Linux GNU targets set `default_uwtable: true` (`compiler/rustc_target/src/spec/base/linux.rs:17`), `Session::must_emit_unwind_tables()` (`session.rs:805-810`) emits `uwtable(async)` even on `nounwind` `extern "C"` functions under `-C panic=abort`. In **Cell 5**, `AbortUnwindingCalls` (`abort_unwinding_calls.rs:116-122`) rewrites `extern "C"` calls to `unwind unreachable` and deletes the entire Rust cleanup block (`before_bb_count = 3 -> after_bb_count = 1`), leaving a valid `.eh_frame` FDE (`has_fde = true`) with `personality = null` and `lsda = null`. A C++ `throw` across that frame walks right past it using CIE CFI, returning `RC=142` (`exit 0`) with **`RUST_DROPS=0`** (silent destructor-elision UB). Passing `-C force-unwind-tables=no` with `-C panic=abort` (**Cell 6**) clears `uwtable`, removes the FDE (`has_fde = false`), and turns the same C++ throw into deterministic `std::terminate()` (`rc = -6`, `RUST_DROPS=0`).
5. **SysV x86-64 `i128` (`__int128`) layout, 5-GPR straddle spilling, ELF `.dynsym` `--version-script`, and Cross-Language ThinLTO inlining:** Under RFC 3435 (`i128:128` in `x86_64_unknown_linux_gnu.rs:34`), `rustc 1.98.0-nightly`, `clang 22.1.4`, and `gcc 15.2.0` agree bit-for-bit on `sizeof(u128) = 16`, `alignof(u128) = 16`, `Pair48` (`size=48, align=16, offsets=[0, 16, 32]`), `Mixed64` (`size=64, align=16, offsets=[0, 16, 32, 48]`), unaligned GPR pairs (`%dil, %rsi:%rdx, %rcx:%r8`), and the **5-GPR straddle boundary** (`cpp_spill_5gpr_128` / `gcc_spill_5gpr_128`: `g0..g4` occupy `%rdi..%r8`, `stack_val: u128` spills wholly to `0x8(%rsp)`/`0x10(%rsp)`, and `r9_tail: u64` still occupies `%r9`). On ELF visibility, `-Z default-visibility=hidden` flips `.rlib` `SymbolExportLevel::Rust` items to `STV_HIDDEN` while preserving `SymbolExportLevel::C` (`#[unsafe(no_mangle)]` / `#[unsafe(export_name = ...)]`) at `STV_DEFAULT` (`partitioning.rs:949-956`), and `rustc --crate-type=cdylib`'s `--version-script` (`linker.rs:877-895`) demotes even `STV_DEFAULT` C/C++ `.o` symbols to `LOCAL` in `.symtab` (`2` `.dynsym` globals vs. `25` in `clang -shared`), enabling `-Clinker-plugin-lto` + `clang -flto=thin` via `rust-lld` to inline `cpp_thinlto_leaf_mul_add128` into `rust_call_cpp_thinlto_leaf` (`0` `call` instructions!) and strip it completely from `.symtab`.
6. **Zero-`sorry`, zero-`Classical.choice`, zero-`._unsafe_rec` `Lean v4.34.1` formalization & Anneal TCB gap:** [CrossLangCUnwindAndAbiCrucible.lean](support/CrossLangCUnwindAndAbiCrucible.lean) (`764` lines, `486` `.olean` constants, `196` theorems, `unsafe_recs=0`, `non_safe=0`, verified in `6.562s` / `523.47 MiB` max RSS with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` and `0` `Classical.choice`/`sorryAx`/`Lean.ofReduceBool`) proves general bidirectional `C-unwind` drop preservation, `catch_unwind` foreign-exception abort containment, `-C panic=abort` containment vs. uncaught C++ `main` `_URC_END_OF_STACK`, `uwtable` drop-skipping UB (`ce1`), pre-RFC-3435 `8`-byte `i128` mismatch (`ce2`), 5-GPR spill `%r9` preservation, and `cdylib` LTO internalization soundness. At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` supports `IntWidth.i128` (`MirAst.lean:154-170`) and syntactic `UnwindAction` (`MirAst.lean:693-697`), but lacks `ExternAbi`, `UnwindTerminateReason`, and `#[repr(C)]` `i128` layout semantics, and `Trusted.MirSemantics.evalTerminator` (`MirSemantics.lean:1543-1569`) rejects `.call`, `.unwindResume`, `Drop`, `UnwindTerminate`, and `cleanup = true` returns with `.fault .unsupported`.

---

## Applicability

`Basis: source + execution`

**Examined subjects and relationships:**

- **`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `x86_64-unknown-linux-gnu`):** Primary Rust compiler executed for all `.rlib`, `cdylib`, `staticlib`, `bin`, `--emit=llvm-ir`, `-Z dump-mir=AbortUnwindingCalls`, and `--print=link-args` artifacts, as well as the pinned primary-source tree for every `compiler/` and `library/` citation.
- **`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`):** Secondary cross-check reference baseline from prior empirical `C-unwind` and `Pair48` ABI capture (`Pair48` `size=48, align=16`; `panic_unwind_O2`, `panic_abort_O2`, and `panic_abort_no_uwtable_O2` matching identically on Cells 1–6).
- **`rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5` (`LLVM / LLD 22.1.6`) & `llvm/llvm-project@35990504507d79e0b9deb809c8ee5e1b34ceef20` (`clang 22.1.4`):** Bundled `rustc` codegen/ThinLTO linker (`rust-lld`) paired with `clang 22.1.4` (`-x c++ -std=c++17 -fexceptions`, plus `-flto=thin` producing LLVM 22.1 bitcode objects consumed directly by `rustc -Clinker-plugin-lto`).
- **`GNU gcc 15.2.0` (`-std=c17 -O2 -fexceptions`), `GNU libstdc++.so.6.0.35`, & `GNU readelf 2.47`:** Host C17 `__int128` / visibility cross-check compiler, Itanium C++ personality/exception runtime (`__gxx_personality_v0`, `__cxa_throw`, `std::terminate`), and ELF `.dynsym`/`.symtab` inspector.
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`Lean v4.34.1`) & `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:** Kernel checker for [CrossLangCUnwindAndAbiCrucible.lean](support/CrossLangCUnwindAndAbiCrucible.lean) and audited MIR/semantics TCB reference.

**Target & configuration scope:**

- Unwinding execution probes ran natively on `x86_64-unknown-linux-gnu` ELF64 (`panic_unwind_O2`, `panic_abort_O2`, `panic_abort_no_uwtable_O2`, `panic_unwind_xlang_thinlto_O2`, and C++ `main()` `staticlib` under `-C opt-level=2 -C panic=abort`).
- Register assignments (`%rdi..%r9`, `%rax:%rdx`, `0x8(%rsp)`/`0x10(%rsp)`), ELF visibility (`STV_DEFAULT`, `STV_HIDDEN`), and GNU `--version-script` semantics apply to `x86_64-unknown-linux-gnu` ELF64; Section 4 of Findings contrasts `rustc_target::callconv::aarch64` AAPCS64 `Reg::i128()` by source inspection only.

---

## Findings

### 1. Upstream `ExternAbi`, `fn_can_unwind`, `AbortUnwindingCalls`, and `uwtable` Emission

`Basis: source + normative`

Direct inspection of `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` traces the complete compiler pipeline from syntactic ABI parsing through MIR lowering and LLVM attribute emission:

1. **`ExternAbi::C { unwind: bool }` and `fn_can_unwind`:**
   - `compiler/rustc_abi/src/extern_abi.rs:23-25, 177-178, 368` defines `ExternAbi::C { unwind: bool }` mapping `"C"` to `C { unwind: false }` (`ExternAbi::FALLBACK`) and `"C-unwind"` to `C { unwind: true }` (alongside `System`, `Aapcs`, `Cdecl`, `Stdcall`, `Fastcall`, `Thiscall`, `Vectorcall`, `SysV64`, and `Win64` `-unwind` variants).
   - `compiler/rustc_middle/src/ty/layout.rs:1236-1297` computes `fn_can_unwind(tcx, fn_def_id, abi)`:
     * Lines `1239-1241`: `CodegenFnAttrFlags::NEVER_UNWIND` (`#[rustc_nounwind]`) forces `false`.
     * Lines `1247-1249`: **`if !tcx.sess.panic_strategy().unwinds() && !tcx.is_foreign_item(did) { return false; }`** — under `-C panic=abort`, *every* Rust-defined function (even `pub extern "C-unwind" fn`) has `can_unwind = false`, whereas an `unsafe extern "C-unwind"` foreign declaration (`tcx.is_foreign_item(did) == true`) falls through to lines `1270-1279` and returns **`unwind = true`**!
     * Lines `1295`: rustic ABIs (`Rust | RustCall | RustCold | RustPreserveNone`) return `tcx.sess.panic_strategy().unwinds()`.
   - `compiler/rustc_ty_utils/src/abi.rs:601-606` sets `FnAbi::can_unwind` using `fn_can_unwind(tcx, determined_fn_def_id, sig.abi())`.
2. **MIR `AbortUnwindingCalls` pass (`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:26-144`):**
   - Computes `body_can_unwind = layout::fn_can_unwind(tcx, Some(def_id), body_abi)` (line `61`) and iterates over every basic block:
     * Lines `77-83`: If `bb.terminator` is `TerminatorKind::UnwindResume` and `!body_can_unwind` (on targets supporting unwinding), rewrites it to **`TerminatorKind::UnwindTerminate(UnwindTerminateReason::Abi)`**.
     * Lines `89-114`: Determines `call_can_unwind` for `Call` (using callee `DefId` + ABI via `fn_can_unwind`), `Drop`, `Assert`, `FalseUnwind`, and `InlineAsm`.
     * Lines `116-122`: If `!call_can_unwind` (e.g. calling `extern "C"` inside any function), rewrites the terminator's `unwind` edge to **`UnwindAction::Unreachable`** and runs `super::simplify::remove_dead_blocks(body)` (line `138`), **deleting all cleanup blocks and `Drop` calls reachable only via that edge**.
     * Lines `123-134`: If `call_can_unwind && !body_can_unwind` and the edge is `UnwindAction::Continue`, rewrites it directly to **`UnwindAction::Terminate(UnwindTerminateReason::Abi)`**; whereas edges carrying `UnwindAction::Cleanup(bb)` retain cleanup execution and terminate afterwards at `bb`'s `UnwindResume -> UnwindTerminate(Abi)` replacement.
3. **LLVM `NoUnwind`, `uwtable`, and the `cleanup_landing_pad` vs. `filter_landing_pad` Split:**
   - `compiler/rustc_codegen_llvm/src/abi.rs:441-443, 602-604` pushes `llvm::AttributeKind::NoUnwind` onto **both** the function definition (`apply_attrs_llfn`) and every callsite (`apply_attrs_callsite`) whenever `!self.can_unwind`.
   - `compiler/rustc_codegen_llvm/src/attributes.rs:164-172, 434-436` emits `uwtable` (`CreateUWTableAttr(llcx, async_unwind)`) whenever `sess.must_emit_unwind_tables()` (`compiler/rustc_session/src/session.rs:776-811`): `self.target.requires_uwtable || self.opts.cg.force_unwind_tables.unwrap_or(self.panic_strategy().unwinds() || self.target.default_uwtable)`. On `x86_64-unknown-linux-gnu`, `compiler/rustc_target/src/spec/base/linux.rs:17` sets `default_uwtable: true` (`requires_uwtable` defaults to `false` in `compiler/rustc_target/src/spec/mod.rs:2905`), so `-C panic=abort` STILL emits `uwtable(async)` and ELF `.eh_frame` FDEs unless overridden with `-C force-unwind-tables=no`. `compiler/rustc_codegen_llvm/src/context.rs:315-332` also sets the LLVM `"uwtable"` module flag (`UWTableKind::Async = 2`).
   - Crucially, `compiler/rustc_codegen_ssa/src/mir/block.rs:1910-1932` (`landing_pad_for_uncached`) emits **`cleanup_landing_pad(llpersonality)`** (`landingpad { ptr, i32 } cleanup`, yielding `cs_action = 0` = `EHAction::Cleanup` in `.gcc_except_table`) for every MIR `UnwindAction::Cleanup(bb)`, whereas `block.rs:1945-2103` (`terminate_block`) emits **`filter_landing_pad(llpersonality)`** (`landingpad { ptr, i32 } filter [0 x ptr] zeroinitializer`, yielding `ttype_index = -1` = `EHAction::Filter`) **only** when `UnwindAction::Terminate(reason)` sits directly on a call or drop edge. Both lower `UnwindTerminateReason::Abi` to `core::panicking::panic_cannot_unwind` (`library/core/src/panicking.rs:335-338`, `"panic in a function that cannot unwind"`) and `UnwindTerminateReason::InCleanup` to `core::panicking::panic_in_cleanup` (`library/core/src/panicking.rs:351-354`).

---

### 2. Itanium Two-Step Personality Interop & Empirical 6-Cell (+ 4b / 4c / ThinLTO) Crucible

`Basis: source + execution + normative`

#### Why `catch_unwind` Aborts on Foreign Exceptions While Running Cleanup Destructors

In `library/std/src/sys/personality/gcc.rs:209-249`, `rust_eh_personality_impl` inspects `find_eh_action(context)` (`gcc.rs:323-339`, subtracting `1` from `ip` when `ip_before_instr == 0`) **without reading `_exception_class`** (line `212`):

- In `_UA_SEARCH_PHASE` (`actions & _UA_SEARCH_PHASE != 0`, lines `224-229`):
  * `EHAction::None | EHAction::Cleanup(_) => _URC_CONTINUE_UNWIND`
  * `EHAction::Catch(_) | EHAction::Filter(_) => _URC_HANDLER_FOUND`
- In `_UA_CLEANUP_PHASE` (`lines 230-247`):
  * Installs `UNWIND_DATA_REG.0 = exception_object` (`%rax`), `UNWIND_DATA_REG.1 = null` (`%rdx`), and `IP = lpad` (`_URC_INSTALL_CONTEXT`) for `Cleanup`, `Catch`, and `Filter` (skipping `Filter` only under `_UA_FORCE_UNWIND`, line `234`).

Once `catch_unwind` (`library/std/src/panicking.rs:500-700`) claims an exception in step 1 and enters its `do_catch` landing pad, it invokes `__rust_panic_cleanup(payload)` -> `panic_unwind::imp::cleanup` (`library/panic_unwind/src/gcc.rs:85-108`):

```rust
// library/panic_unwind/src/gcc.rs:88-103 (rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)
const RUST_EXCEPTION_CLASS: uw::_Unwind_Exception_Class = u64::from_ne_bytes(*b"MOZ\0RUST");
if (*exception).exception_class != RUST_EXCEPTION_CLASS {
    uw::_Unwind_DeleteException(exception);
    super::__rust_foreign_exception(); // rtabort!("Rust cannot catch foreign exceptions")
}
let canary = (&raw const (*exception).canary).read();
if !ptr::eq(canary, &CANARY) {
    super::__rust_foreign_exception(); // Foreign std copy: skip _Unwind_DeleteException
}
```

#### Empirical MIR, LLVM IR, ELF64 FDE/LSDA, and Execution Results

Running [probe_cross_lang_ffi_crucible.py](support/probe_cross_lang_ffi_crucible.py) across `4` linked profiles of [rust_ffi_harness.rs](support/specimens/rust_ffi_harness.rs) + [ffi_bridge.cpp](support/specimens/ffi_bridge.cpp) + [ffi_c17_abi.c](support/specimens/ffi_c17_abi.c) (`576` FDEs in `panic_unwind_O2`, `571` in `panic_abort_O2`, `557` in `panic_abort_no_uwtable_O2`, `575` in `panic_unwind_xlang_thinlto_O2`) plus the uncaught C++ `main()` staticlib binary ([cpp_main_nocatch.cpp](support/specimens/cpp_main_nocatch.cpp) + [rust_staticlib_abort.rs](support/specimens/rust_staticlib_abort.rs), `2,205` FDEs) establishes every cell empirically via unbuffered POSIX `write(2)` destructor tracing (`FFI_TRACE`):

| Crucible Cell & Scenario | Profile(s) | Rust Frame IR / FDE / LSDA | Exit Code (`rc`) | Exact `write(2)` `[TRACE]` Order | Observed Output / Abort Diagnostic |
| :--- | :--- | :--- | ---: | :--- | :--- |
| **Cell 1**: C++ `throw` -> Rust `extern "C-unwind"` (`RustGuard`) -> C++ `catch` | `panic_unwind_O2`, `xlang_thinlto_O2` | No `nounwind`, `uwtable`, FDE `[0x16780, 0x16814)` (`rust_eh_personality`), LSDA `cleanup` | **`0`** | `cpp_throwing` -> **`rust_c_unwind_guard_drop`** -> `cpp_caught_ex` | `RC=142 RUST_DROPS=1` |
| **Cell 2**: Rust `panic!` -> C++ RAII (`CppGuard`) -> Rust `catch_unwind` | `panic_unwind_O2`, `xlang_thinlto_O2` | `cpp_raii_then_rust_panic`: FDE `[0x54d10, 0x54d94)` (`__gxx_personality_v0`), LSDA `cleanup` (`cs_start=24, lpad=105`) + `catch` (`cs_start=33`) | **`0`** | `rust_panicking_in_c_unwind` -> **`cpp_raii_guard_dtor`** -> `rust_caught_panic` | `CAUGHT=true CPP_DTORS=1` |
| **Cell 3**: Outer C++ `try` -> Rust `catch_unwind` (`RustGuard`) -> C++ (`CppGuard`) -> `throw CppEx{77}` | `panic_unwind_O2`, `xlang_thinlto_O2` | `rust_catch_cpp_throw_inner`: FDE (`rust_eh_personality`), LSDA `catch` (`ttype=1`) + `filter_terminate` (`ttype=-1`) | **`-6`** (`SIGABRT`) | `cpp_throwing` -> **`cpp_inner_guard_dtor`** -> **`rust_inner_catch_guard_drop`** -> **`cpp_ex_dtor`** | `fatal runtime error: Rust cannot catch foreign exceptions, aborting` (outer C++ `catch` bypassed) |
| **Cell 4a**: `-C panic=abort` Rust `extern "C-unwind"` (no `Drop`) -> C++ `throw` under Rust `main` / C++ `try` | `panic_abort_O2`, `panic_abort_no_uwtable_O2` | `nounwind`, MIR `bb1 (cleanup): terminate(abi);`, LLVM `landingpad cleanup` -> `panic_cannot_unwind`, FDE `has_fde=true`, LSDA `cleanup` (`cs_action=0`) | **`-6`** (`SIGABRT`) | `cpp_throwing` | `panic in a function that cannot unwind` / `thread caused non-unwinding panic. aborting.` |
| **Cell 4b**: `-C panic=abort` Rust `extern "C-unwind"` (`RustGuard`) -> C++ `throw` under Rust `main` / C++ `try` | `panic_abort_O2`, `panic_abort_no_uwtable_O2` | Same `landingpad cleanup` -> **`drop_glue::<RustGuard>`** -> `panic_cannot_unwind` | **`-6`** (`SIGABRT`) | `cpp_throwing` -> **`rust_c_unwind_guard_drop`** | `RustGuard` runs before `panic in a function that cannot unwind` aborts |
| **Cell 4c**: `-C panic=abort` Rust `staticlib` `extern "C-unwind"` (`StaticlibGuard` / no guard) called from **uncaught C++ `main()`** | `staticlib` `-O2 -C panic=abort` | Both FDEs present (`0x14d70`, `0x14d80`), LSDA `cleanup` (`cs_action=0`, NO `filter`!) | **`-6`** (`SIGABRT`) | `cpp_throwing_bare` (**`staticlib_guard_drop` NOT run!**) | `terminate called after throwing an instance of 'BareCppEx'` (hits `_URC_END_OF_STACK` in step 1) |
| **Cell 5**: C++ `throw` across Rust `extern "C"` (`RustGuard`) WITH default `uwtable` | `panic_unwind_O2`, `panic_abort_O2`, `xlang_thinlto_O2` | `nounwind uwtable`, MIR `unwind unreachable` (`3 -> 1` BBs, `Drop` deleted), FDE **`has_fde=true`**, `personality=null`, `lsda=null` | **`0`** | `cpp_throwing` -> `cpp_caught_ex` (**`rust_nounwind_guard_drop` skipped!**) | `RC=142 RUST_DROPS=0` (**silent frame-skipping UB**) |
| **Cell 6**: C++ `throw` across Rust `extern "C"` (`RustGuard`) with `-C force-unwind-tables=no` | `panic_abort_no_uwtable_O2` | `nounwind` (no `uwtable`), FDE **`has_fde=false`** (`rust_extern_c_nounwind_with_guard` omitted from `.eh_frame`) | **`-6`** (`SIGABRT`) | `cpp_throwing` | `terminate called after throwing an instance of 'CppEx'` (`RUST_DROPS=0`) |

Look at the exact MIR and LLVM IR evidence behind Cells 4a/4b/4c and Cell 5:

- Under `-C panic=abort`, `rust_c_unwind_with_guard.2-2-006.AbortUnwindingCalls.after.mir` transforms `bb2 (cleanup): { resume; }` into `bb2 (cleanup): { terminate(abi); }` while keeping `bb1 (cleanup): { drop(_2) -> [return: bb2, unwind terminate(cleanup)]; }`, so LLVM emits:
  ```llvm
  cleanup:                                          ; preds = %start
    %2 = landingpad { ptr, i32 }
            cleanup
    call fastcc void @_RINv...drop_glue...RustGuard...(ptr %_g)
    tail call void @_RNv...core9panicking19panic_cannot_unwind()
    unreachable
  ```
- Under `Cell 5` (`rust_extern_c_nounwind_with_guard`), `AbortUnwindingCalls` collapses `3` basic blocks down to `1` (`bb0: { _4 = cpp_throw_code_nounwind(...) -> unwind unreachable; }`), emitting `tail call void @cpp_throw_code(...)` with `nounwind uwtable` (`panic_unwind_O2` attribute `#7`) and `lsda = null`.

---

### 3. SysV x86-64 `i128`/`u128` (`__int128`) Alignment, Register Allocation, and 5-GPR Spilling

`Basis: source + execution + normative`

1. **RFC 3435 `i128:128` Data Layout (`compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:34`):**
   - `rustc`'s `x86_64-unknown-linux-gnu` target specifies `"i64:64-i128:128-f80:128-n8:16:32:64-S128"`, unifying Rust `i128`/`u128` ABI alignment (`16` bytes) with System V AMD64 / Clang / GCC `__int128`.
   - Across `rustc 1.98.0-nightly`, `clang 22.1.4` (`-x c++ -std=c++17`), and `gcc 15.2.0` (`-std=c17`), all three compilers emit identical layout coordinates and pass runtime checks (`MATCH=true`):
     * `u128` / `i128`: `size = 16`, `align = 16`.
     * `#[repr(C)] struct Pair48 { tag: u8, big: u128, tail: u64 }`: `size = 48`, `align = 16`, `offsets = [0, 16, 32]`.
     * `#[repr(C)] struct Mixed64 { a: u8, u: u128, b: u32, s: i128 }`: `size = 64`, `align = 16`, `offsets = [0, 16, 32, 48]`.
   - Under pre-RFC-3435 `8`-byte `i128` alignment, `Pair48` shrinks to `(size=32, align=8, offsets=[0, 8, 24])` and `Mixed64` to `(size=48, align=8, offsets=[0, 8, 24, 32])`, causing silent stack/struct corruption across FFI boundaries (mechanized in Theorem `ce2_pre_rfc3435_8byte_i128_align_abi_mismatch`).
2. **SysV x86-64 Unaligned GPR Pairs vs. 5-GPR Straddle Stack-Spill Boundary (`compiler/rustc_target/src/callconv/x86_64.rs:84-96, 200-252`):**
   - In `x86_64::classify_arg`, a `128`-bit integer scalar spans two eightbytes `Class::Int` (`needed_int = 2`, `needed_sse = 0`). Crucially, SysV AMD64 does **not** require even-numbered GPR alignment (unlike AAPCS64 `compiler/rustc_target/src/callconv/aarch64.rs:149-155`, which checks `align.bits() == 128` and passes aggregates via `Reg::i128()`, and which aligns scalar 128-bit parameters to even-numbered `X` register pairs).
   - Disassembly of `cpp_unaligned_gpr_128(u8 tag, u128 a, i128 b)` (`clang 22.1.4`) and `gcc_unaligned_gpr_128` (`gcc 15.2.0`) directly confirms `%dil` (`tag`), `%rsi:%rdx` (`a` in registers `1:2`!), and `%rcx:%r8` (`b` in registers `3:4`!), returning in `%rax:%rdx`.
   - When `5` scalar integer arguments occupy `%rdi, %rsi, %rdx, %rcx, %r8` (`int_regs = 1` remaining), passing `stack_val: u128` triggers `int_regs.checked_sub(2) == None` (`x86_64.rs:210`). Because SysV AMD64 forbids splitting a `128`-bit scalar across `%r9` and the stack, **`stack_val` spills wholly onto the 16-byte-aligned stack slot (`0x8(%rsp)` / `0x10(%rsp)`), leaving `%r9` available for the subsequent `r9_tail: u64` argument**:
     ```asm
     ; clang 22.1.4 cpp_spill_5gpr_128 (ffi_bridge.o +0x340):
     340: 4c 89 c0        movq %r8, %rax
     343: 4c 8b 44 24 10  movq 0x10(%rsp), %r8   ; stack_val hi64 at +16(%rsp)
     ...
     351: 4c 31 c8        xorq %r9, %rax         ; r9_tail STILL in %r9!
     357: 48 03 44 24 08  addq 0x8(%rsp), %rax   ; stack_val lo64 at +8(%rsp)
     ```
     Both `SPILL_CPP_OK=true` (`clang 22.1.4`) and `SPILL_GCC_OK=true` (`gcc 15.2.0`) execute identically when invoked from `rustc 1.98.0-nightly`.

---

### 4. Symbol Visibility (`STV_DEFAULT` vs. `STV_HIDDEN`), `--version-script`, `-C default-linker-libraries`, and Cross-Language ThinLTO

`Basis: source + execution`

Inspecting `symbol_export.rs:520-546`, `partitioning.rs:872-957`, `session.rs:570-576`, `linker.rs:804-899`, and `link.rs:2850-2853` together with `readelf --dyn-syms -W` / `readelf -sW` / `llvm-objdump -d` across `7` build targets reveals three interacting linker/LTO visibility gates:

| Target Artifact | `rust_exported_c_unwind_api` (`#[unsafe(no_mangle)]`) | `rust_mangled_pub_api` (`pub fn`) | `cpp_vis_default_fn` (`visibility("default")`) | `cpp_vis_hidden_fn` (`visibility("hidden")`) | `cpp_thinlto_leaf_mul_add128` | `.dynsym` Defined Globals |
| :--- | :--- | :--- | :--- | :--- | :--- | ---: |
| `prelink_cpp_obj` (`ffi_bridge.o`) | *(absent)* | *(absent)* | `.symtab`: `GLOBAL DEFAULT` | `.symtab`: `GLOBAL HIDDEN` | `.symtab`: `GLOBAL DEFAULT` | `0` |
| `prelink_c17_obj` (`ffi_c17_abi.o`) | *(absent)* | *(absent)* | `gcc_vis_default_fn`: `GLOBAL DEFAULT` | `gcc_vis_hidden_fn`: `GLOBAL HIDDEN` | *(absent)* | `0` |
| `clang -shared` (`libcxx_baseline.so`) | *(absent)* | *(absent)* | **`.dynsym`: `GLOBAL DEFAULT`** | `.symtab`: `LOCAL HIDDEN` (not in `.dynsym`) | **`.dynsym`: `GLOBAL DEFAULT`** | `25` |
| `rustc --crate-type=rlib` (default vis) | `.symtab`: `GLOBAL DEFAULT` | `.symtab`: **`GLOBAL DEFAULT`** | *(external)* | *(external)* | *(external)* | `0` |
| `rustc --crate-type=rlib -Z default-visibility=hidden` | `.symtab`: **`GLOBAL DEFAULT`** (`SymbolExportLevel::C`) | `.symtab`: **`GLOBAL HIDDEN`** (`SymbolExportLevel::Rust`) | *(external)* | *(external)* | *(external)* | `0` |
| `rustc --crate-type=cdylib` (default & `-Z default-visibility=hidden`) | **`.dynsym`: `GLOBAL DEFAULT`** | `.symtab`: **`LOCAL DEFAULT`** (not in `.dynsym`) | `.symtab`: **`LOCAL DEFAULT`** (**demoted by version script!**) | `.symtab`: `LOCAL HIDDEN` (not in `.dynsym`) | `.symtab`: `LOCAL DEFAULT` (called via GOT/PLT) | **`2`** |
| `rustc --crate-type=cdylib -C linker-plugin-lto` + `clang -flto=thin` | **`.dynsym`: `GLOBAL DEFAULT`** | `.symtab`: `LOCAL DEFAULT` | `.symtab`: `LOCAL DEFAULT` | `.symtab`: `LOCAL HIDDEN` | **Dead-stripped (`dynsym=null, symtab=null`) & inlined!** | **`2`** |

Four concrete mechanisms govern this table:

1. **`SymbolExportLevel::C` immune to `-Z default-visibility=hidden` (`partitioning.rs:949-956`):** Because `CodegenFnAttrs::contains_extern_indicator()` (`codegen_fn_attrs.rs:249-266`) returns `true` for `NO_MANGLE`, `symbol_name.is_some()` (`#[unsafe(export_name = ...)]`), and non-`Internal` `Linkage`, `symbol_export_level` (`symbol_export.rs:532-543`) assigns `SymbolExportLevel::C`. `default_visibility` (`partitioning.rs:952`) therefore forces `Visibility::Default` (`STV_DEFAULT`) even when `-Z default-visibility=hidden` flips `rust_mangled_pub_api` (`SymbolExportLevel::Rust`, line `955`) to `STV_HIDDEN` inside the `.rlib` object.
2. **`cdylib` `--version-script` localizes linked C/C++ `STV_DEFAULT` objects (`linker.rs:877-899`):** For `CrateType::Cdylib`, `crates_export_threshold` (`symbol_export.rs:30-46`) equals `SymbolExportLevel::C`, and `GccLinker::export_symbols` writes `{ global: rust_exported_c_unwind_api; rust_custom_export_api; local: *; };` passed via `--version-script=... --no-undefined-version`. Thus `cpp_vis_default_fn` (which leaked into `.dynsym` under `clang -shared`) is forced to `BIND = LOCAL` in `cdylib` (`2` total `.dynsym` globals vs. `25`). For executables (`--crate-type=bin`), `export_symbols` returns early at `linker.rs:804-812` (`rust_c_unwind_with_guard` absent from `.dynsym`), unless `-Z export-executable-symbols` passes `--dynamic-list` (`linker.rs:862-875`, putting `rust_c_unwind_with_guard` into `.dynsym` as `GLOBAL DEFAULT`).
3. **Cross-language ThinLTO inlining & internalization (`rustc -C linker-plugin-lto` + `clang -flto=thin`):** Compiling `ffi_bridge.cpp` with `clang 22.1.4 -O2 -flto=thin` emits LLVM bitcode consumed directly by `rustc 1.98.0-nightly -C opt-level=2 -C linker-plugin-lto` (`rust-lld 22.1.6`). Disassembly of `rust_call_cpp_thinlto_leaf` (`harness`) and `rust_custom_export_api` (`librust_cdylib_thinlto.so`) proves complete cross-language inlining:
   - Without ThinLTO (`panic_unwind_O2`): `rust_call_cpp_thinlto_leaf` (`17` B) executes `callq *0x41b21(%rip)` (`rust_custom_export_api` in `cdylib` executes `callq *0x3aee2(%rip)`).
   - With cross-language ThinLTO (`panic_unwind_xlang_thinlto_O2` and `librust_cdylib_thinlto.so`): **zero `call` instructions remain** (`43` B straight-line `mulq`/`leaq`/`xorq $0x55aa`/`addq`/`adcq` in `harness`; `15` B `leaq`/`xorq $0x55aa`/`addq` in `cdylib`), `THINLTO_SUM=21981` executes identically, and `cpp_thinlto_leaf_mul_add128` is internalized and completely eliminated from both `.dynsym` and `.symtab` (`null` / `null`)! Note that LLVM IR bitcode cross-linking requires matching LLVM major versions (here LLVM `22.1.4` bitcode read by LLD `22.1.6`).
4. **`-C default-linker-libraries=no` (`link.rs:2850-2853`):** Because `TargetOptions::no_default_libraries` defaults to `true` (`spec/mod.rs:2860`), `rustc --print=link-args` passes `-nodefaultlibs` when `-C default-linker-libraries` is omitted (`has_nodefaultlibs=true`), requiring explicit linkage of `libstdc++.so.6` (`-C link-arg=...` or `-lstdc++`) for C++ exception symbols (`__gxx_personality_v0`, `__cxa_throw`); passing `-C default-linker-libraries=yes` removes `-nodefaultlibs` (`has_nodefaultlibs=false`).

---

### 5. Kernel-Checked `Lean v4.34.1` Formalization & Anneal TCB Audit

`Basis: execution (Lean kernel) + source + derived`

[CrossLangCUnwindAndAbiCrucible.lean](support/CrossLangCUnwindAndAbiCrucible.lean) (`764` source lines, `36,786` B) encodes all list iterations via `List.foldr` and compiles under synchronous kernel typechecking (`lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) in `6.562s` (`523.47 MiB` max RSS) producing `1,564,792` B `.olean` containing `486` total constants (`235` definitions, `196` theorems, `11` inductives, **`0` `._unsafe_rec`**, **`0` `non_safe`**, **`0` `sorryAx`**, **`0` `Classical.choice`**, **`0` `Quot.sound`**, **`0` `omega`**, **`0` `Lean.ofReduceBool`**):

- **General Quantified Unwinding Theorems:**
  * `bidirectional_c_unwind_raii_drop_preservation` (`[propext]`): For arbitrary well-typed `C-unwind` / C++ `.cleanupOnly` `inner` stacks above a matching catcher, `runCrossLangUnwind` returns `.caught` with `expectedChainDrops inner ++ catchDrops` and `[]` skipped drops.
  * `catch_unwind_foreign_cpp_aborts_after_intermediate_drops` (`[propext]`) & `catch_unwind_foreign_rust_canary_aborts_without_delete` (`[propext]`): Throwing `.foreignCpp` or foreign-canary `.rustPanic` into `catch_unwind` executes all intermediate C++ and Rust drops, deletes C++ exceptions (`deletedCppEx = true`), skips deletion for foreign Rust `CANARY` mismatches (`deletedCppEx = false`), and aborts with `.abortedForeignException` without reaching `outer`.
  * `panic_abort_filter_pad_containment` (`[propext]`), `panic_abort_cleanup_pad_containment_when_outer_handles` (`[propext]`), & `panic_abort_cleanup_pad_end_of_stack_when_uncaught` (`[propext]`): Separates unconditional `EHAction::Filter` abort pads from `AbortUnwindingCalls`'s `EHAction::Cleanup` pad (aborts with `RustGuard` drops under outer handler, hits `.terminatedEndOfStack` under uncaught C++ `main()`).
  * `extern_c_with_uwtable_skips_drops_silently` (`[propext]`): Proves `noLandingPadWithUwtable` preserves unwind continuation while accumulating non-empty `ubSkippedDrops`.
- **ABI, Visibility & Sharpness Counterexamples:**
  * `ce1_extern_c_with_uwtable_skips_rust_drop_ub` (`0` axioms): Contrasts Cell 1, Cell 5 (`ubSkippedDrops = ["rust_nounwind_guard_drop"]`), Cell 6 (`.terminatedEndOfStack`), and Cell 4c (uncaught C++ `main()` `.terminatedEndOfStack`).
  * `rfc3435_rust_cpp_layout_parity` (`0` axioms) & `ce2_pre_rfc3435_8byte_i128_align_abi_mismatch` (`0` axioms): Proves `layoutReprC 16 = layoutCppInt128` for all field lists, while `layoutReprC 8` shifts `Pair48` to `(size=32, align=8, offsets=[0, 8, 24])` and `Mixed64` to `(size=48, align=8, offsets=[0, 8, 24, 32])`.
  * `sysv_5gpr_i128_spill_preserves_r9_for_trailing_u64` (`0` axioms) & `i128_reg_pair_marshal_roundtrip` (`[propext]`): Proves 5-GPR straddle spills `arg5: u128` to `stackSlot 0 16 16` while placing `arg6: u64` in `%r9` (`gpr1 5`), plus `(lo + hi * 2^64) % 2^64 = lo` and `/ 2^64 = hi`.
  * `rlib_z_hidden_preserves_c_export_default_and_hides_rust` (`0` axioms), `cdylib_version_script_localizes_linked_cxx_and_enables_thinlto_internalization` (`0` axioms), `lto_internalization_iff_not_dynsym_exported` (`0` axioms), and `live_six_cell_and_abi_crucible_witness` (`0` axioms).

**`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` TCB Boundary Audit:**

In `trusted/lean/Trusted/MirAst.lean:153-175, 693-697, 782-795` and `trusted/lean/Trusted/MirSemantics.lean:1543-1569`:
- `IntWidth.i128` (`16` B, `128` bits) is supported for intra-crate integer arithmetic, and `UnwindAction` models `.continue_ | .unreachable | .terminate | .cleanup block`.
- However, `MirAst.TerminatorKind.call` records no `ExternAbi` (cannot distinguish `"C"` vs. `"C-unwind"` vs. `"Rust"`), `Drop` and `UnwindTerminate` collapse into `TerminatorKind.unsupported`, `UnwindAction.terminate` drops `UnwindTerminateReason::{Abi, InCleanup}`, `evalTerminator` faults `.unsupported` on `.call`, `.unwindResume`, `.assert`, `.unsupported`, and `cleanup = true` returns, and `MirAst` lacks `#[repr(C)]` `i128` field-alignment or ELF visibility attributes. Soundly extending Anneal across FFI therefore requires carrying `ExternAbi`, `PanicStrategy`, `UnwindTerminateReason`, and `default_uwtable` flags into call-boundary obligations and verifying `16`-byte `i128` struct padding parity.

#### Quantitative & Validation Scorecard

| Dimension | Measured Value / Structural Guarantee | Basis |
| :--- | :--- | :--- |
| **Authoring Effort & Artifact Footprint** | [probe_cross_lang_ffi_crucible.py](support/probe_cross_lang_ffi_crucible.py): `1,177` lines (`42,728` B); [CrossLangCUnwindAndAbiCrucible.lean](support/CrossLangCUnwindAndAbiCrucible.lean): `764` lines (`36,786` B); `6` C/C++/Rust specimens (`636` lines total, `21,402` B) | Source inspection (`wc`) |
| **Toolchain Verification Time & Footprint** | Lean `v4.34.1` synchronous kernel check: `6.562s`, `523.47 MiB` max RSS (`1,564,792` B `.olean`); full Python probe (`4` harness profiles + `2` `staticlib` C++ `main` modes + `7` visibility targets + ELF DWARF + disasm): `~9s`, `83,530` B JSON output | Execution (`lean`, `rustc`, `clang`, `gcc`, `readelf`) |
| **Lean TCB & Axiom Audit** | `486` `.olean` constants (`235` defs, `196` thms, `11` inducts): `0` `sorryAx`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`, `0` `._unsafe_rec`, `0` `non_safe` (`[]` or `[propext]` only) | Execution (`lean` + `.olean` audit) |
| **Negative & Sharpness Witnesses** | `ce1` (Cell 5 `uwtable` drop-skip vs. Cell 6 missing FDE `std::terminate` vs. Cell 4c uncaught C++ `main` `staticlib`), `ce2` (`8`-byte pre-RFC-3435 `i128` padding shift), plus live `SIGABRT (-6)` and silent `RUST_DROPS=0` native executions | Execution (Lean kernel + OS exits) |
| **Cross-Compiler & Linker Coverage** | `rustc 1.98.0-nightly` (cross-checked against `1.102.0-nightly`), `clang 22.1.4` C++17 (native + `-flto=thin`), `gcc 15.2.0` C17, `rust-lld 22.1.6` (`-Clinker-plugin-lto`), `GNU readelf 2.47` | Execution |

---

## Boundaries

`Basis: source + execution`

- **Non-`x86_64` ABI (`aarch64` AAPCS64 even-odd `Reg::i128()`, Windows MSVC SEH, `i686`):** `not examined` dynamically on target hardware. Source inspection (`compiler/rustc_target/src/callconv/aarch64.rs:149-155`) shows AAPCS64 uses `Reg::i128()` when `align.bits() == 128`, whereas SysV x86-64 (`x86_64.rs:200-224`) uses two contiguous `Class::Int` eightbytes without even-register alignment; Windows SEH / Wasm EH lowering paths in `block.rs:1986-2075` and `gcc.rs:251-282` were not executed.
- **Unconditional `UnwindAction::Continue -> UnwindAction::Terminate(Abi)` (`filter` pad in `-C panic=abort`):** Because `rustc` emits a `bb_cleanup { resume; }` block on every test function we compiled under `-C panic=abort`, `AbortUnwindingCalls` lowered via `abort_unwinding_calls.rs:77-83` (`cleanup` landing pad) rather than `abort_unwinding_calls.rs:123-134` (`filter_landing_pad`). Triggering `filter` directly in `-C panic=abort` (for example via MIR inlining or CFG simplification that turns a call's cleanup block into `Continue` before `AbortUnwindingCalls`) is `not examined` dynamically, though its `filter` behavior is modeled in `abortFilterPad` / `panic_abort_filter_pad_containment`.
- **Same-major vs. mismatched LLVM bitcode versions under `-Clinker-plugin-lto`:** Here `rustc` bundled LLVM `22.1.6` (`rust-lld 22.1.6`) successfully consumed LLVM `22.1.4` bitcode emitted by `clang 22.1.4 -flto=thin`. Cross-major-version bitcode mixing (e.g. Clang 19 with LLVM 22) is `not examined`.
- **Cross-DSO `CANARY` mismatch between two separate Rust `std` dynamic libraries:** `library/panic_unwind/src/gcc.rs:94-103` establishes by source inspection that mismatched `CANARY` addresses call `__rust_foreign_exception()` *without* calling `_Unwind_DeleteException`; dual-`std`-DSO `dlopen` execution is `not examined`, while the semantic distinction (`deletedCppEx = false`) is proved in `catch_unwind_foreign_rust_canary_aborts_without_delete`.
- **Direct verification inside `joshlf/anneal`:** `unsupported` at `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted.MirAst.TerminatorKind.call` omits `ExternAbi` and `Trusted.MirSemantics.evalTerminator` returns `.fault .unsupported` on `.call`, `Drop`, `UnwindTerminate`, and `.unwindResume`).

---

## Evidence

`Basis: source + execution + normative`

1. **Pinned Upstream Primary Sources (`Basis: source`):**
   - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:
     * `compiler/rustc_abi/src/extern_abi.rs:20-25, 177-178, 368` (`ExternAbi::C { unwind: bool }`, `"C"`, `"C-unwind"`, `FALLBACK`).
     * `compiler/rustc_middle/src/ty/layout.rs:1236-1297` (`fn_can_unwind`: `!panic_strategy().unwinds() && !is_foreign_item(did) => false`).
     * `compiler/rustc_ty_utils/src/abi.rs:601-606` (`FnAbi.can_unwind`).
     * `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:26-144` (`UnwindResume -> UnwindTerminate(Abi)`, `!call_can_unwind -> UnwindAction::Unreachable` + `remove_dead_blocks`, `UnwindAction::Continue -> UnwindAction::Terminate(Abi)`).
     * `compiler/rustc_codegen_llvm/src/abi.rs:441-443, 602-604` (`NoUnwind` attribute emission on definitions and callsites).
     * `compiler/rustc_codegen_llvm/src/attributes.rs:164-172, 434-436` & `compiler/rustc_codegen_llvm/src/context.rs:315-332` (`uwtable_attr`, module `"uwtable"` flag) gated by `compiler/rustc_session/src/session.rs:776-811` (`must_emit_unwind_tables`) and `compiler/rustc_target/src/spec/base/linux.rs:17` (`default_uwtable: true`).
     * `compiler/rustc_codegen_ssa/src/mir/block.rs:1910-1932, 1945-2103` (`landing_pad_for_uncached` `cleanup_landing_pad` vs. `terminate_block` `filter_landing_pad`).
     * `library/std/src/sys/personality/gcc.rs:209-249, 323-339` (`rust_eh_personality_impl` ignoring `_exception_class`, `EHAction::Catch` returning `_URC_HANDLER_FOUND`), `library/panic_unwind/src/gcc.rs:48, 85-112` (`MOZ\0RUST`, `CANARY`, `_Unwind_DeleteException`, `__rust_foreign_exception`), `library/std/src/panicking.rs:74-84, 500-700`, and `library/core/src/panicking.rs:335-354` (`panic_cannot_unwind`, `panic_in_cleanup`).
     * `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:34` (`i128:128`), `compiler/rustc_target/src/callconv/x86_64.rs:84-96, 178-265` (SysV eightbyte `Class::Int`, 2-GPR `i128` spill), and `compiler/rustc_target/src/callconv/aarch64.rs:149-155` (`Reg::i128()` on `align.bits() == 128`).
     * `compiler/rustc_codegen_ssa/src/back/symbol_export.rs:29-46, 520-546`, `compiler/rustc_middle/src/middle/codegen_fn_attrs.rs:249-266`, `compiler/rustc_session/src/session.rs:570-576`, `compiler/rustc_monomorphize/src/partitioning.rs:872-957` (`default_visibility`), `compiler/rustc_codegen_ssa/src/back/linker.rs:804-899, 911-933` (`--dynamic-list`, `--version-script`, `linker_plugin_lto`), `compiler/rustc_codegen_ssa/src/back/link.rs:2850-2853` (`-nodefaultlibs`), and `compiler/rustc_codegen_llvm/src/back/lto.rs:196-202`.
   - `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/Trusted/MirAst.lean:153-175, 693-697, 782-795`, `trusted/lean/Trusted/MirSemantics.lean:1543-1569`.
2. **Normative Specifications (`Basis: normative`):**
   - Itanium C++ ABI: Exception Handling (`_Unwind_RaiseException` step 1 search / step 2 cleanup, `_UA_SEARCH_PHASE`, `_UA_CLEANUP_PHASE`, `_URC_HANDLER_FOUND`, `_URC_END_OF_STACK`, `_Unwind_DeleteException`).
   - System V Application Binary Interface — AMD64 Architecture Processor Supplement (16-byte `__int128` alignment and 2-GPR contiguous `INTEGER`-class register allocation without register splitting across stack).
   - Executable and Linking Format (ELF64) symbol visibility (`STV_DEFAULT`, `STV_HIDDEN`) and GNU version scripts.
3. **Preserved Executable Artifacts & Captured Output (`Basis: execution`, observed `2026-11-21`):**
   - Multi-language probe harness: [probe_cross_lang_ffi_crucible.py](support/probe_cross_lang_ffi_crucible.py) (`42,728` B, `1,177` lines, SHA-256 `f9affcc7c38a7af47ebe133ac29d558a07ac5922faa8e9b30a7070b17d583d94`).
   - Preserved C++17, C17, and Rust source specimens under `support/specimens/`:
     * [ffi_bridge.cpp](support/specimens/ffi_bridge.cpp) (`5,502` B, `213` lines, SHA-256 `d214ba95434e12b6eff82b55463ca4d098d4d4fb1283d4ab36296f82b5f22bea`)
     * [ffi_c17_abi.c](support/specimens/ffi_c17_abi.c) (`1,981` B, `76` lines, SHA-256 `4fa6bfadeb6d2ee19df0a9e5ed5f501975e88f55d0a81665ce69296b72b00f0`)
     * [rust_ffi_harness.rs](support/specimens/rust_ffi_harness.rs) (`11,110` B, `304` lines, SHA-256 `a046402de9eaedce8f476ce8d325bbbf9dc6657409813e8ac552941fa73cb393`)
     * [rust_cdylib_vis.rs](support/specimens/rust_cdylib_vis.rs) (`1,026` B, `31` lines, SHA-256 `83e4eada2ff7929a11d95d3e513479a64e56621fff36d1c0ef87b9ecebc82043`)
     * [rust_staticlib_abort.rs](support/specimens/rust_staticlib_abort.rs) (`717` B, `32` lines, SHA-256 `206b94f72ace4c8631414bafbf46e87854d549312b6cff9bdae4d6d1ce13d582`)
     * [cpp_main_nocatch.cpp](support/specimens/cpp_main_nocatch.cpp) (`1,066` B, `31` lines, SHA-256 `01ccfd00a03113e10b4c9336a769aecbccc38f01cd402e948200625dc406946a`)
   - Complete captured MIR, LLVM IR, ELF64 `.eh_frame`/LSDA tables, disassembly, `.dynsym`/`.symtab`, and execution JSON: [cross_lang_ffi_crucible_results.json](support/cross_lang_ffi_crucible_results.json) (`83,530` B, `2,502` lines, SHA-256 `e4fd8f7500fa3c9bddb56a6519808d235546007bf138b8793a939974000e7b02`).
   - Kernel-checked `Lean v4.34.1` formalization: [CrossLangCUnwindAndAbiCrucible.lean](support/CrossLangCUnwindAndAbiCrucible.lean) (`36,786` B, `764` lines, SHA-256 `b8f7b7ea9c052561dfebfaf7c02311127311370475c2eec143255deed8fb83d8`).

---

## Revalidation

`Basis: execution + source`

```bash
# 1. Re-run the full multi-language rustc + clang C++17 + gcc C17 + ThinLTO crucible:
python3 reports/cross-language-c-unwind-ffi-boundary-and-lto-symbol-visibility-seam-crucible/support/probe_cross_lang_ffi_crucible.py \
  --out /tmp/revalidated_cross_lang_ffi_results.json

# 2. Synchronously kernel-check the Lean v4.34.1 formalization and print all theorem axioms:
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  --root reports/cross-language-c-unwind-ffi-boundary-and-lto-symbol-visibility-seam-crucible/support \
  -o /tmp/cross_lang_crucible_check.olean \
  reports/cross-language-c-unwind-ffi-boundary-and-lto-symbol-visibility-seam-crucible/support/CrossLangCUnwindAndAbiCrucible.lean
```

**Fastest discriminating checks after a compiler, personality, or linker upgrade:**

- If `cell3_rust_catch_unwind_on_cpp` changes from `SIGABRT` (`__rust_foreign_exception`) to propagating cleanly into C++ `catch`, inspect `library/std/src/sys/personality/gcc.rs:212, 227` to verify whether `rust_eh_personality_impl` began filtering `_exception_class` against `MOZ\0RUST` during `_UA_SEARCH_PHASE`.
- If `cell4c_cpp_main_nocatch_staticlib_abort` switches from `terminate called` (`RUST_DROPS=0`) to `panic_cannot_unwind` (`staticlib_guard_drop` executing), inspect `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:77-83` and `compiler/rustc_codegen_ssa/src/mir/block.rs:1920-1932` to see whether `UnwindTerminate(Abi)` moved from a MIR `cleanup` landing pad (`cs_action = 0`) to a `filter_landing_pad` (`ttype_index = -1`).
- If `panic_unwind_xlang_thinlto_O2.thinlto_caller_has_call` changes from `false` (`0` `call` instructions) to `true`, inspect LLVM bitcode major-version compatibility between the C++ compiler and `rustc`'s bundled `rust-lld`, or symbol preservation flags in `compiler/rustc_codegen_ssa/src/back/linker.rs:877-933`.
