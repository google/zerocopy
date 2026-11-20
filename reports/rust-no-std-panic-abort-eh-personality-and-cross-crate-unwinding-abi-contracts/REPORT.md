# Rust `no_std` Panic Strategies, `eh_personality`, and Cross-Crate Unwinding ABI Contracts

## Summary

Rust compiles panics and cross-language exceptions under a three-mode panic strategy lattice—`PanicStrategy::Unwind` (`-C panic=unwind`), `PanicStrategy::Abort` (`-C panic=abort`, RFC 1513), and unstable `PanicStrategy::ImmediateAbort` (`-C panic=immediate-abort`)—coupled with the central ABI unwind capability predicate `layout::fn_can_unwind`. Cross-crate linking is asymmetric: `rlib` crates compiled with `-C panic=unwind` link cleanly into final artifacts compiled with `-C panic=abort` (dormant landing pads remain sound when Rust panics abort), whereas linking a `-C panic=abort` `rlib` into a `-C panic=unwind` artifact is rejected by `rustc_metadata::dependency_format::verify_ok` (`RequiredPanicStrategy`), and `ImmediateAbort` or `-Z panic-in-drop` requires strict equality across every linked crate in the dependency graph.

In `#![no_std]` builds, `core::panicking` routes panics to `#[panic_handler]` (`#[lang = "panic_impl"] fn(&PanicInfo<'_>) -> !`, RFC 2070) via two entrypoints: unwinding-capable `panic_fmt` (`can_unwind = true`) and `#[rustc_nounwind] panic_nounwind_fmt` (`can_unwind = false`). Compiler precondition checks (`panic_misaligned_pointer_dereference`, `panic_null_pointer_dereference`, `panic_invalid_enum_construction`), ABI nounwind traps (`panic_cannot_unwind`), and cleanup double-panic traps (`panic_in_cleanup`) invoke `panic_nounwind_fmt`: if a defective `#[panic_handler]` ignores `PanicInfo::can_unwind()` and unwinds anyway, `#[rustc_nounwind]` intercepts the unwind and aborts. Under `-C panic=immediate-abort`, `core::panicking` bypasses `panic_impl` completely and inlines `core::intrinsics::abort_immediate()`.

Across Foreign Function Interface (FFI) boundaries (RFC 2945), `extern "C"` and `extern "C-unwind"` share identical register/stack calling conventions while differing strictly in `ExternAbi` unwind permission:
1. **Rust-defined `extern "C" fn` panicking (`-C panic=unwind`):** `AbortUnwindingCalls` rewrites escaping unwind edges to `UnwindAction::Terminate(UnwindTerminateReason::Abi)`, running local Rust destructors first and then calling `panic_cannot_unwind` to abort deterministically rather than causing Undefined Behavior.
2. **Foreign code unwinding into Rust via `extern "C"`:** `rustc` emits LLVM `nounwind` on foreign `extern "C"` declarations and call sites without a landing pad (`unwind unreachable` in `PostCleanup` MIR); an unforced C++ `throw` crossing `extern "C"` into Rust is immediate Undefined Behavior under both `panic=unwind` and `panic=abort`.
3. **Foreign code unwinding into Rust via `extern "C-unwind"`:** Under `-C panic=unwind`, Rust runs local drop glue and rethrows via `UnwindResume` (`resume`). Under `-C panic=abort`, `AbortUnwindingCalls` preserves local drop glue along the foreign `C-unwind` cleanup edge before terminating via `terminate(abi)` (`panic_cannot_unwind`), while eliding all drop glue along Rust-originated `panic!` and normal `Drop` paths.
4. **Latent `#![no_std]` link hazard under `-C panic=abort`:** Because `rustc_middle::middle::lang_items::required` exempts `LangItem::EhPersonality` under `PanicStrategy::Abort`, `#![no_std]` crates without `eh_personality` pass frontend checks even when calling `extern "C-unwind"` functions or `asm!(..., options(may_unwind))`; however, `rustc_codegen_ssa` emits an LLVM `landingpad` referencing external `rust_eh_personality` (`DW.ref.rust_eh_personality`), failing at bare-metal link time with `undefined symbol: rust_eh_personality` unless an `eh_personality` symbol is supplied.

Finally, `core::panic::{UnwindSafe, RefUnwindSafe, AssertUnwindSafe}` are safe advisory types that cannot be relied upon for memory safety by `unsafe` code. At the runtime ABI boundary, `panic_unwind` tags Rust exceptions with `RUST_EXCEPTION_CLASS` (`"MOZ\0RUST"`) plus a per-DSO `static CANARY: u8` address, aborting via `__rust_foreign_exception` if `catch_unwind` intercepts either a C++ exception or a Rust panic thrown by a distinct dynamically linked copy of `std`.

## Applicability

This report covers four upstream subjects recorded in `REPORT.json`:
- **`rust-lang/rust` at `560abf7946ae41fd210edac5dfe829d7eff86eec`:** Primary source inspected for `rustc_abi::extern_abi`, `rustc_middle::{ty::layout::fn_can_unwind, middle::lang_items}`, `rustc_mir_transform::abort_unwinding_calls`, `rustc_metadata::{creader, dependency_format}`, `rustc_codegen_ssa::mir::block`, `core::{panicking, panic::unwind_safe}`, `panic_unwind`, `panic_abort`, and `std::sys::personality::gcc`.
- **`rustc` `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`):** Executed compiler used to verify `PostCleanup` MIR (`--emit=mir`), LLVM IR (`--emit=llvm-ir`), cross-crate `rlib` diagnostics, and `#![no_std]` `rust-lld` symbol resolution.
- **`rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`:** Specifications in RFC 1513, RFC 2070, and RFC 2945.
- **`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:** Normative rules in `src/abi.md`, `src/panic.md`, `src/runtime.md`, and `src/destructors.md`.

Scope boundaries: `-C panic=unwind`, `-C panic=abort`, `#[panic_handler]`, `extern "C"`, `extern "C-unwind"` (Rust 1.71+), abort-on-unwind in `extern "C"` exports (Rust 1.81+), and `AssertUnwindSafe` / `catch_unwind` apply to stable Rust. `-C panic=immediate-abort` and `-Z panic-in-drop={unwind,abort}` require nightly `-Z unstable-options` (plus `-Z build-std` for `core` under `immediate-abort`). Low-level DWARF CFI bytecode encoding and 32-bit Windows SEH frame chains are covered in sibling packages `unwinding-on-elf-and-macho-targets`, `unwinding-on-windows-targets-and-32bit-seh`, `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`, and `rust-panic-divergence-and-unreachable-semantics`.

## Findings

### 1. Three-Mode Panic Strategy Lattice and Asymmetric Cross-Crate Linking Contracts

`Basis: normative + source + execution`

`rustc_target::spec::PanicStrategy` defines three modes whose runtime injection (`compiler/rustc_metadata/src/creader.rs:1089-1181`) and DAG validation (`compiler/rustc_metadata/src/dependency_format.rs:409-508`) form an asymmetric compatibility lattice:

| Final Artifact Strategy | Injected `#![panic_runtime]` | Required Lang Items (`lang_items::required`) | Upstream `rlib` (`unwind`) | Upstream `rlib` (`abort`) | Upstream `rlib` (`immediate-abort`) |
| --- | --- | --- | --- | --- | --- |
| `PanicStrategy::Unwind` | `panic_unwind` | `panic_impl` + `eh_personality` | Compatible | **Rejected** (`RequiredPanicStrategy`) | **Rejected** (`IncompatibleWithImmediateAbort`) |
| `PanicStrategy::Abort` | `panic_abort` | `panic_impl` (`EhPersonality` exempted) | **Compatible** (landing pads dormant) | Compatible | **Rejected** (`IncompatibleWithImmediateAbort`) |
| `PanicStrategy::ImmediateAbort` | None (`inject_panic_runtime` returns early) | None (`required` returns `false`) | **Rejected** (`IncompatibleWithImmediateAbort[Core]`) | **Rejected** (`IncompatibleWithImmediateAbort[Core]`) | Compatible (must match entire DAG including `core`) |

Four rules govern cross-crate composition:
1. **Deferred `rlib` runtime binding:** Compiling `--crate-type=rlib` alone (outside `#![needs_panic_runtime]` on `std`) skips runtime injection (`creader.rs:1093-1097`). Both `panic_unwind` and `panic_abort` can coexist conditionally (`CrateDepKind::Conditional`, `lines 1153-1160`) until `dependency_format::calculate_type` activates one for a linked output (`Executable`, `Dylib`, `Cdylib`, `StaticLib`, `ProcMacro`).
2. **Asymmetric `unwind` -> `abort` compatibility:** Non-runtime `rlib`s compiled with `-C panic=unwind` record `required_panic_strategy() == None`, allowing prebuilt `unwind` sysroot `libcore.rlib` and `liballoc.rlib` to link into `-C panic=abort` binaries (`dependency_format.rs:476-493`). Conversely, `-C panic=abort` `rlib`s record `Some(PanicStrategy::Abort)` because cleanup landing pads were stripped and Rust functions carry LLVM `nounwind`; linking into `-C panic=unwind` fails with `error: the crate 'dep' requires panic strategy 'abort' which is incompatible with this crate's strategy of 'unwind'`.
3. **Strict `-Z panic-in-drop` equality:** `tcx.panic_in_drop_strategy(cnum)` must match `sess.opts.unstable_opts.panic_in_drop` across every linked upstream crate except `compiler_builtins` (`dependency_format.rs:495-505`, `IncompatiblePanicInDropStrategy`).
4. **Unique panic runtime:** `verify_ok` (`lines 446-474`) rejects multiple `#![panic_runtime]` crates (`TwoPanicRuntimes`) or strategy mismatches (`BadPanicStrategy`).

### 2. `no_std` `#[panic_handler]` Contracts, Nounwind Guards, and `eh_personality` Link Traps

`Basis: normative + source + execution`

In `#![no_std]` crates, `library/core/src/panicking.rs:67-70, 108-111` declares `#[lang = "panic_impl"] fn panic_impl(pi: &PanicInfo<'_>) -> !` (RFC 2070 `text/2070-panic-implementation.md:91-95`).
1. **Divergence (`!`) contract:** Safe Rust forces `#[panic_handler]` to diverge (`loop {}`, hardware reset, or `intrinsics::abort()`). If broken `unsafe` code returns from `panic_impl`, callers in `core::panicking` execute LLVM `unreachable`, causing immediate Undefined Behavior.
2. **Split `panic_fmt` (`can_unwind = true`) vs `#[rustc_nounwind] panic_nounwind_fmt` (`can_unwind = false`):**
   - User `panic!`, `assert!`, `panic_bounds_check`, and arithmetic `panic_const_*` call `panic_fmt` (`panicking.rs:60-81`) with `can_unwind = true`.
   - Precondition/UB checks (`panic_misaligned_pointer_dereference`, `panic_null_pointer_dereference`, `panic_null_reference_constructed`, `panic_invalid_enum_construction` at `lines 280-338`), `panic_cannot_unwind` (`lines 349-354`), and `panic_in_cleanup` (`lines 365-370`) call `#[rustc_nounwind] panic_nounwind_fmt` (`lines 92-125`) with `can_unwind = false`. If a custom `#![no_std]` `#[panic_handler]` ignores `pi.can_unwind() == false` and unwinds anyway, `#[rustc_nounwind]` traps the unwind at `panic_nounwind_fmt`'s `UnwindTerminate(Abi)` guard (`lines 89-92`).
3. **`ImmediateAbort` short-circuit:** Under `-C panic=immediate-abort`, `panic_fmt`, `panic_nounwind_fmt`, and `panic_bounds_check` inline `super::intrinsics::abort_immediate()` (`lines 61-63, 102-104`), dropping formatting strings, caller locations, and `panic_impl` references.

#### `eh_personality` Dispatch and the `#![no_std]` `-C panic=abort` Link Trap

On ELF/Mach-O/MinGW targets (`library/std/src/sys/personality/gcc.rs:96-359`), `#[lang = "eh_personality"]` (`rust_eh_personality`) decodes LSDA tables (`find_eh_action`) across the unwinder's search and cleanup steps:
- During search (`_UA_SEARCH_PHASE` / `_US_VIRTUAL_UNWIND_FRAME`), `EHAction::None | Cleanup(_)` continues unwinding, `Catch(_) | Filter(_)` reports `_URC_HANDLER_FOUND`, and `EHAction::Terminate` aborts via `_URC_FATAL_PHASE1_ERROR` (`gcc.rs:257-262`).
- During cleanup, it loads exception registers (`RAX`/`RDX` on `x86_64`, `X0`/`X1` on `aarch64`, `x10`/`x11` on `riscv64`, `lines 54-90`), signs landing-pad pointers via `pacib` on `aarch64` `pauthtest` (`lines 212-238`), and installs the landing pad (`_URC_INSTALL_CONTEXT`), while letting `_UA_FORCE_UNWIND` bypass `EHAction::Filter(_)` (`lines 267-269`).

`compiler/rustc_middle/src/middle/lang_items.rs:128-136` exempts `LangItem::EhPersonality` when `PanicStrategy::Abort` is active (`lang_item != LangItem::EhPersonality`). Consequently:
- `#![no_std]` with `-C panic=unwind` fails in the frontend (`error: unwinding panics are not supported without std`).
- **`#![no_std]` with `-C panic=abort` + `extern "C-unwind"` link trap:** When a `#![no_std]` crate under `-C panic=abort` calls any `extern "C-unwind"` function or `asm!(..., options(may_unwind))`, frontend lang-item validation passes, yet `AbortUnwindingCalls` + `rustc_codegen_ssa` (`block.rs:2226, 2383`) emit an LLVM `landingpad` referencing external `declare i32 @rust_eh_personality(...)` (`DW.ref.rust_eh_personality` in `.eh_frame`). `--crate-type=rlib`/`staticlib` succeeds silently, and bare-metal final linking (`-nostdlib`) fails with `rust-lld: error: undefined symbol: rust_eh_personality`.

### 3. `extern "C"` vs `extern "C-unwind"` FFI Boundaries and Plain Old Frames (RFC 2945)

`Basis: normative + source + execution`

`compiler/rustc_abi/src/extern_abi.rs:180-222` pairs foreign ABIs with explicit `unwind: bool` flags (`C`, `System`, `SysV64`, `Win64`, `Aapcs`, `Cdecl`, `Stdcall`, `Fastcall`, `Vectorcall`, `Thiscall`) without subtyping or coercion between `"C"` and `"C-unwind"`. `layout::fn_can_unwind` (`compiler/rustc_middle/src/ty/layout.rs:1358-1421`) computes unwind capability in strict priority order:
1. `false` if `fn_def_id == Some(did)` has `CodegenFnAttrFlags::NEVER_UNWIND`;
2. `false` if `!tcx.sess.panic_strategy().unwinds() && !tcx.is_foreign_item(did)` (all Rust-defined functions—even `pub extern "C-unwind" fn`—never unwind under `-C panic=abort`);
3. `false` if `!tcx.sess.opts.unstable_opts.panic_in_drop.unwinds()` and `did` is `LangItem::DropGlue`;
4. For foreign items and indirect `fn` pointers (`fn_def_id == None`), `unwind` for paired foreign ABIs, `false` for interrupt/kernel/EFI/Swift/intrinsic ABIs, and `tcx.sess.panic_strategy().unwinds()` for rustic ABIs (`Rust`, `RustCall`, `RustCold`, `RustPreserveNone`, `RustTail`).

| `-C panic` | ABI | Outbound: Rust `panic!` in Rust FFI Export | Inbound: Unforced Foreign Exception Entering Rust Call | LLVM `nounwind` (Rust Def / Foreign Decl) |
| --- | --- | --- | --- | --- |
| `unwind` | `"C-unwind"` | Runs local drops, **unwinds** into foreign caller (`resume`) | Runs local drops, **continues unwinding** (`resume`) | Omitted / Omitted |
| `unwind` | `"C"` | Runs local drops, **aborts** via `panic_cannot_unwind` | **Immediate UB** (`call` has `#nounwind`, no landing pad) | Emitted / Emitted |
| `abort` | `"C-unwind"` | **Aborts immediately** in `panic_impl` (local drops skipped) | Runs local drops on landing pad, then **aborts** (`panic_cannot_unwind`) | **Emitted** / Omitted |
| `abort` | `"C"` | **Aborts immediately** in `panic_impl` | **Immediate UB** (`call` has `#nounwind`, no landing pad) | Emitted / Emitted |

**Plain Old Frames (POFs) and forced unwinding:** RFC 2945 (`text/2945-c-unwind-abi.md:146-187, 241-252`) defines a POF as a dynamic frame state with no pending `Drop` values and no active `catch_unwind`. Deallocating a non-POF via `longjmp` or forced unwinding (`glibc` `pthread_exit`, Windows SEH `longjmp`) is unconditionally UB. On `terminate` blocks (`block.rs:2289-2387`), MSVC SEH emits `catchpad ... [null, i32 64, null]` (`HT_IsStdDotDot`) and Itanium `rust_eh_personality` ignores `_UA_FORCE_UNWIND` on `Filter` pads so `longjmp`/`pthread_exit` fly over nounwind guards without aborting, whereas Wasm EH `catchpad ... [null]` catches all foreign exceptions.

### 4. `PostCleanup` MIR Drop-Glue Elision and `UnwindAction` Rewriting

`Basis: source + execution`

`AbortUnwindingCalls` (`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:27-147`) runs after `ElaborateDrops`: (1) rewrites `UnwindResume` to `Unreachable` on Wasm without `exception-handling` or `UnwindTerminate(Abi)` when `!body_can_unwind`; (2) sets unwind edges on `!call_can_unwind` terminators to `UnwindAction::Unreachable`; (3) when `call_can_unwind && !body_can_unwind`, rewrites `UnwindAction::Continue` to `UnwindAction::Terminate(Abi)` while keeping `UnwindAction::Cleanup(bb)` (whose tail `UnwindResume` became `UnwindTerminate(Abi)`); and (4) calls `simplify::remove_dead_blocks`.

Empirical `PostCleanup` MIR on `rust_extern_c_unwind_entry` with `_3 = Guard(slot)` (`probe_with_std2.mir` vs `probe_nostd.mir`):

| Edge in `rust_extern_c_unwind_entry` | `-C panic=unwind` `PostCleanup` MIR | `-C panic=abort` `PostCleanup` MIR | `Guard::drop` Executed? |
| --- | --- | --- | --- |
| `panic!(...)` | `panic_fmt(...) -> bb7` (`drop(_3)` -> `resume`) | `panic(...) -> unwind unreachable` | `unwind`: **Yes**; `abort`: **No** (elided) |
| `foreign_c_may_throw()` (`"C"`) | `-> [return: bb4, unwind unreachable]` | `-> [return: bb3, unwind unreachable]` | **UB** if foreign throws |
| `foreign_c_unwind_may_throw()` (`"C-unwind"`) | `-> [return: bb5, unwind: bb7]`; tail `resume` | `-> [return: bb4, unwind: bb6]`; tail `terminate(abi)` | **Yes in both modes** (`abort` drops `_3`, then aborts) |
| Normal exit `drop(_3)` | `drop(_3) -> [return: bb6, unwind continue]` | `drop(_3) -> [return: bb5, unwind unreachable]` | Yes |
| Cleanup `drop(_3)` | `drop(_3) -> [return: bb8, unwind terminate(cleanup)]` | `drop(_3) -> [return: bb7, unwind terminate(cleanup)]` | Double-panic calls `panic_in_cleanup` |

### 5. `UnwindSafe`, `catch_unwind` Isolation, and Multi-Runtime Canary Aborts

`Basis: normative + source + derived`

`library/core/src/panic/unwind_safe.rs:85-201` defines safe `auto trait UnwindSafe` (`!UnwindSafe` for `&mut T`), safe `auto trait RefUnwindSafe` (`!RefUnwindSafe` for `UnsafeCell<T>`), and `pub struct AssertUnwindSafe<T>(pub T)` with a safe public constructor. Because safe callers wrap arbitrary closures in `AssertUnwindSafe` without `unsafe`, **`unsafe` code must never rely on `UnwindSafe` for memory safety** and must restore representation invariants via RAII drop guards along unwind paths.

At runtime, `panic_unwind` (`library/panic_unwind/src/gcc.rs:49-111`) allocates `#[repr(C)] struct Exception { _uwe: _Unwind_Exception, canary: *const u8, cause: Box<dyn Any + Send> }` with `RUST_EXCEPTION_CLASS = u64::from_ne_bytes(*b"MOZ\0RUST")` and `canary: &CANARY`. In `cleanup(ptr)` (`catch_unwind` catch handler):
1. If `(*exception).exception_class != RUST_EXCEPTION_CLASS` (foreign C++ exception), `_Unwind_DeleteException` runs followed by `__rust_foreign_exception() -> !` (process abort).
2. If `!ptr::eq((&raw const (*exception).canary).read(), &CANARY)` (Rust panic from a second dynamically linked `std` instance), `__rust_foreign_exception() -> !` aborts without calling `_Unwind_DeleteException`.
3. If foreign C++ `catch (...)` destroys a Rust `Exception` without rethrowing, `exception_cleanup` calls `__rust_drop_panic() -> !` (process abort).

### 6. Verification Engineering Obligations for Cross-Crate and FFI Soundness

`Basis: derived`

1. **`PostCleanup` MIR under `-C panic=abort`:** Verifiers cannot strip `is_cleanup` blocks or `UnwindTerminate` semantics in `-C panic=abort` mode whenever `extern "C-unwind"` calls, indirect `C-unwind` fn pointers, or `may_unwind` inline assembly exist.
2. **Foreign `extern "C"` precondition:** Every verified call to a foreign `extern "C"` symbol must discharge a caller/link obligation `callee_never_unwinds` (e.g., C++ `noexcept`), matching MIR `UnwindAction::Unreachable` and LLVM `nounwind`.
3. **`#[panic_handler]` proof obligation:** Verified `#![no_std]` panic handlers must prove non-return (`-> !`) and gate any custom unwinder invocation on `pi.can_unwind() == true`.

## Boundaries

- **`not examined`:** 32-bit x86 `fs:[0]` SEH chains, Emscripten JS unwinding (`emcc.rs`), Miri's synthetic unwind tracker (`miri.rs`), and `-Z staticlib-prefer-dynamic` solver heuristics in `dependency_format.rs` were **not examined** (see `unwinding-on-windows-targets-and-32bit-seh` and `unwinding-on-elf-and-macho-targets`).
- **`unknown`:** Future non-UB semantics for `longjmp` / `pthread_exit` forced unwinding across Plain Old Frames and catching foreign exceptions in `catch_unwind` (RFC 2945 `text/2945-c-unwind-abi.md:248-263`) remain **unknown**.
- **`known not to apply`:**
  - Undefined Behavior when a Rust `panic!` reaches a Rust-defined `extern "C" fn` boundary is **known not to apply** in Rust 1.81+ (it deterministically aborts via `panic_cannot_unwind`).
  - Destructor execution along Rust `panic!` paths is **known not to apply** under `-C panic=abort`, whereas local destructors **do** run when a foreign `extern "C-unwind"` exception unwinds into a `-C panic=abort` Rust frame before `terminate(abi)` aborts.
  - Memory-safety guarantees from `UnwindSafe` / `RefUnwindSafe` bounds are **known not to apply**.
- **`unsupported`:**
  - Linking `-C panic=abort` `rlib`s into `-C panic=unwind` targets is **unsupported** (`RequiredPanicStrategy`).
  - Mixing `-C panic=immediate-abort` with standard precompiled `libcore` is **unsupported** (`IncompatibleWithImmediateAbortCore`).
  - Compiling `#![no_std]` targets with `-C panic=unwind` without `std` or nightly lang-item runtimes is **unsupported**.

## Evidence

### Primary Upstream Source Coordinates (`rust-lang/rust` @ `560abf7946ae41fd210edac5dfe829d7eff86eec`)

| Subsystem | File Path | Symbols and Line Ranges |
| --- | --- | --- |
| `ExternAbi` unwind pairs & rustic predicate | `compiler/rustc_abi/src/extern_abi.rs` | `ExternAbi` (`180-222`), `is_rustic_abi` (`300-303`) |
| `fn_can_unwind` decision procedure | `compiler/rustc_middle/src/ty/layout.rs` | `fn_can_unwind` (`1358-1421`) |
| `AbortUnwindingCalls` MIR pass | `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs` | `AbortUnwindingCalls::run_pass` (`27-146`) |
| `UnwindTerminate` landing-pad / SEH / Wasm codegen | `compiler/rustc_codegen_ssa/src/mir/block.rs` | `UnwindTerminate` (`1698-1701`), `cleanup_landing_pad` (`2226-2235`), `terminate_block` (`2248-2415`) |
| `EhPersonality` requirement matrix | `compiler/rustc_middle/src/middle/lang_items.rs` | `required` (`128-136`) |
| Runtime injection & cross-crate strategy checks | `compiler/rustc_metadata/{creader.rs, dependency_format.rs}` | `inject_panic_runtime` (`creader.rs:1089-1181`), `verify_ok` (`dependency_format.rs:409-508`) |
| `panic_fmt`, `panic_nounwind_fmt`, `immediate-abort` | `library/core/src/panicking.rs` | `panic_fmt` (`60-81`), `panic_nounwind_fmt` (`92-125`), `panic_cannot_unwind` (`349-354`), `panic_in_cleanup` (`365-370`) |
| `UnwindSafe`, `RefUnwindSafe`, `AssertUnwindSafe` | `library/core/src/panic/unwind_safe.rs` | `UnwindSafe` (`91`), `RefUnwindSafe` (`109`), `AssertUnwindSafe` (`171-201`) |
| `RUST_EXCEPTION_CLASS`, `CANARY`, foreign abort | `library/panic_unwind/src/{lib.rs, gcc.rs}` | `__rust_panic_cleanup` (`lib.rs:71-92`), `CANARY`, `Exception`, `cleanup` (`gcc.rs:49-111`) |
| `rust_eh_personality` DWARF/ARM/MinGW-SEH & `pacib` | `library/std/src/sys/personality/gcc.rs` | `UNWIND_DATA_REG` (`51-90`), `sign_lpad` (`212-238`), `rust_eh_personality` (`105-208`, `242-356`) |

### Specifications and Peer-Reviewed Literature

- **RFCs (`rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`):** RFC 1513 (`text/1513-less-unwinding.md`), RFC 2070 (`text/2070-panic-implementation.md`), RFC 2945 (`text/2945-c-unwind-abi.md`).
- **The Rust Reference (`rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** `src/abi.md`, `src/panic.md`, `src/runtime.md`, `src/destructors.md`.
- **Papers:** Théophile Bastian, Stephen Kell, and Francesco Zappa Nardelli, *"Reliable and Fast DWARF-Based Stack Unwinding"*, PACMPL Vol. 3, OOPSLA 2019, Article 146, DOI `10.1145/3360572`; Daniel Patterson, Noble Mushtak, Andrew Wagner, and Amal Ahmed, *"Semantic Soundness for Language Interoperability"*, PLDI 2022, DOI `10.1145/3519939.3523703`; Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, and John Regehr, *"Alive2: Bounded Translation Validation for LLVM"*, PLDI 2021, DOI `10.1145/3453483.3454030`; Nick Benton and Andrew Kennedy, *"Exceptional Syntax"*, JFP Vol. 11, No. 4, 2001, DOI `10.1017/S0956796801004099`; Christophe de Dinechin, *"C++ Exception Handling"*, IEEE Concurrency Vol. 8, No. 4, 2000, DOI `10.1109/4434.895109`.

### Reproducible Execution Probes (`2026-11-20`, `rustc 1.98.0-nightly 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`)

1. **`#![no_std]` `-C panic=abort` + `extern "C-unwind"` MIR/LLVM-IR and link trap:** Save `/tmp/probe_nostd.rs`:

```rust
#![no_std]
#![no_main]
unsafe extern "C" { fn foreign_c_may_throw(); }
unsafe extern "C-unwind" { fn foreign_c_unwind_may_throw(); }

pub struct Guard(pub *mut u32);
impl Drop for Guard { fn drop(&mut self) { unsafe { *self.0 += 1; } } }

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    let mut x = 0u32;
    let _g = Guard(&raw mut x);
    unsafe { foreign_c_may_throw(); foreign_c_unwind_may_throw(); }
    loop {}
}

#[panic_handler]
fn on_panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
```

Run:

```bash
rustc --edition=2024 --crate-type=staticlib -C panic=abort --emit=mir,llvm-ir /tmp/probe_nostd.rs -o /tmp/libprobe_nostd.a
rustc --edition=2024 -C panic=abort -C link-arg=-nostdlib /tmp/probe_nostd.rs -o /tmp/probe_nostd_bin
```

`staticlib` exits `0` (emitting `foreign_c_may_throw() -> unwind unreachable`, `foreign_c_unwind_may_throw() -> unwind: bb_cleanup` -> `drop(_g)` -> `terminate(abi)`, and `declare i32 @rust_eh_personality(...)`); bare-metal link (`-nostdlib`) exits `1` with `rust-lld: error: undefined symbol: rust_eh_personality >>> referenced by ...:(DW.ref.rust_eh_personality)`.

2. **Cross-crate `rlib` lattice:**

```bash
printf 'pub fn helper(x: u32) -> u32 { assert!(x > 0); x }\n' > /tmp/dep.rs
printf 'extern crate dep; fn main() { let _ = dep::helper(1); }\n' > /tmp/app.rs
rustc --crate-type=rlib -C panic=abort /tmp/dep.rs -o /tmp/libdep_abort.rlib
rustc --crate-type=rlib -C panic=unwind /tmp/dep.rs -o /tmp/libdep_unwind.rlib
rustc -C panic=unwind --extern dep=/tmp/libdep_abort.rlib /tmp/app.rs -o /tmp/app_fail
rustc -C panic=abort --extern dep=/tmp/libdep_unwind.rlib /tmp/app.rs -o /tmp/app_ok
```

`app_fail` exits `1` (`requires panic strategy 'abort' which is incompatible with this crate's strategy of 'unwind'`); `app_ok` exits `0`.

## Revalidation

1. **CLI probes (< 1 s):** Re-run `/tmp/probe_nostd.rs` and the `dep.rs`/`app.rs` lattice on the target `rustc` to verify `PostCleanup` MIR unwind actions, `rust_eh_personality` link symbol emission under `#![no_std]` + `-C panic=abort`, and asymmetric `rlib` linking.
2. **Targeted source diffs:** Diff `compiler/rustc_middle/src/ty/layout.rs` (`fn_can_unwind`), `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`, `compiler/rustc_middle/src/middle/lang_items.rs` (`required`), and `library/panic_unwind/src/gcc.rs` (`CANARY`, `cleanup`).
