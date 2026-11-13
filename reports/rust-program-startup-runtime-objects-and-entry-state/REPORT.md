# Program Startup Chains, CRT Runtime Objects, Initialization/Teardown, and Process Entry State Across Tier 1 Targets

## Summary

A verified drop-in replacement for `rustc` targeting the 8 Tier 1 platforms must emit the synthetic C entry wrapper, link the appropriate C runtime (`CRT`) and Rust startup objects (`rsbegin.o`/`rsend.o`), and preserve the runtime initialization, teardown, and CPU state contracts summarized below:

1. **Entry Chains Per Target (`compiler/rustc_codegen_ssa/src/base.rs:500-635`, `library/std/src/rt.rs:110-211`, `support/startup_*.s`):**
   - For every binary crate (`--crate-type=bin`) without `#![no_main]`, `maybe_create_entry_wrapper` emits an unmangled C ABI `main` (`_main` on `i686-pc-windows-msvc` and `aarch64-apple-darwin`) with signature `fn(c_int, *const *const u8) -> c_int` (`main_needs_argc_argv: true` on all 8 Tier 1 targets; `compiler/rustc_target/src/spec/mod.rs:2553`).
   - At `-C opt-level=2`, `std::rt::lang_start::<T>` is inlined directly into the generated `main`, which stores the address of the user's mangled Rust `main` (`_RNv...4main`) into an 8-byte (or 4-byte on `i686`) stack slot, pairs it with a 6-word vtable (`drop_in_place`, `size`, `align`, `FnOnce::call_once`, `FnMut::call_mut`, `Fn::call`) wrapping `std::sys::backtrace::__rust_begin_short_backtrace`, and calls `std::rt::lang_start_internal(&main_closure, argc as isize, argv, sigpipe)`.
   - On `x86_64-pc-windows-gnu` (`support/startup_x86_64-pc-windows-gnu.s:126`), LLVM's MinGW target lowering additionally inserts `callq __main` at the start of `main` before invoking `lang_start_internal`, which triggers MinGW `libgcc`'s `__do_global_ctors` (`.ctors` / `.init_array` dispatch).
2. **Pre-`main` Initializers, Runtime Setup, and Teardown (`library/std/src/sys/configure_builtins.rs:33-60`, `sys/args/unix.rs:119-135`, `sys/pal/unix/mod.rs:22-218`, `io/stdio.rs:729-745`, `sys/exit.rs:22-68`):**
   - **Pre-`main` constructor sections:** `std` registers up to two static constructors before `main`:
     1. `RUST_LSE_INIT` (`configure_builtins.rs:33-60`) on `aarch64` when `+outline-atomics` is enabled without compile-time `+lse` (default on `aarch64-unknown-linux-gnu`), placed in `.init_array.90` on ELF, `__DATA,__mod_init_func,mod_init_funcs` on Darwin, and `.CRT$XCT` on Windows to detect hardware LSE via the auxiliary vector and call `__rust_enable_lse()`.
     2. `ARGV_INIT_ARRAY` (`sys/args/unix.rs:119-135`) on `*-unknown-linux-gnu`, placed in `.init_array.00099` so glibc's non-standard `(argc, argv, envp)` `.init_array` invocation populates `ARGC`/`ARGV` even when Rust is linked into a `cdylib` where `lang_start` never runs.
   - **In-`lang_start_internal` initialization (`rt::init`):** Sets the main thread ID (`main_thread::set`), runs `sys::init`:
     - On Unix (`sys/pal/unix/mod.rs:22-50`): sanitizes file descriptors `0..=2` via `poll()` (Linux) or `fcntl(fd, F_GETFD)` (macOS, where `poll` with `events == 0` does not report `POLLNVAL` for closed fds) and opens `/dev/null` on any closed standard stream; configures `SIGPIPE` via `reset_sigpipe(sigpipe)`; initializes guard pages and `sigaltstack` (`stack_overflow::init()`); stores `argc`/`argv`; and on Apple platforms calls `pthread_setname_np("main")`.
     - On Windows (`sys/pal/windows/mod.rs:44-52`): calls `stack_overflow::init()` (`AddVectoredExceptionHandler` + `SetThreadStackGuarantee(0x5000)`) and names the main thread `"main"` via `SetThreadDescription`.
   - **`-Zon-broken-pipe` and `#[unix_sigpipe]`:** The historical `#[unix_sigpipe]` attribute was removed in favor of `-Zon-broken-pipe={default,kill,error,inherit}` (`compiler/rustc_passes/src/entry.rs:98-105`, `compiler/rustc_session/src/config/sigpipe.rs:1-21`), encoded as `u8` (`DEFAULT = 0`, `INHERIT = 1`, `SIG_IGN = 2`, `SIG_DFL = 3`). When `sigpipe == 0` (`DEFAULT`), `std` sets `SIGPIPE` to `SIG_IGN` at startup (`ON_BROKEN_PIPE_USED = false`) and resets `SIGPIPE` to `SIG_DFL` in child processes spawned via `std::process::Command` (`sys/process/unix/unix.rs:364-375, 741-754`); when `-Zon-broken-pipe` is explicitly passed (`1`, `2`, or `3`), `ON_BROKEN_PIPE_USED` is set to `true` and child processes inherit the parent's `SIGPIPE` disposition.
   - **Teardown (`rt::cleanup` and `unique_thread_exit`):** After `main` returns (or catches an unwind and returns `101`), `rt::cleanup()` runs once (`Once::call_once`): `io::cleanup()` replaces `STDOUT`'s `LineWriter` with a zero-capacity `LineWriter::with_capacity(0, stdout_raw())` using `try_lock()` (avoiding deadlock if a `StdoutLock` was leaked), which drops and flushes the previous buffer (`io/stdio.rs:729-745`), and `sys::cleanup()` calls `WSACleanup()` on Windows (`sys/pal/windows/mod.rs:58-60`). On Linux (`sys/exit.rs:22-57`), `unique_thread_exit()` then serializes process exit using `EXITING_THREAD_ID.compare_exchange(null, __errno_location())` to prevent concurrent `libc::exit` races in glibc (`#126600`).
3. **CRT Objects, `rsbegin.o`/`rsend.o`, Crate Types, and `+crt-static` (`compiler/rustc_target/src/spec/crt_objects.rs:1-135`, `rustc_codegen_ssa/src/back/link.rs:2250-2381`, `library/rtstartup/rs{begin,end}.rs`, `library/core/src/ffi/mod.rs:76-83`):**
   - On Linux (`gnu`), macOS, and Windows MSVC, `rustc` invokes the C compiler driver or linker without injecting manual `pre_link_objects`, delegating CRT startup object selection (`Scrt1.o`/`crt1.o`/`rcrt1.o`, `crti.o`, `crtbeginS.o`/`crtbeginT.o`, `crtendS.o`/`crtend.o`, `crtn.o` on Linux; `libSystem.B.dylib` on macOS; `msvcrt.lib` vs. `libcmt.lib` via `.drectve` in `core::ffi` on MSVC) to the linker/driver.
   - On `x86_64-pc-windows-gnu`, self-contained mode (`pre_mingw_self_contained`) injects `crt2.o` (for `bin`) or `dllcrt2.o` (for `dylib`/`cdylib`). Although `bootstrap` still compiles `library/rtstartup/{rsbegin,rsend}.rs` into `rsbegin.o` and `rsend.o` for all `windows-gnu` targets (`src/bootstrap/src/core/build_steps/compile.rs:915-950`), their DWARF `.eh_frame` registration tables (`__EH_FRAME_BEGIN__`, `OBJ`, `P_INIT` in `.ctors.65535` calling `__register_frame_info`, and `__EH_FRAME_END__`) are gated on `#[cfg(all(target_os = "windows", target_arch = "x86", target_env = "gnu"))]` (`i686-pc-windows-gnu`), so on 64-bit `x86_64-pc-windows-gnu` (which uses PE+ `.pdata`/`.xdata` SEH) `rsbegin.o` and `rsend.o` are empty marker objects and are not added to `pre_link_objects`.
4. **Process State Assumed at Entry:** Compiled Rust code assumes ABI-mandated stack alignment (`RSP % 16 == 8` on x86_64 ELF/Mach-O/PE, `SP % 16 == 0` on AArch64, `ESP % 16 == 12` on `i686-unknown-linux-gnu`, `ESP % 4 == 0` on `i686-pc-windows-msvc`), IEEE-754 default round-to-nearest-even floating-point control state with trapped FP exceptions masked (`MXCSR = 0x1F80`, `FPCR = 0`, and x87 `FCW = 0x037F` on Linux/MinGW or `0x027F` 53-bit mantissa on MSVC `i686`), direction flag `DF = 0` on x86/x86_64, and AArch64 `PSTATE.SM = 0` / `PSTATE.ZA = 0` on SME-capable hardware.

## Applicability

These findings apply to `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), its bundled LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) across all 8 Tier 1 targets.

## Findings

### 1. Entry Chains Per Target: From OS Loader to `lang_start_internal` and User `main`

Basis: source + execution

Compiling `support/startup_probe.rs` across all 8 Tier 1 targets (`support/startup_*.s` and `support/startup_x86_64-unknown-linux-gnu.ll`) and tracing `compiler/rustc_codegen_ssa/src/base.rs:500-635` and `library/std/src/rt.rs:152-211` yields the complete entry chain for each target family:

| Target Family | OS Loader Entry Symbol | C Runtime Startup Chain | Compiler-Generated C Entry Wrapper (`create_entry_fn`) | Rust Runtime Entry (`#[lang = "start"]`) | Backtrace & User Entry |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Linux ELF (`x86_64`, `aarch64`, `i686-unknown-linux-gnu`) | `_start` (in `Scrt1.o` for default PIE, `crt1.o` for no-PIE, `rcrt1.o` for `+crt-static` PIE) | `_start` aligns stack to 16 B, extracts `(argc, argv, envp)` from initial stack, calls `__libc_start_main(main, argc, argv, __libc_csu_init/null, __libc_csu_fini/null, rtld_fini, stack_end)` which runs `.preinit_array` and `.init_array` | `main(argc: i32, argv: *const *const u8) -> i32` (`support/startup_x86_64-unknown-linux-gnu.ll:78-89`) | `std::rt::lang_start::<()>` (inlined at `-O2` into `main`, calling `std::rt::lang_start_internal(&closure, argc as isize, argv, sigpipe)`) | `closure` calls `std::sys::backtrace::__rust_begin_short_backtrace(crate::main)` (marked `noinline` with trailing empty inline asm barrier `asm!("", options(preserves_flags, nostack))`), then `.report().to_i32()` |
| macOS Mach-O (`aarch64-apple-darwin`) | `dyld` (`LC_MAIN` load command pointing directly to `_main`; no `crt1.o` on macOS $\ge 10.8$) | `dyld` maps Mach-O segments, initializes `libSystem.B.dylib` (`libSystem_initializer`), runs `__DATA,__mod_init_func` initializers, and calls `_main(argc, argv, envp, apple)` | `_main(argc: i32, argv: *const *const u8) -> i32` (`support/startup_aarch64-apple-darwin.s:86-114`) | `__RNvNtCs..._3std2rt19lang_start_internal` | `__RINvNtNtCs..._3std3sys9backtrace28___rust_begin_short_backtrace...` $\rightarrow$ `__RNvCs..._13startup_probe4main` |
| Windows MSVC (`x86_64`, `aarch64`, `i686-pc-windows-msvc`) | `mainCRTStartup` (or `wmainCRTStartup` / `WinMainCRTStartup` depending on `/SUBSYSTEM`) in `msvcrt.lib` or `libcmt.lib` | `mainCRTStartup` calls `__scrt_common_main_seh`, initializes UCRT/VCRuntime, runs `_initterm(__xi_a, __xi_z)` (C initializers) and `_initterm(__xc_a, __xc_z)` (`.CRT$XCA`..`.CRT$XCZ` C++ initializers including `.CRT$XCT`), and calls `main(argc, argv, envp)` | `main` (`x86_64`/`aarch64`) or `_main` (`i686`, `cdecl`) (`support/startup_*windows-msvc.s`) | `_RNvNtCs..._3std2rt19lang_start_internal` | `___rust_begin_short_backtrace` $\rightarrow$ user `main` (note: Windows `std::env::args_os` ignores `(argc, argv)` and calls `GetCommandLineW()`) |
| Windows MinGW (`x86_64-pc-windows-gnu`) | `mainCRTStartup` in `crt2.o` ( calls `__tmainCRTStartup`) | `__tmainCRTStartup` initializes MinGW CRT, registers SEH handler, and calls `main(argc, argv, envp)`. Inside `main`, LLVM emits `callq __main` (`startup_x86_64-pc-windows-gnu.s:126`), which runs `__do_global_ctors` once (`__initialized`) over `.ctors` / `.init_array` | `main` (`support/startup_x86_64-pc-windows-gnu.s:111-143`, including `callq __main` at line `126` and `.drectve` `-exclude-symbols:` at lines `156-158`) | `_RNvNtCs..._3std2rt19lang_start_internal` | `___rust_begin_short_backtrace` $\rightarrow$ user `main` |

**Exact structure of the compiler-generated `main` and `vtable.0` (`support/startup_x86_64-unknown-linux-gnu.ll:6-89`):**
- `maybe_create_entry_wrapper` (`compiler/rustc_codegen_ssa/src/base.rs:500-605`) looks up `LangItem::Start` (`std::rt::lang_start::<T>`, where `T` is the return type of the user's `main`, typically `()`) and calls `lang_start(rust_main, argc as isize, argv, sigpipe)`.
- Because `lang_start` is generic over `T: Termination + 'static`, `std::rt::lang_start` (`library/std/src/rt.rs:199-211`) immediately delegates to the monomorphic `lang_start_internal(main: &(dyn Fn() -> i32 + Sync + RefUnwindSafe), argc: isize, argv: *const *const u8, sigpipe: u8) -> isize`.
- At `-C opt-level=2`, LLVM inlines `lang_start::<()>` into `main` (`startup_x86_64-unknown-linux-gnu.ll:78-89`):
  ```llvm
  define noundef i32 @main(i32 %0, ptr %1) unnamed_addr #5 {
  top:
    %_7.i = alloca [8 x i8], align 8
    %2 = sext i32 %0 to i64
    call void @llvm.lifetime.start.p0(ptr nonnull %_7.i)
    store ptr @_RNvCslIq7RLtFujA_13startup_probe4main, ptr %_7.i, align 8
    %_0.i = call noundef i64 @_RNvNtCs8ZKwes1zzDd_3std2rt19lang_start_internal(
        ptr noundef nonnull %_7.i,
        ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(48) @vtable.0,
        i64 noundef %2, ptr noundef %1, i8 noundef 0)
    call void @llvm.lifetime.end.p0(ptr nonnull %_7.i)
    %3 = trunc i64 %_0.i to i32
    ret i32 %3
  }
  ```
- Why `__rust_begin_short_backtrace` contains an empty `asm!("")` (`startup_x86_64-unknown-linux-gnu.ll:22-29`): Marked `#[inline(never)]`, it calls `f()` followed by `tail call void asm sideeffect "", "~{memory}"()` (`#APP` / `#NO_APP` in `startup_*.s`) to prevent tail-call elimination so the return address of `__rust_begin_short_backtrace` remains on the call stack as the sentinel frame where `RUST_BACKTRACE=1` stops printing frames.

### 2. Initialization and Teardown: `.init_array` / `.CRT$XCT`, `SIGPIPE`, `atexit`, TLS Destructors, and `stdout` Flushing

Basis: source + execution

1. **Static initializers emitted by `std` before `main`:**
   - **`RUST_LSE_INIT` (`library/std/src/sys/configure_builtins.rs:33-60`):** Compiled when `all(target_arch = "aarch64", target_feature = "outline-atomics", not(target_feature = "lse"), not(feature = "compiler-builtins-c"))`—which holds by default on `aarch64-unknown-linux-gnu` (`features: "+v8a,+outline-atomics"` in `tier1_target_specs_1991.txt:36`), whereas `aarch64-apple-darwin` (`cpu: "apple-m1"`, which implies `+lse`) and `aarch64-pc-windows-msvc` (`features: "+v8a,+neon"`, no `+outline-atomics`) do not require it. On ELF, `RUST_LSE_INIT` is placed in `.init_array.90` (priority `90`, inside the implementation-reserved `0..=100` priority range) and calls `__rust_enable_lse()` if `is_aarch64_feature_detected!("lse")` succeeds.
   - **`ARGV_INIT_ARRAY` (`library/std/src/sys/args/unix.rs:119-135`):** Compiled on `all(target_os = "linux", target_env = "gnu")` (`x86_64`, `aarch64`, and `i686-unknown-linux-gnu`) in section `.init_array.00099` (priority `99`, running right after `.init_array.90`). It stores `(argc, argv)` into `ARGC` and `ARGV` (`AtomicIsize` / `AtomicPtr`) using `Ordering::Relaxed`. When running as a normal executable, `sys::args::init(argc, argv)` inside `rt::init` writes `ARGC`/`ARGV` a second time (to support emulators like QEMU user-mode or custom loaders that do not pass `argc`/`argv` to `.init_array`; `unix.rs:112-114`). On macOS (`sys/args/unix.rs:153-190`), no initializer is needed because `std::env::args` queries `_NSGetArgc()` and `_NSGetArgv()` dynamically from `libSystem`.
   - **Windows `.CRT$XCT` initializers (`library/std/src/sys/pal/windows/compat.rs:40-44`):** On `target_vendor = "win7"`, `INIT_TABLE_ENTRY` is placed in `.CRT$XCT` (which runs before user `.CRT$XCU` initializers) to preload `WaitOnAddress`/`WakeByAddressSingle`. On the Tier 1 `pc` vendor targets (`Windows 10+`), `WaitOnAddress` is linked directly against `api-ms-win-core-synch-l1-2-0.dll` without a `.CRT$XCT` initializer.
   - **Codegen `.init_array` configuration (`compiler/rustc_codegen_llvm/src/back/write.rs:230, 297`, `compiler/rustc_target/src/spec/mod.rs:2676-2677`):** `use_ctors_section` defaults to `false` on all Tier 1 targets, so LLVM's `TargetOptions::UseInitArray` is enabled (`true`) across all ELF targets.
2. **Standard file descriptor sanitization (`library/std/src/sys/pal/unix/mod.rs:51-139`):**
   - On Linux (`x86_64`, `aarch64`, `i686`), `sanitize_standard_fds()` executes a single `libc::poll(&mut [pollfd(0), pollfd(1), pollfd(2)], 3, 0)` system call and checks `pfd.revents & libc::POLLNVAL != 0`, falling back to `fcntl(fd, F_GETFD)` only if `poll` fails with `EINVAL`/`EAGAIN`/`ENOMEM`.
   - On macOS (`aarch64-apple-darwin`, `unix/mod.rs:86-87, 123-138`), Darwin's `poll()` does not set `POLLNVAL` when `events == 0`, so `sanitize_standard_fds()` skips `poll()` and executes three `libc::fcntl(fd, libc::F_GETFD)` calls for `fd in 0..3`, opening `/dev/null` (`O_RDWR`) if any returns `-1` with `EBADF` (and calling `libc::abort()` if `/dev/null` cannot be opened).
3. **`SIGPIPE` disposition (`-Zon-broken-pipe` vs. removed `#[unix_sigpipe]`):**
   - `compiler/rustc_passes/src/entry.rs:98-105` maps `-Zon-broken-pipe` (`OnBrokenPipe`) to the 4th parameter (`sigpipe: u8`) of `lang_start`:
     - Default (`OnBrokenPipe::Default` $\rightarrow$ `sigpipe::DEFAULT = 0`): `reset_sigpipe` (`sys/pal/unix/mod.rs:167-180`) calls `libc::signal(SIGPIPE, SIG_IGN)` and leaves `ON_BROKEN_PIPE_USED = false`. Later, `std::process::Command` checks `!on_broken_pipe_used()` (`sys/process/unix/unix.rs:364, 741`) and resets `SIGPIPE` to `SIG_DFL` in spawned child processes (either via `POSIX_SPAWN_SETSIGDEF` in `posix_spawn` or `signal(SIGPIPE, SIG_DFL)` after `fork`).
     - `-Zon-broken-pipe=inherit` (`sigpipe::INHERIT = 1`): `reset_sigpipe` stores `ON_BROKEN_PIPE_USED = true` and does *not* call `signal(SIGPIPE, ...)`.
     - `-Zon-broken-pipe=error` (`sigpipe::SIG_IGN = 2`): `reset_sigpipe` stores `ON_BROKEN_PIPE_USED = true` and calls `signal(SIGPIPE, SIG_IGN)`.
     - `-Zon-broken-pipe=kill` (`sigpipe::SIG_DFL = 3`): `reset_sigpipe` stores `ON_BROKEN_PIPE_USED = true` and calls `signal(SIGPIPE, SIG_DFL)`.
4. **Teardown order (`lang_start_internal`, TLS destructors, `stdout` flush, `atexit`):**
   - **Normal return from `main` (`library/std/src/rt.rs:175-193`):**
     1. `main` runs inside `panic::catch_unwind(main)`. If `main` panics and unwinds, the payload is dropped inside a nested `catch_unwind` (aborting via `rtabort!("drop of the panic payload panicked")` on double panic) and `ret_code` is set to `101`.
     2. `rt::cleanup()` runs via `static CLEANUP: Once`:
        - `crate::io::cleanup()` (`library/std/src/io/stdio.rs:729-745`) calls `STDOUT.get_or_init(...)`. If `STDOUT` was never initialized, it initializes it with a zero-capacity `LineWriter::with_capacity(0, stdout_raw())`; if `STDOUT` was already initialized, it calls `stdout.try_lock()` and overwrites `*lock.borrow_mut() = LineWriter::with_capacity(0, stdout_raw())`, which drops the old `LineWriter`, flushing any buffered stdout bytes to fd 1 and disabling future stdout buffering during shutdown! (Note: `STDERR` is unbuffered `StderrRaw`, and `STDIN`'s buffer is discarded without flushing.)
        - `sys::cleanup()` is a no-op on Unix (`sys/pal/unix/mod.rs:217`) and calls `winsock::cleanup()` (`WSACleanup` if Winsock was initialized) on Windows (`sys/pal/windows/mod.rs:58-60`).
     3. `crate::sys::exit::unique_thread_exit()` (`library/std/src/sys/exit.rs:22-68`) executes on Linux (`target_os = "linux"`), recording `crate::sys::io::errno_location()` in `EXITING_THREAD_ID`: if another thread is already exiting, the second thread loops in `libc::pause()`; if the *same* thread calls `std::process::exit` re-entrantly (e.g., from a TLS destructor or `atexit` handler), it aborts with `panic_nounwind("std::process::exit called re-entrantly")`.
     4. `lang_start_internal` returns `ret_code` to C `main`, which returns to `__libc_start_main` / `dyld` / `__scrt_common_main_seh`, which invokes `exit(ret_code)`:
        - **Main-thread TLS destructors** run first (`__call_tls_dtors` in glibc registered via `__cxa_thread_atexit_impl`, `_tlv_exit` in macOS `dyld` registered via `_tlv_atexit`, and `PIMAGE_TLS_CALLBACK` / `.CRT$XLB` `on_tls_callback` on `DLL_PROCESS_DETACH` on Windows). Because `io::cleanup()` already replaced `STDOUT` with a 0-capacity `LineWriter` before `main` returned, any `println!` inside a main-thread TLS destructor or `atexit` handler writes directly to `stdout_raw()` without losing buffered output!
        - **`atexit` and `.fini_array` / `.dtors` handlers** run next (`__run_exit_handlers` on glibc, `__cxa_finalize_ranges` on macOS, `_initterm_e`/`_initterm` on Windows). `std` itself does not register a global `libc::atexit` handler on Tier 1 targets (except on targets without native thread-local destructor support, which none of the 8 Tier 1 targets use).

### 3. Startup Objects, Crate Types (`bin`, `dylib`, `cdylib`, `staticlib`), and `+crt-static`

Basis: source

Tracing `compiler/rustc_codegen_ssa/src/back/link.rs:2250-2381`, `compiler/rustc_target/src/spec/crt_objects.rs:1-135`, `tier1_target_specs_1991.txt`, `src/bootstrap/src/core/build_steps/compile.rs:906-954`, and `library/rtstartup/rs{begin,end}.rs` establishes which startup objects and C runtime libraries are linked for each crate type and `+crt-static` mode:

| Target Triple | `LinkOutputKind` (`bin` default vs. `+crt-static`) | `bin` Startup Objects & CRT Libraries | `dylib` / `cdylib` Startup Objects & Entry | `staticlib` / `rlib` Startup Objects | `rsbegin.o` / `rsend.o` Role |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu` | Default: `DynamicPicExe` (`-pie`).With `+crt-static`: `StaticPicExe` (`-static-pie`, since `static-position-independent-executables: true`). | Delegated to `cc` driver (`gnu-lld-cc`):<br>• `DynamicPicExe`: `Scrt1.o`, `crti.o`, `crtbeginS.o` ... `crtendS.o`, `crtn.o`, `-lc`, `-lm`, `-lpthread`, `-ldl`, `-lrt`<br>• `StaticPicExe` (`+crt-static`): `rcrt1.o`, `crti.o`, `crtbeginS.o` ... `crtendS.o`, `crtn.o`, static `libc.a` | `DynamicDylib` (`crt-static-allows-dylibs: false`, so `+crt-static` is ignored for dylibs!): `crti.o`, `crtbeginS.o` ... `crtendS.o`, `crtn.o` (`-shared`). Initializers in `.init_array` run on `dlopen` / load. | None (`ar` archive of `.rcgu.o` objects; no linker or CRT objects). | None (`!target.is_windows_gnu()`). |
| `aarch64-apple-darwin` | `DynamicPicExe` (`crt-static-respected: false`; macOS does not support static linking of `libSystem`). | `darwin-cc` driver links `-lSystem` (`libSystem.B.dylib`); Mach-O uses `LC_MAIN` (no `crt1.o` on macOS $\ge 11.0$). | `DynamicDylib` (`-dynamiclib`): links `-lSystem`; `__DATA,__mod_init_func` runs on image load. | None (`darwin` `ar` archive). | None. |
| `x86_64-pc-windows-msvc`, `aarch64-pc-windows-msvc`, `i686-pc-windows-msvc` | Default: `DynamicPicExe`.With `+crt-static`: `StaticPicExe` (`crt-static-respected: true`). | `link.exe` / `lld-link` reads `.drectve` emitted by `library/core/src/ffi/mod.rs:76-83`:<br>• Default (`-C target-feature=-crt-static`): `/defaultlib:msvcrt` (pulls `mainCRTStartup` from `msvcrt.lib`, linking dynamic `vcruntime140.dll` + `ucrtbase.dll`).<br>• `+crt-static`: `/defaultlib:libcmt` (pulls `mainCRTStartup` from static `libcmt.lib` + `libvcruntime.lib` + `libucrt.lib`). | Default: `DynamicDylib` (`/DLL`, `/defaultlib:msvcrt`, `_DllMainCRTStartup`).With `+crt-static`: `StaticDylib` (`crt-static-allows-dylibs: true`, `/DLL`, `/defaultlib:libcmt`). | None (`coff` `.lib` archive; embeds `.drectve` `/defaultlib:msvcrt` or `/defaultlib:libcmt` inside `core`'s object files!). | None. |
| `x86_64-pc-windows-gnu` | Default: `DynamicPicExe` (`crt-static-respected: false` on `windows-gnu` in `1.99.1`, though `-C link-self-contained` controls CRT object source). | • Self-contained (`pre-link-objects-fallback`): `rustc` explicitly passes `<sysroot>/crt2.o` before user objects and late-links `-lmsvcrt -lmingwex -lmingw32 -lgcc -lmsvcrt -lmingwex -luser32 -lkernel32` plus `-lgcc_s` (dynamic) or `-lgcc_eh -l:libpthread.a` (static).<br>• External `x86_64-w64-mingw32-gcc`: GCC driver supplies `crt2.o`, `crtbegin.o`, `crtend.o`. | • Self-contained: `rustc` passes `<sysroot>/dllcrt2.o` (`DllMainCRTStartup`).<br>• External GCC driver: `dllcrt2.o`, `crtbegin.o`, `crtend.o`. | None (`ar` archive). | Built by `bootstrap` into `<sysroot>/lib/rustlib/x86_64-pc-windows-gnu/lib/{rsbegin,rsend}.o` (`compile.rs:917`), but their `.eh_frame` registration code is `#[cfg(target_arch = "x86")]` (`rsbegin.rs:56`), so on `x86_64` they contain no symbols and are only linked on `i686-pc-windows-gnu`. |

**Why `rsbegin.o` and `rsend.o` exist in `library/rtstartup/` (`rsbegin.rs:1-114`, `rsend.rs:1-41`):**
- `rsbegin.rs` and `rsend.rs` are `#![no_core]` Rust files compiled with `rustc --emit=obj` during toolchain bootstrap (`src/bootstrap/src/core/build_steps/compile.rs:928-950`).
- On 32-bit `i686-pc-windows-gnu` (`#[cfg(all(target_os = "windows", target_arch = "x86", target_env = "gnu"))]`), DWARF `.eh_frame` unwind tables are not discovered automatically by the OS loader; `rsbegin.o` defines `pub static __EH_FRAME_BEGIN__: [u8; 0] = []` in `.eh_frame`, a 6-`isize` `static mut OBJ` scratch struct (`struct object` in `libgcc/unwind-dw2-fde.h`), and `P_INIT` in `.ctors.65535` / `P_UNINIT` in `.dtors.65535` calling `__register_frame_info` / `__deregister_frame_info`, while `rsend.o` places the terminating zero sentinel `pub static __EH_FRAME_END__: u32 = 0` at the end of `.eh_frame`.
- On 64-bit `x86_64-pc-windows-gnu` (Tier 1), unwinding uses Windows PE+ `.pdata`/`.xdata` SEH rather than `.eh_frame` registration, so `eh_frames` is compiled out and `pre_mingw_self_contained()` (`crt_objects.rs:87-96`) links only `crt2.o` / `dllcrt2.o`.

### 4. Process and CPU State Assumed by Compiled Rust Code at Entry

Basis: normative + source + execution

When control enters compiled Rust code (either at the generated `main` wrapper for a `bin` crate or at any `pub extern "C"` / `#[no_mangle]` entry point in a `cdylib`/`staticlib`), the code generated by `rustc` / LLVM relies on the following architectural and OS state invariants:

| State Category | `x86_64` (`linux-gnu`, `windows-msvc`, `windows-gnu`) | `aarch64` (`linux-gnu`, `apple-darwin`, `windows-msvc`) | `i686-unknown-linux-gnu` | `i686-pc-windows-msvc` |
| :--- | :--- | :--- | :--- | :--- |
| **Stack Pointer (`SP`) Alignment at Function Entry** | `RSP % 16 == 8` (`16-byte` aligned prior to `callq`, which pushes an 8-byte return address; `S128` in `data-layout`) | `SP % 16 == 0` at all times when `SP` is used as a base register (`bl` writes return address to `x30`/`LR`; hardware `SP` alignment fault if `SP % 16 != 0`) | `ESP % 16 == 12` (`16-byte` aligned prior to `calll`, which pushes a 4-byte return address; `S128` in `data-layout`) | `ESP % 4 == 0` (**4-byte** aligned at call boundary; `S32` in `data-layout`; functions with $\ge 8\text{ B}$ aligned locals emit dynamic realignment `andl $-8, %esp`) |
| **CPU Flags / Direction Flag** | `RFLAGS.DF == 0` (forward string operations `rep movsb` / `rep stosb` assumed by `llvm.memcpy` / `llvm.memset` lowering) | `PSTATE` condition flags (`NZCV`) caller-saved / undefined at entry | `EFLAGS.DF == 0` | `EFLAGS.DF == 0` |
| **Floating-Point Control Register (`MXCSR` / `FPCR` / `x87 FCW`)** | `MXCSR == 0x1F80`: Round-to-Nearest-Even (`RC = 00`), Flush-to-Zero off (`FZ = 0`), Denormals-Are-Zero off (`DAZ = 0`), all 6 SIMD FP exceptions masked (`PM=UM=OM=ZM=DM=IM=1`). (`x87 FCW = 0x037F` on Linux/MinGW, `0x027F` on MSVC, though Rust `f32`/`f64` use SSE2). | `FPCR == 0x00000000`: Round-to-Nearest (`RMode = 00`), Flush-to-Zero off (`FZ = 0`, `FZ16 = 0`), Default NaN (`DN = 0` on Linux/Windows; Apple ARM64 ABI allows default `FPCR = 0`), all FP exception traps disabled (`IDE=IXE=UFE=OFE=DZE=IOE=0`). | `MXCSR == 0x1F80` (target spec sets `cpu: "pentium4"`, `rustc-abi: "x86-sse2"`, so scalar `f32`/`f64` arithmetic uses SSE2 `addss`/`addsd`, while `extern "C"` returns `f32`/`f64` on `st(0)` with `x87 FCW == 0x037F`, 64-bit precision). | `MXCSR == 0x1F80` (`cpu: "pentium4"`, `rustc-abi: "x86-sse2"`), plus `x87 FCW == 0x027F` (MSVC CRT sets 53-bit double precision and masks all x87 exceptions; `f32`/`f64` `cdecl` returns use `st(0)`). |
| **AArch64 SME (`PSTATE.SM`, `PSTATE.ZA`, `TPIDR2_EL0`)** | N/A | Standard AAPCS64 non-streaming interface: `PSTATE.SM == 0` (not in Streaming SVE mode) and `PSTATE.ZA == 0` (ZA array dormant / lazy-save `TPIDR2_EL0 == 0` or valid). | N/A | N/A |
| **Thread Pointer Register** | Linux: `%fs:0` points to TCB (`struct pthread`, stack guard at `%fs:0x28`).Windows: `%gs:0x30` points to `TEB` (`ThreadLocalStoragePointer` at `%gs:0x58`). | Linux: `TPIDR_EL0` (`mrs xN, tpidr_el0`) points to TCB.macOS: `TPIDRRO_EL0` (`mrs xN, tpidrro_el0`) holds thread self pointer (`tlv_get_addr`).Windows: `x18` (`pr_18`) points directly to `TEB` (`[x18, #0x58]` = `TlsArray`). | Linux: `%gs:0` points to TCB (`struct pthread`, stack guard at `%gs:0x14`). | Windows: `%fs:0x18` points to `TEB` (`%fs:[0]` = `ExceptionList` SEH chain; `%fs:[0x2c]` = `ThreadLocalStoragePointer`). |
| **OS Signal Mask & File Descriptors (`bin` after `rt::init`)** | Linux: `SIGPIPE` set to `SIG_IGN` (unless `-Zon-broken-pipe` overrides it); `SIGSEGV`/`SIGBUS` handled on `sigaltstack`; fds `0`, `1`, `2` guaranteed open (mapped to `/dev/null` if closed at `execve`).Windows: `SetThreadStackGuarantee(0x5000)` active; VEH registered. | Linux/macOS: `SIGPIPE` set to `SIG_IGN`; `SIGSEGV`/`SIGBUS` handled on `sigaltstack`; fds `0`, `1`, `2` guaranteed open.Windows: `SetThreadStackGuarantee(0x5000)` active; VEH registered. | Same as `x86_64-unknown-linux-gnu`. | Same as `x86_64-pc-windows-msvc`. |

## Boundaries

- **`#![no_main]` and `cdylib` / `staticlib` entry points:** As documented in `library/std/src/rt.rs:90` and `sys/pal/unix/mod.rs:20`, `std::rt::init` and `std::rt::cleanup` are *only* invoked when execution enters through the Rust-generated `main` $\rightarrow$ `lang_start` chain. In a `cdylib`, `staticlib`, or `#![no_main]` binary where C code calls a `#[no_mangle] pub extern "C" fn` directly:
  - `.init_array` / `__mod_init_func` / `.CRT$XCT` constructors (`RUST_LSE_INIT` and `ARGV_INIT_ARRAY`) still run when the shared library or executable is initialized by the OS loader;
  - However, `sanitize_standard_fds()`, `reset_sigpipe()`, `stack_overflow::init()`, and `rt::cleanup()` (`io::cleanup()` stdout flush at exit) do **not** run automatically.
- **Custom target specifications (`-Z build-std` / `#![no_std]`):** Bare-metal targets with `main_needs_argc_argv: false` or `os: "uefi"` (`efi_main(handle, system_table)`) use the alternate `create_entry_fn` branches in `compiler/rustc_codegen_ssa/src/base.rs:532-538, 610-634`.

## Evidence

### Primary Upstream Sources

- `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`):
  - `compiler/rustc_codegen_ssa/src/base.rs:500-635` (`maybe_create_entry_wrapper`, `create_entry_fn`, `get_argc_argv`).
  - `compiler/rustc_codegen_cranelift/src/main_shim.rs:14-160` (`maybe_create_entry_wrapper` in Cranelift backend).
  - `compiler/rustc_passes/src/entry.rs:74-105` (`configure_main`, `sigpipe(tcx)`).
  - `compiler/rustc_session/src/config/sigpipe.rs:1-21` (`DEFAULT = 0`, `INHERIT = 1`, `SIG_IGN = 2`, `SIG_DFL = 3`).
  - `compiler/rustc_target/src/spec/crt_objects.rs:1-135` and `compiler/rustc_codegen_ssa/src/back/link.rs:2250-2381` (`CrtObjects`, `link_output_kind`, `self_contained_components`, `add_pre_link_objects`, `add_post_link_objects`).
  - `library/core/src/ffi/mod.rs:75-83` (`#[link(name = "/defaultlib:msvcrt")]` vs. `#[link(name = "/defaultlib:libcmt", cfg(target_feature = "crt-static"))]`).
  - `library/rtstartup/rsbegin.rs:1-114`, `library/rtstartup/rsend.rs:1-41`, and `src/bootstrap/src/core/build_steps/compile.rs:906-954` (`StartupObjects` build step for `rsbegin.o` and `rsend.o`).
  - `library/std/src/rt.rs:87-211` (`init`, `thread_cleanup`, `cleanup`, `lang_start_internal`, `lang_start`).
  - `library/std/src/sys/configure_builtins.rs:1-60` (`RUST_LSE_INIT` in `.init_array.90`, `__DATA,__mod_init_func`, and `.CRT$XCT`).
  - `library/std/src/sys/args/unix.rs:95-190` (`ARGV_INIT_ARRAY` in `.init_array.00099` on Linux `gnu`; `_NSGetArgc`/`_NSGetArgv` on Apple).
  - `library/std/src/sys/pal/unix/mod.rs:17-218` (`sanitize_standard_fds`, `reset_sigpipe`, `on_broken_pipe_used`) and `library/std/src/sys/process/unix/unix.rs:364-375, 741-754` (child process `SIGPIPE` reset when `!on_broken_pipe_used()`).
  - `library/std/src/sys/pal/windows/mod.rs:42-60` and `compat.rs:26-69` (Windows `sys::init`, `sys::cleanup`, and `.CRT$XCT` `INIT_TABLE_ENTRY`).
  - `library/std/src/io/stdio.rs:726-745` (`stdio::cleanup()` flushing `STDOUT` via `LineWriter::with_capacity(0, stdout_raw())`).
  - `library/std/src/sys/exit.rs:1-69` (`unique_thread_exit()` mitigating concurrent `libc::exit` races on Linux).

### Preserved Package Support Artifacts

- `support/startup_probe.rs`: Minimal binary crate exercising `main` wrapper generation, `lang_start::<()>`, `vtable.0`, and `__rust_begin_short_backtrace`.
- `support/startup_x86_64-unknown-linux-gnu.ll`: LLVM IR emitted for `startup_probe.rs` on `x86_64-unknown-linux-gnu`, showing `@vtable.0`, `lang_start`, `__rust_begin_short_backtrace`, and the generated `@main` wrapper.
- `support/startup_x86_64-unknown-linux-gnu.s`, `support/startup_aarch64-unknown-linux-gnu.s`, `support/startup_i686-unknown-linux-gnu.s`, `support/startup_aarch64-apple-darwin.s`, `support/startup_x86_64-pc-windows-msvc.s`, `support/startup_aarch64-pc-windows-msvc.s`, `support/startup_i686-pc-windows-msvc.s`, `support/startup_x86_64-pc-windows-gnu.s`: Target assembly across all 8 Tier 1 targets.

## Revalidation

```bash
# 1. Inspect the generated C main wrapper and lang_start_internal call across all 8 Tier 1 targets
for t in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu i686-unknown-linux-gnu \
         aarch64-apple-darwin x86_64-pc-windows-msvc aarch64-pc-windows-msvc \
         i686-pc-windows-msvc x86_64-pc-windows-gnu; do
  rustc +1.99.1 --target "$t" --edition=2021 -C opt-level=2 \
    --emit=asm="/tmp/startup_${t}.s" \
    reports/rust-program-startup-runtime-objects-and-entry-state/support/startup_probe.rs
  echo "=== $t ==="
  grep -E "^_?main:|lang_start_internal|__main" "/tmp/startup_${t}.s"
done

# 2. Verify -Zon-broken-pipe=kill emits sigpipe = 3 (SIG_DFL) in the generated @main wrapper
rustc +nightly-2026-11-12 -Zon-broken-pipe=kill --edition=2021 -C opt-level=2 \
  --emit=llvm-ir=/tmp/startup_sigpipe_kill.ll \
  reports/rust-program-startup-runtime-objects-and-entry-state/support/startup_probe.rs
grep "lang_start_internal" /tmp/startup_sigpipe_kill.ll
```
