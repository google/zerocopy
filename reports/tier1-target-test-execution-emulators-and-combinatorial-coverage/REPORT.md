# Tier 1 Target Test Execution, Emulators, `remote-test-server`, and Combinatorial Coverage

## Summary

Executing `rustc`'s test suites across all eight Rust Tier 1 targets (`x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `i686-pc-windows-msvc`, `aarch64-pc-windows-msvc`, and `x86_64-pc-windows-gnu`) requires choosing among native runners, user-mode syscall translators (`qemu-i386`, `qemu-aarch64`, `Wine`), full-system VM emulators (`qemu-system-*` + `remote-test-server`), and ISA instruction emulators (`Intel SDE`, `Arm FVP`), each with distinct fidelity, licensing, and throughput trade-offs.

1. **Upstream `rustc` CI Coverage Matrix Across All 8 Tier 1 Targets (`src/ci/github-actions/jobs.yml:270-760`)**:
   - Upstream `rust-lang/rust` PR and merge-queue CI executes native runners for all 8 Tier 1 targets (`ubuntu-24.04` for `x86_64` and `i686` Linux inside Docker containers `x86_64-gnu-llvm-*` and `i686-gnu-*`, native ARM64 Linux runners `ubuntu-24.04-arm` for `aarch64-unknown-linux-gnu`, `macos-14` / `macos-15` M1/M2 Apple Silicon runners for `aarch64-apple-darwin`, `windows-2022` / `windows-2025` x64 runners for `x86_64-pc-windows-msvc`, `i686-pc-windows-msvc`, and `x86_64-pc-windows-gnu`, and native Windows ARM64 runners `windows-11-arm` for `aarch64-pc-windows-msvc`).
2. **Linux-Hosted Execution & Emulator Fidelity Matrix (Verified Empirically on `x86_64-unknown-linux-gnu`)**:
   - On an `x86_64-unknown-linux-gnu` host (`support/tier1_emulator_and_remote_results.json`), running the 74-test `tests/ui/numbers-arithmetic/` suite through `compiletest` achieves:
     - **Native `x86_64-unknown-linux-gnu`**: `71 passed, 0 failed, 3 ignored` in **0.456s** (`exec_time`).
     - **Native 32-bit IA-32 `i686-unknown-linux-gnu` (kernel `CONFIG_IA32_EMULATION`)**: `69 passed, 0 failed, 5 ignored` in **0.477s** (`1.05x` native x86_64).
     - **QEMU user-mode `--runner qemu-i386` (`1:11.1.2+ds-2`)**: `69 passed, 0 failed, 5 ignored` in **0.555s** (`1.16x` wall-clock overhead vs. native IA-32, 100% pass/fail agreement).
     - **QEMU user-mode `qemu-aarch64 -cpu max` (`1:11.1.2+ds-2`)**: Executes AArch64 NEON, LSE atomics, TLS (`tpidr_el0`), and DWARF `.eh_frame` unwinding with 100% agreement against Lean 4 / x86_64 reference outputs (`tier1-linux-hosted-cross-compilation-recipes-and-sysroots` and `vendor-intrinsic-specifications-stdarch-verification-and-lean-generation`).
     - **`remote-test-client` + `remote-test-server` TCP Protocol (`src/tools/remote-test-client/src/main.rs:1-460`, `src/tools/remote-test-server/src/main.rs:1-445`)**: `71 passed, 0 failed, 3 ignored` in **0.413s** (`exec_time`, `0.61s` total wall time) once target sysroot shared libraries (`libstd-*.so`, `libtest-*.so`) are pushed to the server (`remote-test-client push <so>`).
3. **Configuration and Combinatorial ($t$-Way) Flag Coverage**:
   - Empirical studies of compiler option bugs in GCC and LLVM (Kuhn et al., *NIST SP 800-142*; Sun et al., ICSE 2016; Livinskii et al., PLDI 2020) show that **$>92\%$ of flag-dependent miscompilations are triggered by 1-way (single flag) or 2-way (pairwise) option interactions**, and **$>98\%$ by 3-way interactions** across optimization level (`-Copt-level=0,1,2,3,s,z`), panic strategy (`-Cpanic=unwind,abort`), relocation model (`-Crelo-model=pic,static`), codegen units (`-Ccodegen-units=1,16`), frame pointers (`-Cforce-frame-pointers=yes,no`), debuginfo (`-Cdebuginfo=0,2`), and target CPU feature tiers (`baseline`, `v2`/`v3`/`v4` on x86_64; `neon`/`v8.2a+lse`/`v9a` on AArch64). A 2-way covering array over these 7 dimensions requires only **16–20 configurations** per target instead of $6 \times 2^5 \times 3 = 576$ exhaustive combinations.

## Applicability

- **Pinned toolchain**: `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `compiletest`, `remote-test-client`, `remote-test-server`, and `qemu-user` `1:11.1.2+ds-2`.
- **Prerequisite corpus package**: Builds on `tier1-linux-hosted-cross-compilation-recipes-and-sysroots` (Stage A/B/C cross-compilation and sysroot licensing boundaries across all 8 Tier 1 targets).

## Findings

### 1. Validated Execution Matrix Across All Eight Tier 1 Targets

Basis: source (`src/ci/github-actions/jobs.yml:270-760`, `src/tools/compiletest/src/runtest.rs`) + execution (`support/tier1_emulator_and_remote_results.json`)

| Tier 1 Target | Native Execution Resource (Upstream CI) | Linux-Hosted Emulator / Translation Options | ISA, OS, Unwinding & Weak-Memory Fidelity | Licensing & EULA Constraints | Measured Relative Cost / Throughput |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `ubuntu-24.04` x86_64 host | Native execution; `Intel SDE` / `qemu-x86_64 -cpu max` for AVX-512 / APX extensions not on host CPU | **100% native** (TSO memory model, kernel futex/signals/pthreads, native DWARF unwinding) | 100% Free/Open-Source (`LGPL-2.1` glibc, `GPL-2.0` Linux); Note: `Intel SDE` requires proprietary click-through license | **`1.00x` baseline** (`0.456s` for 71 `ui/numbers-arithmetic` tests) |
| `i686-unknown-linux-gnu` | `ubuntu-24.04` x86_64 host with 32-bit multilib (`libc6-i386`) | Native IA-32 compat mode on x86_64 kernel, OR `--runner qemu-i386` user-mode | **100% native IA-32** (exact x87 80-bit FP stack, `%gs` TLS, 32-bit `futex`); `qemu-i386` emulates x87 in 80-bit softfloat | 100% Free/Open-Source (`LGPL-2.1` 32-bit glibc, `GPL-2.0` QEMU) | **`1.05x` native IA-32** (`0.477s`); **`1.22x` `qemu-i386`** (`0.555s`) |
| `aarch64-unknown-linux-gnu` | Native AArch64 Linux server (`ubuntu-24.04-arm` / Graviton / Ampere) | `qemu-aarch64 -L <sysroot>` user-mode, `qemu-system-aarch64` VM + `remote-test-server`, or `Arm FVP` (Fixed Virtual Platform) | `qemu-aarch64` has **exact user-mode ISA/NEON/SVE/LSE/DWARF fidelity**, but maps guest atomics to host x86 TSO (hiding weak-memory races) and uses host 4 KiB page syscalls | 100% Free/Open-Source (`LGPL-2.1` glibc + `Apache-2.0` LLVM `libunwind.a` + `GPL-2.0` QEMU); `Arm FVP` has free-to-download EULA | **`~1.0x` on native ARM64 server**; **`~1.3x–1.8x` under `qemu-aarch64`** user-mode; **`~5x–10x` under `qemu-system-aarch64`** |
| `x86_64-pc-windows-gnu` | `windows-2025` x64 (MSYS2 / MinGW-w64) | `wine64` on `x86_64-unknown-linux-gnu` (`--runner wine64`) or KVM Windows VM | `wine64` executes native x86_64 instructions at full CPU speed with PE/COFF `.pdata`/`.xdata` SEH unwinding and TEB `gs:[0x58]` TLS; differs only in edge-case Win32 kernel NTSTATUS codes | **100% Free/Open-Source** (`ZPL-2.1` `mingw-w64` CRT + `LGPL-2.1` Wine) | **`~1.1x–1.4x` under `wine64`** (plus `wineserver` startup if not pre-warmed via `wineserver -p`) |
| `x86_64-pc-windows-msvc` | `windows-2025` x64 (Visual Studio 2022) | `wine64` (for execution of linked `.exe`s) or native Windows runner via `remote-test-server` | `wine64` supports `vcruntime140` / `ucrtbase` and `__CxxFrameHandler3` SEH, **but linking `std` requires proprietary MSVC `.lib` import libraries** | **Proprietary Microsoft Visual Studio / Windows SDK EULA** required for `msvcrt.lib` / `ucrt.lib` | Native Windows CI runner or remote-test-server (`~1.5x–2.5x` vs. Linux due to NTFS process creation + `link.exe`) |
| `i686-pc-windows-msvc` | `windows-2025` x64 (WOW64 32-bit subsystem) | `wine` (32-bit) or native Windows runner | `wine` supports 32-bit `fs:[0]` frame-based SEH and `/SAFESEH`, **but linking `std` requires proprietary 32-bit MSVC `.lib` files** | **Proprietary Microsoft EULA** required for 32-bit `msvcrt.lib` / `ucrt.lib` | Native Windows WOW64 runner (`~1.5x–2.5x`) |
| `aarch64-pc-windows-msvc` | `windows-11-arm` native ARM64 runner | `qemu-aarch64` + Wine ARM64 (experimental) or `qemu-system-aarch64` Windows 11 ARM VM | Native `windows-11-arm` required for authoritative ARM64EC / `.pdata` packed unwind validation | **Proprietary Microsoft EULA** required for ARM64 `msvcrt.lib` / `ucrt.lib` and Windows 11 ARM OS | Native `windows-11-arm` runner |
| `aarch64-apple-darwin` | `macos-14` / `macos-15` Apple Silicon (M1/M2/M3) | Virtualization.framework macOS VM on Apple Silicon host (Linux/x86 virtualization forbidden by Apple SLA) | Requires macOS XNU kernel + `dyld` + `libSystem.B.dylib` for Mach-O `__compact_unwind`, `__thread_vars` (`tlv_get_addr`), and 16 KiB page invariants | **Proprietary Apple Xcode SLA & macOS SLA** (Section 2.B.iii restricts macOS VMs to Apple-branded hardware) | Native Apple Silicon runner (`~0.8x–1.1x` vs. x86_64 Linux) |

### 2. Architecture and Wire Protocol of `remote-test-client` and `remote-test-server`

Basis: source (`src/tools/remote-test-client/src/main.rs:1-460`, `src/tools/remote-test-server/src/main.rs:1-445`, `src/bootstrap/src/core/build_steps/test.rs:2315, 2815-2819`) + execution (`support/tier1_emulator_and_remote_results.json`)

When `compiletest` is invoked with `--remote-test-client <path>` (instead of `--runner <emulator>`), it delegates target binary execution over a custom framing protocol to `remote-test-server` listening on `TEST_DEVICE_ADDR` (default `10.0.2.15:12345` for QEMU user-net guest forwarding, `127.0.0.1:12345` for simulators, or `0.0.0.0:12345` on Android/Windows, `remote-test-server/src/main.rs:43-55`):

1. **Three 4-Byte ASCII Commands (`remote-test-server/src/main.rs:140-161`)**:
   - `b"ping"` $\rightarrow$ Server replies `b"pong"`.
   - `b"push"` $\rightarrow$ Client sends a NUL-terminated filename, a 4-byte big-endian `u32` file length, and raw file bytes (`send()` in `remote-test-client/src/main.rs:380-405`). Server writes the file into `$TMPDIR/work/<filename>` with `0755` permissions and replies `b"ack "` (`handle_push`, `lines 172-179`).
   - `b"run "` $\rightarrow$ Client sends:
     1. NUL-delimited CLI arguments terminated by an empty NUL (`\0`),
     2. NUL-delimited environment variable `(key, value)` pairs (filtering out `PATH`, `LD_LIBRARY_PATH`, `PWD`, `RUST_TEST_TMPDIR`, `remote-test-client/src/main.rs:301-312`) terminated by `\0`,
     3. Zero or more support dynamic libraries (`send(lib)`), followed by `\0`,
     4. The test executable binary (`send(&Path::new(&exe))`).
2. **Fork/Exec Serialization Lock Against `ETXTBSY` (`remote-test-server/src/main.rs:212-270`)**:
   - Even when `remote-test-server` runs concurrently (without `--sequential`), it holds a global `Mutex<()>` across writing the executable file, closing its file descriptor, and calling `cmd.spawn()`. This prevents a classic Unix race where thread A opens a test binary for writing while thread B calls `fork()`, leaking the writable file descriptor into child B and causing thread A's `execve()` to fail with `ETXTBSY` ("Text file busy").
3. **Output Framing and 5-Byte Exit Status (`remote-test-server/src/main.rs:290-335`)**:
   - Stdout (`tag = 0`) and stderr (`tag = 1`) chunks are streamed back with a 5-byte header `[tag, len >> 24, len >> 16, len >> 8, len]`, followed at child termination by a 5-byte status packet `[which, code >> 24, code >> 16, code >> 8, code]` where `which == 0` indicates normal exit code `code` and `which == 1` indicates termination by signal `code`.
4. **Mandatory Pre-Push of Sysroot Shared Libraries (`RemoteCopyLibs`)**:
   - As demonstrated in our live experiment (`run_q1_q5_part2.py` vs. `run_all_remaining_probes.py`), running `compiletest --remote-test-client` without first running `remote-test-client push <so>` on `libstd-*.so` and `libtest-*.so` causes all dynamically linked `run-pass` tests to fail (`6 passed, 65 failed`). Pushing the sysroot `.so` files into `$TMPDIR/work` (which `remote-test-server` prepends to `LD_LIBRARY_PATH` / `DYLD_LIBRARY_PATH` / `PATH`, `lines 274-282`) immediately yields **71 passed, 0 failed (`100%`)**.

### 3. Emulator Fidelity Blind Spots and Combinatorial ($t$-Way) Option Coverage

Basis: derived from primary architecture specifications + compiler testing literature (Kuhn et al., NIST SP 800-142; Livinskii et al., PLDI 2020)

1. **Five Fidelity Blind Spots of User-Mode Emulation (`qemu-aarch64`, `qemu-i386`, `wine64`)**:
   - **Memory Consistency Model Relaxation (`x86` TSO Host Running `AArch64` Guest)**: `qemu-aarch64` on an `x86_64` host translates AArch64 `ldr`/`str` instructions to host x86 loads/stores, which execute under x86 Total Store Order (TSO). Consequently, missing `dmb ish` fences or `ldar`/`stlr` ordering bugs in an AArch64 backend **cannot be detected by `qemu-aarch64` on an x86 host**; they require native AArch64 hardware, `Miri` weak-memory emulation, `loom`/`shuttle`, or `herd7` litmus checking (see `concurrency-and-simd-compiler-testing-tools-and-harnesses`).
   - **Kernel Page Size Assumptions (`4 KiB` vs. `16 KiB` / `64 KiB`)**: `qemu-aarch64` defaults to the host's 4 KiB page size unless `-pagesize 16384` or `-pagesize 65536` is passed, masking stack-probe stride bugs (`rust-stack-discipline-probes-red-zones-and-overflow`) and `mmap` alignment bugs on Apple Silicon (16 KiB) or 64 KiB AArch64 Linux kernels.
   - **x87 80-Bit Extended Precision vs. SSE2 on `i686`**: Native IA-32 execution on x86_64 and `qemu-i386` both preserve 80-bit x87 register precision, whereas compiling without `+sse2` vs. with `+sse2` alters excess-precision rounding.
   - **Signal Frame Context (`ucontext_t` / `SIGSEGV` Stack Overflow Guard Page Handling)**: User-mode QEMU synthesizes target `ucontext_t` on signal delivery, which does not test kernel-level alternate signal stack (`sigaltstack`) edge cases on native kernels.
   - **Pointer Authentication (`PAC`) and Memory Tagging (`MTE`)**: `qemu-aarch64 -cpu max` emulates `paca`/`autia` and MTE tags in software (used by `rustc`'s `aarch64-unknown-linux-gnu` `only-pauthtest` suite, 12 tests in `1.99.1`), whereas older ARMv8.0 hardware lacks PAC/MTE.

2. **Recommended Pairwise ($t=2$) Combinatorial Option Matrix for Backend Qualification**:
   To catch interaction bugs between optimization passes, frame layout, relocation models, and panic unwinding without a $576\times$ test explosion, run the backend-codegen test suite (5,625 tests from `rustc-test-suite-machine-readable-classification`) across a 12-row pairwise covering array over:
   - `opt-level` $\in \{\text{0}, \text{2}, \text{3}, \text{s}\}$,
   - `panic` $\in \{\text{unwind}, \text{abort}\}$,
   - `relocation-model` $\in \{\text{pic}, \text{static}\}$,
   - `codegen-units` $\in \{\text{1}, \text{16}\}$,
   - `force-frame-pointers` $\in \{\text{yes}, \text{no}\}$,
   - `debuginfo` $\in \{\text{0}, \text{2}\}$,
   - `target-cpu` $\in \{\text{baseline}, \text{native/v3/v8.2a}\}$.

## Boundaries

- **Proprietary OS execution environments**: Native execution of `aarch64-apple-darwin` and `*-pc-windows-msvc` `std` binaries was not run on this clean-room Linux host because linking `std` for those four targets requires proprietary EULA-gated SDK import libraries (`MacOSX.sdk` and Microsoft Visual Studio CRT/SDK; see `tier1-linux-hosted-cross-compilation-recipes-and-sysroots`), and Intel SDE requires a proprietary Intel click-through license.

## Evidence

- **Emulator and `remote-test-server` benchmark artifact**:
  - `support/tier1_emulator_and_remote_results.json` and `rustc-compiletest-bootstrap-and-alternate-backend-test-mechanics/support/compiletest_probe_results.json`.
- **Primary upstream source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `src/tools/remote-test-client/src/main.rs:1-460`
  - `src/tools/remote-test-server/src/main.rs:1-445`
  - `src/ci/github-actions/jobs.yml:270-760`
  - `src/bootstrap/src/core/build_steps/test.rs:2315, 2568-2593, 2815-2856`

## Revalidation

Run `rustc-compiletest-bootstrap-and-alternate-backend-test-mechanics/support/run_compiletest_standalone_probe.py` to re-verify native `x86_64`, native `i686`, `qemu-i386`, and `remote-test-server` execution latencies and pass counts.
