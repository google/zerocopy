# Linux-Hosted Cross-Compilation Recipes, Sysroot Dependencies, and Licensing Boundaries Across All Eight Tier 1 Targets

## Summary

From a single `x86_64-unknown-linux-gnu` host with `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) and all eight Tier 1 `rust-std` target
components installed, the compilation and linking pipeline separates cleanly into three
stages with distinct external sysroot and licensing requirements:

1. **Stage A — Compiler, Object, Archive, and `no_std` Linking (8 / 8 Tier 1 Targets,
   Zero Proprietary SDKs)**: `rustc +1.99.1 --target <triple> --emit=obj,link` compiles
   any `core`/`alloc`/`std` crate to `.o`, `.rlib`, and `staticlib` across **all 8
   Tier 1 targets** with zero external C toolchains or OS SDKs. Furthermore, bundled
   `<sysroot>/lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld` natively links
   `no_std` `cdylib` and executable PE32/PE32+ (`-flavor link`), ELF32/ELF64
   (`-flavor gnu`), and Mach-O `arm64` (`-flavor darwin`, using a 10-line open-source
   `tapi-tbd` v4 stub and emitting a valid ad-hoc `LC_CODE_SIGNATURE`) on Linux.
2. **Stage B — Full `std` Linking and Execution Under Free/Open-Source Licenses
   (4 / 8 Tier 1 Targets)**:
   - All **3 Linux Tier 1 targets** (`x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`,
     and `aarch64-unknown-linux-gnu`) compile, link, and execute full multi-threaded,
     unwinding `std` programs on `x86_64-unknown-linux-gnu` (running `x86_64` and `i686`
     natively or via `qemu-i386`, and `aarch64` via `qemu-aarch64` against an
     `aarch64-linux-gnu` glibc sysroot + Apache-2.0 LLVM `libunwind.a`).
   - `x86_64-pc-windows-gnu` uses open-source `mingw-w64` CRT headers/archives
     (`ZPL-2.1` / Public Domain) plus `rustup`'s bundled `crt2.o`/`dllcrt2.o`/`rsbegin.o`/`rsend.o`
     and `windows_x86_64_gnu`'s `libwindows.0.52.0.a` (`MIT OR Apache-2.0`).
3. **Stage C — Proprietary EULA-Gated `std` Final-Link Sysroots (4 / 8 Tier 1 Targets)**:
   Linking a `std` executable or `cdylib` for `x86_64-pc-windows-msvc`,
   `i686-pc-windows-msvc`, `aarch64-pc-windows-msvc`, or `aarch64-apple-darwin`
   requires proprietary runtime import libraries (`msvcrt.lib` / `vcruntime.lib` /
   `ucrt.lib` for the 14 C/C++ CRT symbols used by `std` on Windows MSVC, and
   `libSystem.B.tbd` from `MacOSX.sdk` on macOS) whose redistribution or automated
   download (`xwin --accept-license`, Apple Xcode SLA) requires accepting a proprietary
   click-through EULA (see `compiler-isa-sdk-licensing-trademarks-and-upstream-governance`).

## Applicability

- **Pinned toolchain**: `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`),
  bundled `rust-lld` `22.1.1`.
- **Host environment**: `x86_64-unknown-linux-gnu`.
- **Target matrix**: All eight Rust Tier 1 targets.

## Findings

### 1. Upstream `rust-lang/rust` CI Architecture vs Single-Host Cross-Compilation

Inspecting `src/ci/github-actions/jobs.yml:270-760` and `src/ci/docker/` in
`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` reveals that upstream
CI does **not** cross-compile all eight Tier 1 targets from a single Linux container;
instead, it dispatches each OS family to native GitHub Actions runners:

| Tier 1 Target | Upstream CI Job (`src/ci/github-actions/jobs.yml`) | Upstream Runner Image & Environment | C/C++ Toolchain & Sysroot Used in Upstream CI |
| :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `dist-x86_64-linux` (line 459) | `ubuntu-24.04` running `src/ci/docker/host-x86_64/dist-x86_64-linux/Dockerfile` (`centos:7`, glibc `2.17`) | GCC `10.5.0` (crosstool-ng), binutils `2.42`, LLVM/Clang `22.1.1` (`rust-lld`) |
| `i686-unknown-linux-gnu` | `dist-i686-linux` (line 369) | `ubuntu-24.04` running `src/ci/docker/host-x86_64/dist-i686-linux/Dockerfile` (`centos:7` multilib) | 32-bit multilib GCC/glibc inside x86_64 container |
| `aarch64-unknown-linux-gnu` | `dist-aarch64-linux` (line 289) | Native Arm64 `ubuntu-24.04-arm` running `src/ci/docker/host-aarch64/dist-aarch64-linux/Dockerfile` (`centos:7` aarch64, glibc `2.17`) | Native aarch64 GCC `10.5.0` + binutils `2.42` |
| `aarch64-apple-darwin` | `dist-aarch64-apple` (line 699) | Native Apple Silicon `macos-15` (`Select-Xcode -Version 26.2`) | Apple Xcode `26.2` (`clang`, `ld`, `MacOSX.sdk` with `-mmacosx-version-min=11.0.0`) |
| `x86_64-pc-windows-msvc` | `dist-x86_64-msvc` (line 627) | Native `windows-2025` | Pre-installed Visual Studio 2022 MSVC (`cl.exe`, `link.exe`, Windows 10/11 SDK, `msvcrt.lib`) |
| `i686-pc-windows-msvc` | `dist-i686-msvc` (line 583) | Native `windows-2025` | Pre-installed Visual Studio 2022 x86 MSVC toolchain & Windows SDK |
| `aarch64-pc-windows-msvc` | `dist-aarch64-msvc` (line 548) | Native Arm64 `windows-11-arm` (or cross from `windows-2025`) | Visual Studio 2022 ARM64 MSVC toolchain & Windows SDK |
| `x86_64-pc-windows-gnu` | `dist-x86_64-mingw` (line 600) | Native `windows-2025` MSYS2 / MinGW-w64 | `x86_64-w64-mingw32-gcc` (LLVM/MinGW-w64 toolchain) |

### 2. Complete Linux-Hosted Cross-Compilation Matrix (`support/t11_recipes_matrix.json`)

The table below summarizes what `rustc +1.99.1` ships out of the box on
`x86_64-unknown-linux-gnu`, what additional sysroot files are required to link `std`,
and the verified build/link/run status:

| Target | `.o` / `.rlib` / `staticlib` (`std`) | `no_std` `cdylib` / `bin` via `rust-lld` | Full `std` `bin` / `cdylib` Link & Run on Linux | Bundled in `rustup` `rust-std` (`1.99.1`) | External Sysroot Required for Full `std` Link & Its License |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | Verified (`rc=0`) | Verified (`rc=0`) | **Verified (`rc=0`, native run)** | `libstd`/`libcore`/etc., `bin/rust-lld`, `bin/gcc-ld/ld.lld` | Host `gcc` + `glibc-devel` (`crt1.o`, `crti.o`, `crtn.o`, `libc.so`, `libgcc_s.so` — `LGPL-2.1+` / `GPL-3.0-with-GCC-exception`) |
| `i686-unknown-linux-gnu` | Verified (`rc=0`) | Verified (`rc=0`) | **Verified (`rc=0`, native IA32 & `qemu-i386`)** | `libstd`/`libcore`/etc., `bin/rust-lld`, `bin/gcc-ld/ld.lld` | 32-bit multilib `gcc-multilib` + `libc6-dev-i386` (`/usr/lib32/crt1.o`, `libc.so`, `libgcc_s.so` — `LGPL-2.1+` / `GPL-3.0-with-GCC-exception`) |
| `aarch64-unknown-linux-gnu` | Verified (`rc=0`) | Verified (`rc=0`) | **Verified (`rc=0`, `qemu-aarch64` run)** | `libstd`/`libcore`/etc., `bin/rust-lld`, `bin/gcc-ld/ld.lld` | `aarch64-linux-gnu` glibc sysroot (`LGPL-2.1+`) + `clang --target=aarch64-unknown-linux-gnu` + LLVM `libunwind.a` (`Apache-2.0 WITH LLVM-exception`) |
| `aarch64-apple-darwin` | Verified (`rc=0`) | **Verified (`rc=0`, emits `LC_CODE_SIGNATURE`)** | Blocked at `std` final link by Apple SLA (`libSystem.B.tbd`) | `libstd`/`libcore`/etc., `bin/rust-lld -flavor darwin` (`ld64.lld`) | `MacOSX.sdk/usr/lib/libSystem.B.tbd` (**Proprietary Apple Xcode SLA**) |
| `x86_64-pc-windows-msvc` | Verified (`rc=0`) | **Verified (`rc=0`)** | Blocked at `std` final link by MS EULA (`msvcrt.lib` / `ucrt.lib`) | `libstd`/`libcore`/etc. (with `raw-dylib` Win32/NT stubs), `bin/rust-lld -flavor link` | `windows.0.52.0.lib` (`MIT OR Apache-2.0`, in crates.io `windows_x86_64_msvc`) + `msvcrt.lib`/`vcruntime.lib`/`ucrt.lib` (**Proprietary Microsoft VS / Windows SDK EULA**) |
| `x86_64-pc-windows-gnu` | Verified (`rc=0`) | **Verified (`rc=0`)** | Open-source linkable (requires `mingw-w64` `libmingwex.a` / `libmsvcrt.a`) | `libstd`/`libcore`/etc., **`crt2.o`, `dllcrt2.o`, `rsbegin.o`, `rsend.o`**, `bin/rust-lld` | `libwindows.0.52.0.a` (`MIT OR Apache-2.0`, in crates.io `windows_x86_64_gnu`) + `mingw-w64` `libmingwex.a`, `libmingw32.a`, `libmsvcrt.a` (`ZPL-2.1` / Public Domain) |
| `i686-pc-windows-msvc` | Verified (`rc=0`) | **Verified (`rc=0`)** | Blocked at `std` final link by MS EULA (`msvcrt.lib` / `ucrt.lib`) | `libstd`/`libcore`/etc., `bin/rust-lld -flavor link` | `windows.0.52.0.lib` (`MIT OR Apache-2.0`, `windows_i686_msvc`) + `msvcrt.lib`/`vcruntime.lib`/`ucrt.lib` (**Proprietary Microsoft EULA**) |
| `aarch64-pc-windows-msvc` | Verified (`rc=0`) | **Verified (`rc=0`)** | Blocked at `std` final link by MS EULA (`msvcrt.lib` / `ucrt.lib`) | `libstd`/`libcore`/etc., `bin/rust-lld -flavor link` | `windows.0.52.0.lib` (`MIT OR Apache-2.0`, `windows_aarch64_msvc`) + `msvcrt.lib`/`vcruntime.lib`/`ucrt.lib` (**Proprietary Microsoft EULA**) |

### 3. Verified Linux Recipes (`x86_64`, `i686`, and `aarch64-unknown-linux-gnu`)

All three Linux Tier 1 targets were verified against a multi-threaded, unwinding
`std` test binary (`std_probe.rs` in `support/test_t11_recipes.py`, exercising thread
spawning, `AtomicUsize`, `Mutex`, `HashMap`, and `std::panic::catch_unwind`):

1. **`x86_64-unknown-linux-gnu` (Native)**:
   ```bash
   rustc +1.99.1 --target x86_64-unknown-linux-gnu -C opt-level=2 std_probe.rs -o std_probe_x86_64
   ./std_probe_x86_64
   # Output: OK arch=x86_64 os=linux res=30 caught=60
   ```
2. **`i686-unknown-linux-gnu` (32-bit Multilib + `qemu-i386`)**:
   ```bash
   rustc +1.99.1 --target i686-unknown-linux-gnu -C opt-level=2 std_probe.rs -o std_probe_i686
   ./std_probe_i686
   qemu-i386 ./std_probe_i686
   # Output: OK arch=x86 os=linux res=30 caught=60
   ```
3. **`aarch64-unknown-linux-gnu` (Cross-Linked with Clang + LLVM `libunwind.a` + `qemu-aarch64`)**:
   `library/unwind/src/lib.rs:34-43` links `-lgcc_s` by default on `*-unknown-linux-gnu`.
   When cross-compiling with a Clang/LLVM toolchain and an `aarch64-linux-gnu` glibc
   sysroot that provides `crt1.o`, `crti.o`, `crtn.o`, and `libc.so.6` without GCC's
   `libgcc_s.so`, LLVM's `libunwind.a` (`Apache-2.0 WITH LLVM-exception`) is a binary-compatible
   drop-in replacement for `_Unwind_Resume`, `_Unwind_Backtrace`, `_Unwind_RaiseException`,
   and `_Unwind_DeleteException` via a 1-line linker script `libgcc_s.so`:
   ```ld
   INPUT ( <clang-dir>/lib/aarch64-unknown-linux-gnu/libunwind.a )
   ```
   ```bash
   # Wrapper script aarch64-cc.sh:
   # exec clang --target=aarch64-unknown-linux-gnu --sysroot=<aarch64-glibc-sysroot> "$@"
   rustc +1.99.1 --target aarch64-unknown-linux-gnu -C opt-level=2 \
     -C linker=./aarch64-cc.sh \
     -L native=./aarch64-unwind-shim \
     -C link-arg=<clang-dir>/lib/clang/23/lib/aarch64-unknown-linux-gnu/clang_rt.crtbegin.o \
     -C link-arg=<clang-dir>/lib/clang/23/lib/aarch64-unknown-linux-gnu/clang_rt.crtend.o \
     std_probe.rs -o std_probe_aarch64
   qemu-aarch64 -L <aarch64-glibc-sysroot> ./std_probe_aarch64
   # Output: OK arch=aarch64 os=linux res=30 caught=60
   ```

### 4. Exact Symbol Inventory of Windows and macOS Sysroot Dependencies

#### 4.1 Windows `*-pc-windows-msvc`: `windows.0.52.0.lib` vs Proprietary `msvcrt.lib`

In `rustc 1.99.1`, `library/std` imports Win32/NT APIs through two mechanisms:
- `library/windows_link/src/lib.rs:1-52`: Uses `#[link(name = "...", kind = "raw-dylib")]`
  when `cfg(cargobuild)` is active (`bcryptprimitives.dll`, `api-ms-win-core-synch-l1-2-0.dll`),
  and otherwise links `-l windows.0.52.0`.
- The open-source crates `windows_x86_64_msvc`, `windows_i686_msvc`, and
  `windows_aarch64_msvc` (`0.52.6`, `MIT OR Apache-2.0`) ship pre-generated import
  libraries `windows.0.52.0.lib` that satisfy every Win32 API import in `libstd` except
  `NtCreateNamedPipeFile` (which resides in `ntdll.dll` and can be synthesized via
  `llvm-dlltool` or `ar_archive_writer`).
- Passing `-L native=<windows_x86_64_msvc>/lib` and a 1-symbol `ntdll.lib` stub to
  `rustc +1.99.1 --target x86_64-pc-windows-msvc -C linker=rust-lld -C linker-flavor=lld-link`
  leaves **exactly 14 undefined symbols**, all belonging to Microsoft's C/C++ CRT
  (`msvcrt.lib` / `vcruntime.lib` / `ucrt.lib`):
  1. Entry point & initialization: `mainCRTStartup`, `atexit`, `_fltused`, `_tls_index`
  2. Stack probe: `__chkstk`
  3. SEH / C++ exception unwinding (`libpanic_unwind`): `__CxxFrameHandler3`,
     `_CxxThrowException`, `const type_info::'vftable'` (`??_7type_info@@6B@`)
  4. Memory & string primitives: `memcpy`, `memmove`, `memset`, `memcmp`, `strlen`, `wcslen`

For `no_std` binaries and `cdylib`s (`-C panic=abort -C link-arg=/NOENTRY -C link-arg=/NODEFAULTLIB`),
**zero** external `.lib` files are needed: `rust-lld -flavor link` produces valid PE32/PE32+
binaries across all three MSVC targets (`x86_64`, `i686`, `aarch64`) directly on Linux.

#### 4.2 Windows `x86_64-pc-windows-gnu`: Bundled CRT Objects vs `mingw-w64`

Unlike the MSVC targets, `rustup`'s `rust-std-1.99.1-x86_64-pc-windows-gnu` component
bundles four prebuilt COFF startup objects directly inside
`<sysroot>/lib/rustlib/x86_64-pc-windows-gnu/lib/`:
- `crt2.o` (executable startup) and `dllcrt2.o` (DLL startup)
- `rsbegin.o` and `rsend.o` (Rust DWARF/SEH frame and `.CRT` section delimiters)

Combining those bundled objects with `windows_x86_64_gnu`'s `libwindows.0.52.0.a`
(`MIT OR Apache-2.0`) leaves only the open-source `mingw-w64` (`ZPL-2.1`) archives
`libmingwex.a`, `libmingw32.a`, and `libmsvcrt.a` (plus `libgcc.a` or `libunwind.a`),
which can be built from upstream `mingw-w64` source or installed from standard Linux
distribution packages (`mingw-w64-x86-64-dev`) without any proprietary EULA.

#### 4.3 `aarch64-apple-darwin`: `rust-lld -flavor darwin` and `tapi-tbd` Stubs

When targeting `aarch64-apple-darwin` on Linux with
`-C linker=<sysroot>/lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld -C linker-flavor=ld64.lld`:
- `rustc` attempts to run `xcrun --sdk macosx --show-sdk-path`
  (`compiler/rustc_codegen_ssa/src/back/apple.rs:212-265`), emits a non-fatal warning
  when `xcrun` is absent on Linux, and invokes `rust-lld -flavor darwin`.
- `rust-lld -flavor darwin` natively parses text-based `.tbd` stub files (`!tapi-tbd`
  `tbd-version: 4`), resolves Mach-O `arm64` relocations and LOH hints, and writes a
  valid `LC_CODE_SIGNATURE` (`CS_ADHOC | CS_LINKER_SIGNED`).
- Verified in `support/test_t11_recipes.py`: a `no_std` `cdylib` links cleanly (`rc=0`)
  on Linux against a 10-line synthetic `libSystem.tbd` defining `___chkstk_darwin`,
  `_memcpy`, `_memmove`, `_memset`, `_memcmp`, and `_bzero`. Linking full `libstd`
  additionally requires the ~115 Darwin libc/pthread/dyld/libunwind symbol names in
  `libSystem.B.tbd`, which in Apple's official distribution is governed by the Xcode SLA.

### 5. Host-Independent Reproducibility Flags Across All 8 Tier 1 Targets

To produce byte-for-byte deterministic `.o`, `.rlib`, and linked outputs regardless of
the Linux build directory or timestamp:

| Artifact Layer | Flag / Environment Variable | Source Implementation & Effect |
| :--- | :--- | :--- |
| DWARF / CodeView / `std::panic::Location` paths | `--remap-path-prefix=$PWD=/build` + `-Z remap-cwd-prefix=.` | Rewrites source file paths in `.debug_info`, `.debug_line`, CodeView `.debug$S`, and `.rodata` panic strings |
| Symbol hashes & CGU partitioning | `-C metadata=<seed>` + `-C codegen-units=1` | Fixes `StableCrateId` and prevents thread-scheduling variations across CGU splits |
| `.rlib` and `staticlib` archives | *(automatic in `ar_archive_writer`)* | `compiler/rustc_codegen_ssa/src/back/archive.rs` always writes `mtime = 0`, `uid = 0`, `gid = 0`, `mode = 0644` |
| PE/COFF headers & PDB paths (`*-pc-windows-*`) | `-C link-arg=/Brepro` + `-C link-arg=/PDBALTPATH:%_PDB%` (or `-Wl,--no-insert-timestamp` on MinGW) | Sets PE COFF `TimeDateStamp` and export/debug directory timestamps to deterministic hashes and strips absolute host paths from RSDS CodeView records |
| Mach-O `LC_UUID` & `OSO` stabs (`aarch64-apple-darwin`) | `-C link-arg=-Wl,-no_uuid` (or content-hashed UUID in `ld64.lld`) + `ZERO_AR_DATE=1` | Prevents timestamp-seeded `LC_UUID` and normalizes `N_OSO` object modification timestamps |
| ELF build ID (`*-unknown-linux-gnu`) | `-C link-arg=-Wl,--build-id=sha1` (or `none`) | Hashes output sections deterministically into `.note.gnu.build-id` |

## Boundaries

1. **No circumvention of proprietary SDK EULAs**: Tools such as `xwin` (which downloads
   Microsoft's CRT and Windows SDK `.cab`/`.msi` packages from Visual Studio manifests)
   and `osxcross` (which extracts `MacOSX.sdk` from Apple Xcode `.xip` archives) require
   accepting the Microsoft Visual Studio License Terms or the Apple Xcode and Apple SDKs
   Agreement, respectively. Clean-room Linux build environments must not invoke
   `xwin --accept-license` or redistribute extracted proprietary `.lib`/`.tbd` files
   without explicit organizational license clearance.
2. **Kernel vs user-mode emulation fidelity**: While `qemu-i386` and `qemu-aarch64`
   faithfully execute user-mode instructions, TLS (`tpidr_el0` / `%gs`), atomics, and
   DWARF unwinding, they forward system calls (`clone`, `futex`, `epoll`, `io_uring`)
   to the host `x86_64` Linux kernel and do not test target-specific kernel page sizes
   (such as 16 KiB pages on Apple Silicon or 64 KiB pages on some AArch64 servers unless
   `-pagesize` is configured).

## Evidence

- **Empirical cross-compilation and execution script & matrix**:
  `support/test_t11_recipes.py` and `support/t11_recipes_matrix.json` (verified `.o`/`.rlib`
  compilation across 8/8 targets, `no_std` `cdylib` cross-linking via `rust-lld` across
  Windows MSVC and macOS `arm64` with `LC_CODE_SIGNATURE` verification, and full `std`
  multi-threaded/unwinding build+run across `x86_64`, `i686`, and `aarch64` Linux).
- **Pinned `rustc 1.99.1` source citations**:
  - `src/ci/github-actions/jobs.yml:270-760` (upstream Tier 1 CI runner definitions)
  - `src/ci/docker/host-x86_64/dist-x86_64-linux/Dockerfile` and `dist-i686-linux/Dockerfile`
  - `src/ci/docker/host-aarch64/dist-aarch64-linux/Dockerfile`
  - `compiler/rustc_codegen_ssa/src/back/apple.rs:212-265` (`xcrun_show_sdk_path`)
  - `library/windows_link/src/lib.rs:1-52` (`raw-dylib` vs `windows.0.52.0`)
  - `library/unwind/src/lib.rs:1-100` (`libgcc_s` / `libunwind` linkage per target)

## Revalidation

Run `python3 support/test_t11_recipes.py` on an `x86_64-unknown-linux-gnu` host with
`rustc +1.99.1`, `qemu-i386`, `qemu-aarch64`, and an `aarch64-linux-gnu` sysroot
installed to re-verify all compilation, cross-linking, and user-mode execution recipes.
