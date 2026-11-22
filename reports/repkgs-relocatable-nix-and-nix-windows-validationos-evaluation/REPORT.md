# `repkgs` Relocatable ELF/Nix Package Set and `nix-windows-demo` ValidationOS Architecture

## Summary

1. **`repkgs` (`repkgs-org/repkgs@2f4a87bbbd450d3ad24cf99949bae021a3167788`, MIT)** is an experimental 213-package set (created `2026-09-10`) built on a patched Nix master fork (`Mic92/nix-1@e6c24e710343d0485995d1a67c6f4971d698bbca`, carrying `NixOS/nix#16459`, `#16465`, and `#16477`) requiring `ca-derivations`, `dynamic-derivations`, `recursive-nix`, and `builder-rpc-v0`. It combines structured Nushell builders, flat `callPackage`-style evaluation (`0.4 s` / `44 MB` across 175 shared packages vs. `10 s` / `570 MB` in `nixpkgs` per `docs/eval.md`), a host-daemon compiler cache (`jig` + `jigd`) exposed via an in-sandbox socket outside `.drv` input hashes, and store-path-free relocatable outputs.
2. **Freestanding ELF Relative-Interpreter Stub (`crt_interp` + `formatelf`)**: To eliminate absolute `/nix/store/.../ld-linux-*.so.*` `PT_INTERP` paths (which the Linux kernel resolves strictly relative to `/`, ignoring `$ORIGIN`) without coupling to the target machine's `/lib64/ld-linux-*.so.*` glibc version, `pkgs/cr/crt-interp/src/crt_interp.c` (`390` lines freestanding C across `x86_64`, `aarch64`, `riscv64`, `loongarch64`, and `ppc64le`) links or implants (`reloc_stub.bin` via `builder/implant.nu`) a custom entry point `__reloc_start` into dynamic PIEs with `PT_INTERP` flipped to `PT_NULL` on disk. At startup, `__reloc_start` resolves `/proc/self/exe` (falling back to `AT_EXECFN`), opens the relative `.interp` path from `dirname(/proc/self/exe)`, `mmap`s `ld.so`'s `PT_LOAD` segments, flips the in-memory program header back to `PT_INTERP`, patches `auxv` (`AT_BASE`, `AT_ENTRY`), and jumps to `ld.so` while preserving `/proc/self/exe`.
3. **Why `repkgs` Does Not Replace `ci-core` or `anneal/flake.nix`**:
   - *Standalone CI engine (`ci-core`)*: Static `musl` Rust + `bwrap` binaries already carry zero `PT_INTERP` and zero runtime Nix dependency, while `repkgs`'s `jigd` host-socket compiler cache and custom Nix daemon require persistent host daemon infrastructure incompatible with zero-daemon GitHub Actions sandboxes.
   - *Anneal toolchain packaging (`anneal/flake.nix`)*: `repkgs`'s 213 packages omit `lean4`, `elan`, `z3`, `cvc5`, `bubblewrap`, `ocaml` (listed under unbuilt ecosystems in `docs/plan.md`), `kani`, and `cbmc`. Furthermore, `pkgs/ru/rust/package.nix` builds `rustc` from source against `repkgs`'s shared `pkgs.llvm22` (`tests.run = false`) rather than preserving upstream `rustup` nightly distributions (`rustc_private` + `libLLVM` + `miri` ABI parity required by `anneal-rustc-capture`), and `anneal/flake.nix` (`omnibus-archive`) already emits a Nix-free `.tar.zst` archive. Only `crt_interp` / `formatelf` itself is a candidate standalone technique if `anneal-rustc-capture` ever needs bundled-glibc execution on older-glibc Linux hosts.
4. **`nix-windows-demo` (`nix-windows/nix-windows-demo@0f117ea0e3c2d463851d849a3ac7907554623d6e`) & Windows Readiness**:
   - `nix-windows-demo` cross-compiles `nix-windows/nix@d13b627ee439c0f5f1f90b5973d2bd0e5d680a44` (`x86_64-w64-mingw32`) on `x86_64-linux`, injects `nix.exe` plus a custom `stub-shell32.dll` (`SHGetKnownFolderPath` shim) into a ~1 GB Microsoft ValidationOS `.vhdx` via `guestfish`/`chntpw`, and boots QEMU to run `C:\nix\bin\nix-build C:\demo.nix` (`cmd.exe /c echo Hello`) and `nix-util-tests`/`nix-store-tests`. It does not provide native Windows `nixpkgs` or build sandboxing.
   - In `repkgs`, Windows is a Linux-hosted cross-compilation target (`clang` targeting MSVC ABI over Microsoft CRT/WinSDK), and `docs/plan.md` (`L122–123`, `L183–186`) explicitly lists Windows `.exe`/`.dll` install names, Cargo/Go targets, Wine test execution, and CMake `MSVC` detection (`clang-cl` / `CMAKE_C_SIMULATE_ID`) as unbuilt. Because Windows PE loader search natively checks the executable's directory first and both Rust (`x86_64-pc-windows-msvc`) and Lean 4 (`lean-*-windows.zip`) publish native relocatable Windows archives, Windows `cargo-anneal` packaging does not benefit from Nix on Windows (though ValidationOS on Linux/KVM is a viable license-free headless Windows test harness).

## Applicability

Applies to:
- `repkgs-org/repkgs` at commit `2f4a87bbbd450d3ad24cf99949bae021a3167788` (`2026-11-18`) and its pinned Nix fork `Mic92/nix-1` at `e6c24e710343d0485995d1a67c6f4971d698bbca`.
- `nix-windows/nix-windows-demo` at commit `0f117ea0e3c2d463851d849a3ac7907554623d6e` (`2026-11-20`) and `nix-windows/nix` (`windows-demo-1`) at `d13b627ee439c0f5f1f90b5973d2bd0e5d680a44`.
- `google/zerocopy` `anneal/flake.nix` at commit `907b9175fee081872ec883ca4709e6ad922f8ed0`.

Rapidly evolving experimental repositories (`repkgs` and `nix-windows`) may add packages or complete items listed in `docs/plan.md` on subsequent commits.

## Findings

### 1. `repkgs` Architecture, Daemon Requirements, and `jigd` Compiler Cache

`README.md`, `docs/design.md`, and `nix/nix/default.nix` in `repkgs-org/repkgs@2f4a87bbbd450d3ad24cf99949bae021a3167788` establish the following architectural commitments:
- **Custom Nix Daemon Requirement**: `nix/nix/default.nix` overrides `pkgs.nixVersions.git` to `Mic92/nix-1@e6c24e710343d0485995d1a67c6f4971d698bbca` (`NixOS/nix#16459` required so dynamic derivations rebuild after GC; `#16465` and `#16477` recommended for content-addressed rebuild traces) with `experimental-features = [ "nix-command" "ca-derivations" "dynamic-derivations" "recursive-nix" ]` and `system-features = [ "builder-rpc-v0" ... ]`.
- **Host-Socket Compiler Cache (`jig` / `jigd`)**: `jig` wraps `cc`, `c++`, and `rustc` on build `PATH` and communicates over an in-sandbox socket with per-machine daemon `jigd` outside `.drv` input hashes (`docs/design.md` `L6–21`, `docs/plan.md` `L168–177`). While `.drv` hashes stay invariant, cache hits depend on an external mutable host daemon rather than purely attested artifact inputs, and `docs/plan.md` `L170–172` notes that `bin` and `proc-macro` Rust crates are not yet cached in `rustc` mode.
- **Package Coverage and `rustc` Build Model**: Across `pkgs/*/*/package.nix`, `repkgs@2f4a87bb` defines `213` packages (`clang`, `llvm21`/`llvm22`, `rust`, `cpython314`, `git`, `jq`, `zstd`, etc.), with zero packages for `lean4`, `elan`, `z3`, `cvc5`, `bubblewrap`, `ocaml`, `kani`, or `cbmc`. In `pkgs/ru/rust/package.nix`, `rust` compiles from the upstream release tarball against `pkgs.llvm22` with `tests.run = false`, diverging from `anneal/flake.nix`'s requirement (`L47–51` at `907b9175fe`) that `anneal-rustc-capture` link against the exact unmodified upstream `rustup` nightly sysroot (`rustc_private` + `libLLVM`).

### 2. Freestanding ELF Relative-Interpreter Mechanism (`crt_interp` and `implant.nu`)

On Linux, the kernel ELF loader resolves `PT_INTERP` strictly from `/` and does not expand `$ORIGIN` inside `.interp`. In `anneal/flake.nix` (`L283–299` at `907b9175fe`), `omnibus-archive` copies `libz.so.1` and `libgcc_s.so.1` into `rust/lib/`, sets `RPATH` on `bin/anneal-rustc-capture` to `$ORIGIN/../rust/lib`, and sets `PT_INTERP` to the standard host path (`/lib64/ld-linux-x86-64.so.2` or `/lib/ld-linux-aarch64.so.1`)—eliminating any `/nix/store` runtime dependency on user machines while retaining a minimum host-glibc version requirement.

`repkgs` (`pkgs/cr/crt-interp/src/crt_interp.c` and `builder/implant.nu`) eliminates even the host-glibc path assumption:
1. Link-built dynamic PIEs link `crt_interp` (`-Wl,-e,__reloc_start`) with `PT_INTERP` flipped to `PT_NULL` on disk and a relative path to the bundled `ld.so` stored in `.interp`; prebuilt upstream ELFs (`rustc`, `bun`, `deno`) have `reloc_stub.bin` (`RELOCSTB` magic + original `e_entry`) implanted by `formatelf` (`builder/implant.nu` `L20–31`).
2. On execution, `__reloc_start` (`crt_interp.c` `L7–14`) reads `/proc/self/exe` (or `AT_EXECFN` when `/proc` is unmounted), opens `dirname + "/" + .interp`, `mmap`s `ld.so`, restores `p_type = PT_INTERP` in memory for glibc's startup assertions, rewrites `AT_BASE` and `AT_ENTRY` in the initial stack's auxiliary vector, and jumps to `ld.so` with `argv`/`envp` and `/proc/self/exe` intact.

### 3. `nix-windows-demo` ValidationOS Harness vs. `repkgs` Windows Cross-Target Status

- **`nix-windows-demo@0f117ea0e3c2d463851d849a3ac7907554623d6e` (`flake.nix`, `README.md`)**: Cross-compiles `nix-cli-x86_64-w64-mingw32` from `nix-windows/nix@d13b627ee439c0f5f1f90b5973d2bd0e5d680a44` using `pkgsCross.mingwW64` on `x86_64-linux`, compiles a minimal `windows/stub-shell32/` DLL implementing `SHGetKnownFolderPath` from environment variables (`LOCALAPPDATA`, `APPDATA`, `ProgramData`) because Microsoft ValidationOS omits `shell32.dll`, injects both offline into `ValidationOS.vhdx` via `guestfish` and `chntpw`, and runs QEMU checks verifying `nix-util-tests`, `nix-store-tests`, and `C:\nix\bin\nix-build C:\demo.nix` (`cmd.exe` echoing `Hello`).
- **`repkgs` Windows Cross-Compilation Maturity (`docs/design.md` `L25–27`, `docs/plan.md` `L122–123`, `L183–186`)**: Build hosts in `repkgs` are exclusively `x86_64-linux` and `aarch64-linux`. Windows is a cross target fetching Microsoft's CRT and Windows SDK (`builder/fetch/winsdk.nu`), and `docs/plan.md` explicitly records that Windows `.exe`/`.dll` install names, Cargo and Go Windows targets, Wine test execution, and CMake `MSVC` compiler-ID handling remain unimplemented.

## Boundaries

- Static source and API inspection only; neither `Mic92/nix-1` (`ca-derivations` + `dynamic-derivations` + `builder-rpc-v0`) nor `ValidationOS.vhdx` under QEMU was built or executed locally during this review.
- `crt_interp` interaction with Linux LSMs (AppArmor/SELinux `execmod` or `mmap` `PROT_EXEC` policies on non-`PT_INTERP` PIEs) and `bwrap` without `/proc` (`AT_EXECFN` relative-path corner cases when invoked via `PATH` or symlink) was not empirically probed on target kernels.

## Evidence

- `repkgs-org/repkgs@2f4a87bbbd450d3ad24cf99949bae021a3167788`: `README.md`, `docs/design.md`, `docs/plan.md`, `nix/nix/default.nix`, `pkgs/ru/rust/package.nix`, `pkgs/cr/crt-interp/src/crt_interp.c`, `builder/implant.nu`, and full recursive Git tree inventory (`213` package directories under `pkgs/`).
- `nix-windows/nix-windows-demo@0f117ea0e3c2d463851d849a3ac7907554623d6e`: `README.md`, `flake.nix`, and `nix-windows/nix@d13b627ee439c0f5f1f90b5973d2bd0e5d680a44` (`windows-demo-1`).
- `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0`: `anneal/flake.nix` (`omnibus-archive` staging, `dontPatchELF`, and `patchelf` `$ORIGIN` rewrite).

## Revalidation

```bash
gh api repos/repkgs-org/repkgs/commits/HEAD --jq '{sha: .sha, date: .commit.committer.date}'
gh api repos/repkgs-org/repkgs/git/trees/HEAD?recursive=1 --jq '[.tree[].path | select(startswith("pkgs/")) | split("/")[2]] | unique | length'
gh api repos/repkgs-org/repkgs/contents/docs/plan.md --jq '.content' | base64 -d | grep -n -i -E 'windows|ocaml'
gh api repos/nix-windows/nix-windows-demo/commits/HEAD --jq '{sha: .sha, date: .commit.committer.date}'
```
