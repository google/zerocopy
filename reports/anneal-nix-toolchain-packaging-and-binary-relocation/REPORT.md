# Anneal Nix Toolchain Packaging, Host-Platform Matrix, Fixed-Output Acquisition, Import-From-Derivation, and ELF/Mach-O Relocation

## Summary

This report synthesizes the Nix toolchain acquisition, evaluation-time metadata extraction, host-platform support matrix, Linux ELF / macOS Mach-O binary relocation architecture, and clean-environment Linux `x86_64` dynamic-loader qualification of Anneal across `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` and `joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b`:

1. **Four-Host Platform Intersection Matrix and Upstream Packaging Caveats**:
   Anneal's packaged-toolchain host intersection in `anneal/flake.nix` is exactly four systems (`x86_64-linux`, `aarch64-linux`, `x86_64-darwin`, `aarch64-darwin`), throwing on any other Nix `system`:

   | Nix host | Aeneas asset | Rust host triple | Lean archive platform | Native `leantar` (`0.1.16`) |
   | --- | --- | --- | --- | --- |
   | `x86_64-linux` | `aeneas-linux-x86_64.tar.gz` | `x86_64-unknown-linux-gnu` | `linux` | `x86_64-unknown-linux-musl` |
   | `aarch64-linux` | `aeneas-linux-aarch64.tar.gz` | `aarch64-unknown-linux-gnu` | `linux_aarch64` | `aarch64-unknown-linux-musl` |
   | `x86_64-darwin` | `aeneas-macos-x86_64.tar.gz` | `x86_64-apple-darwin` | `darwin` | `x86_64-apple-darwin` |
   | `aarch64-darwin` | `aeneas-macos-aarch64.tar.gz` | `aarch64-apple-darwin` | `darwin_aarch64` | `aarch64-apple-darwin` |

   Two upstream packaging anomalies are compensated by Anneal's flake:
   - *Charon Linux AArch64 interpreter defect*: In `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon-portable` unconditionally runs `patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 || true` on any Linux host, and Aeneas's release workflow (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`) only smoke-tests `./aeneas --help` (not bundled `charon`). Anneal's final Linux staging pass overwrites ELF interpreters per host (`/lib64/ld-linux-x86-64.so.2` on `x86_64-linux`, `/lib/ld-linux-aarch64.so.1` on `aarch64-linux`).
   - *Lean `v4.30.0-rc2` `linux_aarch64` wrong-architecture `leantar`*: Lean `v4.30.0-rc2`'s `linux_aarch64` archive bundles an x86-64 `leantar` binary; Anneal bypasses it by fetching native `leantar` `0.1.16` separately per host.

2. **Linux ELF Interpreter and RPATH Rewriting (`patchelf 0.15.2`)**:
   In `packages.omnibus-tar`, Linux builds run `find $TMPDIR/dist_staging -type f -executable`, filter for `ELF 64-bit` via `file`, replace any present `PT_INTERP` with the host glibc loader, clear RPATH via `patchelf --set-rpath ""`, and run `strip`. While downloaded Rust, Lean, and `leantar` fixed-output derivations preserve upstream bytes via `dontPatchShebangs = true; dontPatchELF = true; dontStrip = true`, the final `omnibus-tar` loop is **best-effort rather than fail-closed**: every mutating command uses `|| true`, non-executable ELF shared objects are skipped by `-executable`, `omnibus-archive-layout-check` does not inspect ELF headers, and clearing RPATH erases relative `$ORIGIN` lookup paths—requiring Anneal's runtime wrappers (`anneal/src/setup.rs`, `anneal/src/resolve.rs`, `anneal/src/main.rs`) to supply `LD_LIBRARY_PATH` (`rust/lib`, `lean/lib`, `lean/lib/lean`) and `PATH`.

3. **macOS Mach-O Relocation, `DYLD_LIBRARY_PATH`, and Code-Signing Boundaries**:
   Unlike Linux, `packages.omnibus-tar` has no `stdenv.isDarwin` binary-rewrite or code-signing pass. Relocatability on macOS relies on upstream component packaging plus Anneal's runtime environment: Aeneas's `mk-aeneas-release` runs `dylibbundler -od -b -x ./aeneas -d ./libs -p @executable_path/libs` on `./aeneas` (but not on `charon` or `charon-driver`), while Anneal sets `DYLD_LIBRARY_PATH` at invocation time to point into the installed Rust and Lean `lib` directories. Because Apple's code-signing rules (TN2206) invalidate signatures if executable bytes are modified after signing, any future Darwin `install_name_tool` or `strip` pass must re-sign modified Mach-O images afterward.

4. **Nix Fixed-Output Derivations (FODs) for Upstream Archives and Caches**:
   Anneal isolates network acquisition behind five per-platform SHA-256 FOD families: two single-file `pkgs.fetchurl` derivations (`fetchAeneas`, `fetchLeantar`) and three recursive NAR-hashed (`outputHashMode = "recursive"`) directory-tree derivations (`fetchRustToolchain`, `fetchLeanToolchain`, and `packages.mathlib-cache-download`). `mathlib-cache-download` runs `lake exe cache get-` to download `.ltar` files without decompressing them, strips `/nix/store`-bearing `.trace`/`.hash` files, `mathlib/.lake`, and `.git` directories, and hashes the sanitized tree; downstream `mathlib-cache-unpacked` and `aeneas-compiled` (`MATHLIB_NO_CACHE_ON_UPDATE=1`) are ordinary derivations. Execution on `aarch64-darwin` (Nix `2.35.2`) verified the Aeneas, Lean, and Rust FOD hashes and wrong-hash rejection controls, whereas `mathlib-cache-download` produced two distinct mismatched hashes across two runs.

5. **Import-From-Derivation (`packages.test-ifd`) and Relocated Toolchain-Tree Execution**:
   - *IFD evaluation boundary*: `packages.test-ifd` calls `builtins.fromJSON (builtins.readFile "${unpacked}/metadata.json")` on `packages.aeneas-unpacked`, forcing realization of `aeneas-unpacked` during evaluation (and failing if `allow-import-from-derivation = false`). Only `lean-toolchain` (`4.30.0-rc2`) is genuinely parsed from `$out/backends/lean/lean-toolchain`; `rust-toolchain-date` (`2026-05-31`) is copied from Anneal's static `rustDate` binding, expected `outputHash` values are copied from the static toolchain packages, and production `packages.{rust-toolchain,lean-toolchain,default}` bypass IFD entirely. `nix build .#test-ifd` succeeded on `aarch64-darwin` (`Dynamic IFD Verification Success!`).
   - *Relocated Rust and Lean FOD trees on `aarch64-darwin`*: Copying the realized `aarch64-darwin` Lean (`14,447` entries, `2.5 GiB`, NAR `sha256-dpUCCLkhoGDKkDKPZxr7WrmkifxHi4MWLpD148z2vhg=`) and Rust (`8,193` entries, `1.6 GiB`, NAR `sha256-X7ndqbjsmnjL6KZzNCxkVFJPzAsAjUqerD/wc1rxK5E=`) FOD trees outside `/nix/store` preserved identical NAR and inventory digests and successfully compiled and ran smoke programs (`support/nix-toolchain-tree-relocation/smoke.rs`, `support/nix-toolchain-tree-relocation/Smoke.lean`), with `otool -L` confirming relative `@rpath` load commands (`@loader_path/..` + `/lib` for Rust and `@executable_path/..` + `/lib` and `/lib/lean` for Lean).

6. **Linux `x86_64` Omnibus Relocation (`dontPatchELF = true`), `DT_RUNPATH` Non-Transitivity, and `bwrap --tmpfs /` Qualification (`joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b`)**:
   - *Targeted ELF patching vs. bulk `patchelf --set-rpath ""`*: In `joshlf/anneal`, `flake.nix` sets `dontPatchELF = true` on `packages.toolchain-omnibus`, preserving upstream relative `$ORIGIN/../lib` (`rust/bin/*`, `rust/lib/*.so`) and `$ORIGIN/../lib:$ORIGIN/../lib/lean` (`lean/bin/lean`) `DT_RUNPATH` entries while rewriting only `bin/anneal-rustc-capture` (`--set-interpreter /lib64/ld-linux-x86-64.so.2`, `--set-rpath '$ORIGIN/../rust/lib'`, `--add-needed libz.so.1`).
   - *Why `--add-needed libz.so.1` and section-mapped ELF auditing are required*: Unlike `DT_RPATH`, `DT_RUNPATH` in GNU `ld.so` (`elf/dl-load.c`) is non-transitive—it applies only to the direct `DT_NEEDED` children of the object declaring `DT_RUNPATH`. Adding `libz.so.1` as a direct `DT_NEEDED` entry on `bin/anneal-rustc-capture` ensures `libz.so.1` is loaded into the process link map before `librustc_driver-*.so` and `libLLVM.so.*` initialize. Furthermore, a section-mapped ELF scan (`support/linux-x86-64-clean-env-qualification/elf_audit.py`) shows that `bin/anneal-rustc-capture` contains `2,670` `/nix/store/...` substrings in `.rodata` (`panic!`/`Location::caller()` literals) and `.debug_*` sections that would trigger a naive whole-file `grep -F /nix/store`, while `lean/lib/{libz.so.1.2.11, libgcc_s.so.1, libatomic.so.1.2.0}` carry a dormant upstream `DT_RUNPATH` (`/nix/store/...-glibc-2.26-131/lib`). Notably, `patchelf --remove-rpath` alone deletes the `DT_RUNPATH` tag from `.dynamic` without erasing the string in `.dynstr`; running `patchelf --set-rpath ""` before `patchelf --remove-rpath` overwrites the `.dynstr` bytes with `'X'` padding and removes the tag.
   - *Shrinking the host shared-library floor from 8 SONAMEs to 6 core `glibc` SONAMEs and self-contained `--manifest-path`*: Inside an unprivileged `bwrap --tmpfs /` rootfs with **zero `/bin` or `/usr/bin` executables** and `PATH=""`, resolving `<installed>/rust/bin/cargo` (and `RUSTC=<installed>/rust/bin/rustc`) in `cargo_request()` makes `cargo-anneal verify --manifest-path` completely self-contained (`cargo metadata --format-version=1 --no-deps --offline` parses `Cargo.toml` in-process in `14 ms`). Adding relative symlinks `rust/lib/libz.so.1 -> ../../lean/lib/libz.so.1.2.11` and `rust/lib/libgcc_s.so.1 -> ../../lean/lib/libgcc_s.so.1` (plus `$ORIGIN/../lean/lib` or `-static-libgcc` for `cargo-anneal`, since prebuilt `libstd-*.rlib` carries `#[link(name = "gcc_s")]` even under `-C panic=abort`) shrinks the host shared-library surface from 8 SONAMEs (`ld-linux-x86-64.so.2`, `libc.so.6`, `libm.so.6`, `libpthread.so.0`, `libdl.so.2`, `librt.so.1`, `libgcc_s.so.1`, `libz.so.1`) to the **6 core `glibc` SONAMEs** (`ld-linux-x86-64.so.2`, `libc.so.6`, `libm.so.6`, `libpthread.so.0`, `libdl.so.2`, `librt.so.1`), which a 5-SONAME negative control (`librt.so.1` removed) proves is a tight lower bound.

7. **`GLIBC` Symbol Version Floor (`GLIBC_2.39` vs. `GLIBC_2.34` vs. `GLIBC_2.17`) and `VER_FLG_WEAK` Loader Semantics (`elf/dl-version.c`)**:
   - *Strong vs. weak symbol partition*: Across all 21 `libc.so.6` version nodes in `cargo-anneal`, the highest version referenced by any strong (`STB_GLOBAL`) symbol is **`GLIBC_2.34`** (`__libc_start_main`, `dlsym`, `pthread_*`), followed by `GLIBC_2.33` (`stat64`, `fstat64`, `lstat64`, `fstatat64`) and `GLIBC_2.32` (`pthread_getattr_np`). Seven nodes (`GLIBC_2.18`, `2.25`, `2.27`, `2.28`, `2.29`, `2.30`, and **`GLIBC_2.39`** for `pidfd_spawnp` / `pidfd_getpid`) are referenced **exclusively by `STB_WEAK` symbols** from `libstd`'s `weak!` / `syscall!` feature probes.
   - *Why `rust/bin/cargo` stops at `GLIBC_2.17` and `bin/anneal-rustc-capture` stops at `GLIBC_2.34`*: Upstream Rust CI linked `cargo` and `librustc_driver` against a `glibc 2.17` sysroot, leaving post-2.17 weak symbols **unversioned** (`ver_index = 0`) in `.dynsym`. `bin/anneal-rustc-capture` reuses `libstd` dynamically from `librustc_driver-*.so` and links only host `Scrt1.o` (`__libc_start_main@GLIBC_2.34`), whereas `cargo-anneal` links `libstd-*.rlib` statically against the build host's `libc.so.6` (`glibc 2.39+`).
   - *Linker `vna_flags` divergence and `ld.so` `stderr` warning hazard*: `LLD 22.1.6` (`rustc 1.98.0-nightly`) and `GNU ld.bfd 2.45` emit `Elf64_Vernaux.vna_flags = 0x0` on weak-only version nodes, causing `_dl_check_map_versions` (which never inspects `.dynsym`) to abort before `main()` with exit code `1` on `glibc < 2.39`. Newer `LLD 23.1.4` (`rustc 1.101.0-nightly`) sets `vna_flags = VER_FLG_WEAK (0x2)`, allowing `main()` to run and exit `0` on `glibc 2.34`..`2.38`, **but** because `elf/rtld.c:dl_main` calls `_dl_check_all_versions(..., verbose=1, ...)`, `ld.so` still prints `weak version 'GLIBC_2.39' not found` to `stderr` on every process start. Only unversioned `STB_WEAK` symbols (`ver_index = 0`, matching `rust/bin/cargo` or linking against a target-floor `glibc` sysroot) fall back to `NULL` with `exit_code = 0` and completely silent `stderr`.

## Applicability

These findings apply to:

- **Zerocopy Anneal**: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix` blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, `anneal/flake.lock` blob `92ac56b0a777d280f0a76e28f163b20ff6fb2003`, `anneal/src/setup.rs`, `anneal/src/resolve.rs`, `anneal/src/main.rs`, `anneal/v1/src/charon.rs`, `anneal/v1/src/aeneas.rs`, and `.github/workflows/anneal.yml`).
- **Anneal Standalone Omnibus Toolchain and CLI Runner**: `joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b` (`flake.nix`, `.github/workflows/ci.yml`, `.github/workflows/release.yml`, `trusted/cargo-anneal/src/{setup.rs,verify.rs}`), bundling `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly (2026-05-30)`) and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
- **Aeneas and Charon Packaging**: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`, `flake.nix` blob `05e71549416ac622d6f12edc1fc7c74e338949ba`, `.github/workflows/release.yml` blob `e248e9fdbecb3809f54ef58456db3faee448175f`) and `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`, `flake.nix` blob `844a2ca996e86acb053bbecd52ff251134341da8`, `rust-toolchain`).
- **Lean 4 and PatchELF / Nixpkgs**: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), and `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1` (`patchelf-0.15.2`, `pkgs/development/tools/misc/patchelf/default.nix` blob `086e18e941858c130e684a5476d2f2bc681a4eea`).
- **Host Execution Environments**: `aarch64-darwin` (Apple Silicon, Darwin `25.6.0`, 8 GiB RAM, Nix `2.35.2`) for FOD, IFD, and macOS tree-relocation runs on 2026-09-27; and `x86_64-linux` (Linux `6.17.11`, GNU `glibc 2.42`, `bwrap` user-namespace sandboxes) for ELF dynamic-loader, `bwrap --tmpfs /` zero-executable rootfs, and `DT_VERNEED` qualification runs on 2026-11-12.

Host-platform support in `anneal/flake.nix` governs the machine architecture on which `rustc`, `charon`, `aeneas`, `lean`, and `lake` execute; it must not be confused with the cross-compilation `targets` list inside Charon's `rust-toolchain` file (which includes Windows, i686 Linux, PowerPC64 Linux, and RISC-V bare-metal standard library targets).

## Findings

### 1. Host-Platform Support Matrix (`anneal/flake.nix` vs. Upstream Releases)

#### 1.1 Explicit four-system dispatch and intersection rule
`anneal/flake.nix` defines four platform-mapping tables (`rustPlatform`, `leanPlatform`, `aeneasTarget`, `leantarPlatform`) and corresponding four-way SHA-256 tables across `x86_64-linux`, `aarch64-linux`, `x86_64-darwin`, and `aarch64-darwin`, terminating with `else throw "Unsupported system: ${system}"`. Thus Anneal's supported host set is the strict intersection of hosts possessing mappings and fixed-output hashes across Aeneas, Rust, Lean, `leantar`, and Mathlib cache materialization ([`support/host-platform-matrix/host-matrix.json`](support/host-platform-matrix/host-matrix.json), [`support/host-platform-matrix/source-map.json`](support/host-platform-matrix/source-map.json)).

#### 1.2 Upstream Aeneas release matrix, smoke-test scope, and asymmetric binary packaging
At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `.github/workflows/release.yml` builds four matching archives:
- `aeneas-linux-x86_64` (self-hosted Linux/Nix, Nix package `aeneas-static-release`),
- `aeneas-linux-aarch64` (`ubuntu-24.04-arm`, Nix package `aeneas-static-release`),
- `aeneas-macos-x86_64` (`macos-15-intel`, Nix package `aeneas-release`),
- `aeneas-macos-aarch64` (`macos-latest`, Nix package `aeneas-release`).

Each job precompiles the Lean backend (`leanprover/lean4:v4.30.0-rc2`), packages `aeneas-{platform}.tar.gz`, and runs `./aeneas --help` as a smoke test. However, the workflow does **not** smoke-test the bundled `charon` or `charon-driver` binaries copied from Charon's `charon-portable` derivation.

#### 1.3 Linux AArch64 `charon-portable` interpreter bug and Lean `linux_aarch64` `leantar` workaround
Two architecture-specific upstream defects affect `aarch64-linux`:
1. In `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`flake.nix`), `charon-portable` checks only whether the host system string contains `linux` and runs `patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 || true`. Anneas's final Linux staging loop in `anneal/flake.nix` repairs this by setting `/lib64/ld-linux-x86-64.so.2` on `x86_64-linux` and `/lib/ld-linux-aarch64.so.1` on `aarch64-linux`.
2. Because Lean `v4.30.0-rc2`'s `linux_aarch64` distribution archive bundles an x86-64 `leantar` executable, Anneal fetches native `leantar` `0.1.16` (`x86_64-unknown-linux-musl`, `aarch64-unknown-linux-musl`, `x86_64-apple-darwin`, `aarch64-apple-darwin`) separately for unpacking Mathlib `.ltar` cache archives.

Basis: **source** in `anneal/flake.nix`, `AeneasVerif/aeneas` (`flake.nix`, `.github/workflows/release.yml`), and `AeneasVerif/charon` (`flake.nix`, `rust-toolchain`).

---

### 2. Linux ELF Interpreter and RPATH Relocation (`patchelf 0.15.2`)

#### 2.1 Producer staging rewrite vs. byte-preserved FOD downloads
In `anneal/flake.nix`, `fetchToolchainAsset` (used for Rust and Lean) and `fetchLeantar` set `dontPatchShebangs = true; dontPatchELF = true; dontStrip = true` so their fixed-output store trees remain byte-identical to upstream archives independent of Nix's `stdenv` fixup phase (`pkgs/stdenv/generic/setup.sh`). By contrast, `aeneas-unpacked` is an ordinary derivation without those flags.

In `packages.omnibus-tar`, when `pkgs.stdenv.isLinux` holds, Anneal walks `find $TMPDIR/dist_staging -type f -executable` and for every file whose `file` output contains `ELF 64-bit`:
1. checks `patchelf --print-interpreter`; if present, runs `patchelf --set-interpreter <host-loader> || true` (`/lib64/ld-linux-x86-64.so.2` or `/lib/ld-linux-aarch64.so.1`);
2. runs `patchelf --set-rpath "" || true`;
3. runs `strip || true`.

Basis: **source** in `anneal/flake.nix` and `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1` ([`support/linux-elf-relocation/source-map.json`](support/linux-elf-relocation/source-map.json), [`support/linux-elf-relocation/relocation-contract.json`](support/linux-elf-relocation/relocation-contract.json)).

#### 2.2 Consequences of unconditional `--set-rpath ""` and best-effort guards
Calling `patchelf --set-rpath ""` removes not only `/nix/store/...` entries but also any relative `$ORIGIN` RPATH entries (such as `$ORIGIN/..` + `/lib`) that an upstream portable binary might rely on to locate private shared libraries. Consequently, the extracted binaries are not standalone under an empty environment; Anneal's runtime invocation wrappers (`anneal/src/setup.rs`, `anneal/src/resolve.rs`, `anneal/src/main.rs`, `anneal/v1/src/charon.rs`, `anneal/v1/src/aeneas.rs`) explicitly inject `LD_LIBRARY_PATH` pointing to installed `rust/lib`, `lean/lib`, and `lean/lib/lean` alongside `LEAN_SYSROOT`, `CHARON_TOOLCHAIN_IS_IN_PATH=1`, and `PATH`.

Moreover, because `-executable` skips non-executable `.so` files, every command is suffixed with `|| true`, and `omnibus-archive-layout-check` inspects only tar member names, the build does not fail-closed if an ELF object retains a `/nix/store` RPATH or wrong interpreter.

Basis: **source** and **derived** analysis ([`support/linux-elf-relocation/relocation-contract.json`](support/linux-elf-relocation/relocation-contract.json)).

---

### 3. macOS Mach-O Relocation, Runtime `DYLD_LIBRARY_PATH`, and Code Signing

#### 3.1 Component-level Mach-O relocation vs. absence of final omnibus Darwin pass
`packages.omnibus-tar` has no `stdenv.isDarwin` binary-rewrite branch: it does not invoke `install_name_tool`, `dylibbundler`, `codesign`, or `otool`. Instead, macOS relocation is determined by:
- **Aeneas (`mk-aeneas-release`)**: on Darwin, runs `dylibbundler -od -b -x ./aeneas -d ./libs -p @executable_path/libs` to bundle non-system dylibs under `./libs` and rewrite `./aeneas`'s `LC_LOAD_DYLIB` commands to `@executable_path/libs/...`.
- **Charon (`charon-portable`)**: contains only a Linux `patchelf` branch and no Darwin branch, and Aeneas's `dylibbundler` invocation targets only `-x ./aeneas`, not `./charon` or `./charon-driver`.
- **Anneal runtime environment**: sets `DYLD_LIBRARY_PATH` on macOS to the installed Rust `lib` directory (for Charon/Cargo/rustc) and to `lean/lib` and `lean/lib/lean` (for Lean/Lake/Aeneas).

#### 3.2 Ordering constraint between Mach-O load-command mutation and code signing
Per Apple's Mach-O dynamic loader documentation and Technical Note TN2206, `install_name_tool` or `strip` mutates executable bytes and invalidates any existing embedded `LC_CODE_SIGNATURE` on arm64/x86-64 macOS. Any future Darwin relocation pass in `omnibus-tar` must perform all load-command mutations first, run `codesign -f -s -` (or distribution signing) second, and verify signatures on the final staged bytes before archiving.

Basis: **source** and **documentation** ([`support/macos-macho-relocation/source-map.json`](support/macos-macho-relocation/source-map.json), [`support/macos-macho-relocation/relocation-contract.json`](support/macos-macho-relocation/relocation-contract.json)).

---

### 4. Nix Fixed-Output Derivations (FODs) and `aarch64-darwin` Execution Observations

#### 4.1 Five fixed-output boundaries in `anneal/flake.nix`
Anneal separates network materialization from build transformation using five FOD families documented in [`support/nix-fixed-output-downloads/fod-inventory.json`](support/nix-fixed-output-downloads/fod-inventory.json):
1. `fetchAeneas`: `pkgs.fetchurl` flat-file hash over `aeneas-${target}.tar.gz`.
2. `fetchRustToolchain`: `fetchToolchainAsset` (`outputHashMode = "recursive"`, `outputHashAlgo = "sha256"`) hashing the merged sysroot of `cargo`, `rustc`, `rust-std`, `rustc-dev`, `llvm-tools`, `miri`, and `rust-src` for `2026-05-31`.
3. `fetchLeanToolchain`: `fetchToolchainAsset` (`outputHashMode = "recursive"`) hashing the extracted Lean `v4.30.0-rc2` directory tree.
4. `fetchLeantar`: `pkgs.fetchurl` flat-file hash over the `leantar` `0.1.16` archive.
5. `packages.mathlib-cache-download`: recursive FOD running `lake exe cache get-` (which downloads linked `.ltar` files into `$TMPDIR/.cache/mathlib` and materializes `.lake/packages` without decompressing `.ltar` archives), deleting `/nix/store`-bearing `.trace`/`.hash` files, `mathlib/.lake`, and `.git` directories before NAR hashing. Downstream `packages.mathlib-cache-unpacked` (expanding `.ltar` via `leantar` and touching to epoch) and `packages.aeneas-compiled` (`MATHLIB_NO_CACHE_ON_UPDATE=1`) are ordinary derivations.

#### 4.2 Direct `aarch64-darwin` execution verification (Nix `2.35.2`)
On 2026-09-27 on `aarch64-darwin` ([`support/nix-fixed-output-downloads/execution-observations.json`](support/nix-fixed-output-downloads/execution-observations.json)):
- `fetchAeneas`, `fetchLeanToolchain`, and `fetchRustToolchain` matched their declared `aarch64-darwin` SHA-256 hashes, and negative controls with intentionally mutated hashes were rejected by Nix with explicit expected-vs-actual hash errors.
- `packages.mathlib-cache-download` failed twice with two different actual recursive hashes across the two runs for the same pinned manifest, blocking downstream `mathlib-cache-unpacked` and `omnibus-tar` realization on that host.

Basis: **source**, **documentation**, and **execution** ([`support/nix-fixed-output-downloads/fod-inventory.json`](support/nix-fixed-output-downloads/fod-inventory.json), [`support/nix-fixed-output-downloads/execution-observations.json`](support/nix-fixed-output-downloads/execution-observations.json), [`support/nix-fixed-output-downloads/source-map.json`](support/nix-fixed-output-downloads/source-map.json)).

---

### 5. Nix Import-From-Derivation (`packages.test-ifd`) and Toolchain-Tree Relocation

#### 5.1 `packages.test-ifd` data flow and evaluator phase coupling
In `anneal/flake.nix`, `packages.aeneas-unpacked` unpacks the Aeneas archive, strips `leanprover/lean4:v` from `$out/backends/lean/lean-toolchain` (`4.30.0-rc2`), injects `RUST_DATE=${rustDate}` (`2026-05-31`) from the flake's static binding, and writes `$out/metadata.json` with three fields (`lean-toolchain`, `rust-toolchain-date`, `rust-toolchain-version`). `packages.test-ifd` then evaluates:

```nix
unpacked = self.packages.${system}.aeneas-unpacked;
aeneasMetadata = builtins.fromJSON (builtins.readFile "${unpacked}/metadata.json");
```

and constructs `dynamicRust` and `dynamicLean` reusing `self.packages.${system}.rust-toolchain.outputHash` and `self.packages.${system}.lean-toolchain.outputHash`. Thus:
- Reading `"${unpacked}/metadata.json"` triggers Nix IFD, pausing evaluation to realize `aeneas-unpacked` and failing under `allow-import-from-derivation = false`.
- Only `leanVersion` is genuinely extracted from the Aeneas archive; `rustDate` is round-tripped from the flake's static binding, and `outputHash` values remain static.
- Normal packages (`packages.rust-toolchain`, `packages.lean-toolchain`, `packages.default`) do not use IFD.
- Running `nix build .#test-ifd` on `aarch64-darwin` (Nix `2.35.2`) succeeded and emitted `Dynamic IFD Verification Success!` ([`support/nix-ifd-version-extraction/execution-results.json`](support/nix-ifd-version-extraction/execution-results.json), [`support/nix-ifd-version-extraction/execution/test-ifd-build.txt`](support/nix-ifd-version-extraction/execution/test-ifd-build.txt)).

Basis: **source**, **documentation**, and **execution** ([`support/nix-ifd-version-extraction/metadata-flow.json`](support/nix-ifd-version-extraction/metadata-flow.json), [`support/nix-ifd-version-extraction/source-map.json`](support/nix-ifd-version-extraction/source-map.json)).

#### 5.2 Relocating the Nix-packaged Rust and Lean FOD trees on `aarch64-darwin`
Using [`support/nix-toolchain-tree-relocation/relocate.py`](support/nix-toolchain-tree-relocation/relocate.py), the realized `aarch64-darwin` store outputs `/nix/store/wf1mr6pak9n88v5bwm6y749d8k19r0mw-lean-toolchain-aarch64-darwin-4.30.0-rc2` and `/nix/store/ms2vns33wg2qxzqdfdw37w6g9xay9jjc-rust-toolchain-aarch64-darwin` were copied via `cp -a` to a directory outside `/nix/store`:

| Toolchain Tree | NAR SHA-256 (`nix hash path --type sha256`) | Inventory Entries & Digest | Size |
| --- | --- | --- | --- |
| Lean `4.30.0-rc2` | `sha256-dpUCCLkhoGDKkDKPZxr7WrmkifxHi4MWLpD148z2vhg=` | `14,447` entries (`0` symlinks); SHA-256 `77c2af70d52e0f6c48d429def71b9aa495a34e98a5d5d2f1c57a27680b89460a` | `2.5 GiB` |
| Rust `nightly` | `sha256-X7ndqbjsmnjL6KZzNCxkVFJPzAsAjUqerD/wc1rxK5E=` | `8,193` entries (`0` symlinks); SHA-256 `d94ef08200855aa736c74040bca79a50b432b5396a140abc4c972d9097e1d388` | `1.6 GiB` |

From the relocated copies:
- `rustc --version` reported `1.98.0-nightly (f8a08b688 2026-05-30)`, `cargo --version` reported `1.98.0-nightly (fbb61be30 2026-05-26)`, and compiling and running [`support/nix-toolchain-tree-relocation/smoke.rs`](support/nix-toolchain-tree-relocation/smoke.rs) printed `relocated rust ok`.
- `lean --version` reported `4.30.0-rc2`, `lake --version` reported `5.0.0-src+3dc1a08`, and `lean --run` on [`support/nix-toolchain-tree-relocation/Smoke.lean`](support/nix-toolchain-tree-relocation/Smoke.lean) printed `relocated lean ok`.
- `otool -L` confirmed that the copied `rustc` uses `@rpath/librustc_driver-c20cab87d43f5461.dylib` with `@loader_path/..` + `/lib` RPATH, and the copied `lean` executable uses `@rpath` Lean libraries with `@executable_path/..` + `/lib` and `@executable_path/..` + `/lib/lean` RPATHs.

Basis: **execution** ([`support/nix-toolchain-tree-relocation/relocation-observations.json`](support/nix-toolchain-tree-relocation/relocation-observations.json), [`support/nix-toolchain-tree-relocation/source-map.json`](support/nix-toolchain-tree-relocation/source-map.json)).

---

### 6. Linux `x86_64` Omnibus Archive Relocation (`dontPatchELF = true`), `DT_RUNPATH` Non-Transitivity, and `bwrap --tmpfs /` Qualification (`joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b`)

#### 6.1 Targeted `patchelf` + `dontPatchELF = true` vs. bulk `patchelf --set-rpath ""`
Whereas `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` ran a bulk `patchelf --set-rpath ""` loop over all executable ELF files in `dist_staging` (requiring runtime `LD_LIBRARY_PATH` wrappers), `joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b` sets `dontPatchELF = true` on `packages.toolchain-omnibus` (`flake.nix:604-612`). This preserves the upstream relative `$ORIGIN` `DT_RUNPATH` tags inside `rust/bin/*` (`$ORIGIN/../lib`), `rust/lib/*.so` (`$ORIGIN/../lib`), `lean/bin/*` (`$ORIGIN/../lib:$ORIGIN/../lib/lean`), and `lean/lib/lean/*.so` (`$ORIGIN:$ORIGIN/..`) while patching only the Nix-built `bin/anneal-rustc-capture` binary (`flake.nix:489-504`):
1. `--set-interpreter /lib64/ld-linux-x86-64.so.2`,
2. `--set-rpath '$ORIGIN/../rust/lib'`, and
3. `--add-needed libz.so.1`.

#### 6.2 Non-transitivity of `DT_RUNPATH` for `libLLVM.so -> libz.so.1` and section-mapped ELF auditing
Why does `bin/anneal-rustc-capture` require `patchelf --add-needed libz.so.1` even though `rust/lib/libLLVM.so.22.1-rust-1.98.0-nightly` already declares `DT_NEEDED: libz.so.1`?
- In GNU `ld.so` (`elf/dl-load.c:_dl_map_object`), `DT_RPATH` (deprecated) is inherited transitively by all indirect dependencies, whereas **`DT_RUNPATH` is non-transitive**—it searches only the `DT_RUNPATH` of the immediate object requesting a `DT_NEEDED` child.
- When `bin/anneal-rustc-capture` is built inside Nix, Nix's linker wrapper initially sets `DT_RUNPATH` on `anneal-rustc-capture` to include Nix's `zlib` store path. Once `anneal-rustc-capture`'s `DT_RUNPATH` is rewritten to `$ORIGIN/../rust/lib`, `libLLVM.so` (loaded indirectly via `librustc_driver-5d5a3c5207375ffc.so`) searches its own `DT_RUNPATH` (`$ORIGIN/../lib`, which resolves to `rust/lib/`, where no `libz.so.1` exists in the unhardened archive) and then the host default search path. Adding `libz.so.1` as a direct `DT_NEEDED` entry on `bin/anneal-rustc-capture` forces `ld.so` to resolve and map `libz.so.1` into the global link map at executable startup before `librustc_driver` and `libLLVM` load.

Using [`support/linux-x86-64-clean-env-qualification/elf_audit.py`](support/linux-x86-64-clean-env-qualification/elf_audit.py) ([`support/linux-x86-64-clean-env-qualification/elf_audit.json`](support/linux-x86-64-clean-env-qualification/elf_audit.json)), a section-mapped audit of all 106 ELF files inside `anneal-toolchain-x86_64-unknown-linux-gnu.tar.zst` (`564,613,562` bytes, SHA-256 `e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a`, unpacked `2,554,321,880` bytes across `7,853` files) established three structural facts:
1. **Why raw whole-file `grep -F /nix/store` fails on `bin/anneal-rustc-capture`**: `bin/anneal-rustc-capture` has zero `/nix/store` bytes in `PT_INTERP` or `.dynstr`, but contains `2,670` `/nix/store/...` substrings in `.rodata` (`panic!` / `Location::caller()` source paths), `.debug_str`, `.debug_line_str`, `.strtab`, and `.comment`. A release check (`flake.nix:615-635` / `.github/workflows/release.yml:87-96`) must therefore inspect `readelf -l` (`PT_INTERP`) and `readelf -d` (`DT_RPATH`/`DT_RUNPATH`), not raw file bytes on unstripped Rust binaries.
2. **Dormant `/nix/store` `DT_RUNPATH` in `lean/lib/*.so` and `patchelf` `.dynstr` scrubbing**: Three shared libraries shipped by upstream Lean (`lean/lib/libz.so.1.2.11`, `lean/lib/libgcc_s.so.1`, and `lean/lib/libatomic.so.1.2.0`) carry `DT_RUNPATH = /nix/store/hwwqshlmazzjzj7yhrkyjydxamvvkfd3-glibc-2.26-131/lib`. Running `patchelf --remove-rpath` removes the `DT_RUNPATH` tag from `.dynamic` but leaves the `/nix/store/...` string intact in `.dynstr`; running `patchelf --set-rpath ""` *before* `patchelf --remove-rpath` overwrites the `.dynstr` bytes with `'X'` padding and removes the tag, leaving zero `/nix/store` bytes in `lean/lib/*.so`.
3. **Origin of the host `.rustup` `DT_RUNPATH` in `cargo-anneal`**: `trusted/cargo-anneal` has no `rustc_private` dependency or `build.rs`, yet the host-built `cargo-anneal` binary carried `DT_RUNPATH = <host-home>/.rustup/toolchains/nightly-2026-05-31-x86_64-unknown-linux-gnu/lib` because `.github/workflows/ci.yml:186-204` exports `RUSTFLAGS="-Lnative=${SYSROOT}/lib -Clink-arg=-Wl,-rpath,${SYSROOT}/lib"` globally for `anneal-rustc-capture` before building `cargo-anneal`. Building `cargo-anneal` with `env -u RUSTFLAGS` produces zero `DT_RPATH`/`DT_RUNPATH` entries.

#### 6.3 Self-contained `verify --manifest-path` and shrinking the host shared-library surface from 8 SONAMEs to 6 core `glibc` SONAMEs
In `trusted/cargo-anneal/src/verify.rs:260`, `cargo_request()` invoked bare `Command::new("cargo")` before `ensure_toolchain_installed()`, causing `verify --manifest-path` to fail (`exit 2`, `phase: "config"`) in an environment without a host `cargo` binary on `PATH`. Because the omnibus archive already bundles `<installed>/rust/bin/cargo` (`DT_RUNPATH: $ORIGIN/../lib`) and `<installed>/rust/bin/rustc`, resolving `<installed>/rust/bin/cargo` via `setup::find_installed_toolchain()` and passing `RUSTC=<installed>/rust/bin/rustc` makes `verify --manifest-path` completely self-contained: `cargo metadata --format-version=1 --no-deps --offline` parses `Cargo.toml` in-process in `14 ms` (`resolve: null`) without spawning `rustc` or requiring any additional host executables or shared libraries.

Furthermore, adding two relative symlinks (`rust/lib/libz.so.1 -> ../../lean/lib/libz.so.1.2.11` and `rust/lib/libgcc_s.so.1 -> ../../lean/lib/libgcc_s.so.1`, plus `$ORIGIN/../lean/lib` on `bin/anneal-rustc-capture`) routes every bundled binary to the archive's own `libz.so.1` and `libgcc_s.so.1`. We executed 30 qualification runs across [`support/linux-x86-64-clean-env-qualification/run_clean_env_qualification.py`](support/linux-x86-64-clean-env-qualification/run_clean_env_qualification.py) and [`support/linux-x86-64-clean-env-qualification/run_track_d_qualification.py`](support/linux-x86-64-clean-env-qualification/run_track_d_qualification.py) inside an unprivileged `bwrap --tmpfs /` rootfs with **zero `/bin` or `/usr/bin` executables** and `PATH=""`:

| Check ID | Host SONAMEs Mounted in `/lib64` & `/lib/x86_64-linux-gnu` | Bundle & CLI Configuration | Verification Target | Exit Code | Elapsed (`ms`) | Observed Outcome |
| :--- | :---: | :--- | :--- | :---: | :---: | :--- |
| **Suite 2 `2.2` / `2.4`** | 8 (`glibc` 6 + `libgcc_s.so.1` + `libz.so.1`) | Unhardened bundle + baseline `cargo-anneal` | `scalar-pos` (`--request`) & Starnix (`--request`) | `0` | `15,876` / `45,872` | `status: "crate_verified"`, `exactType: true` (`0` `/nix`, `.rustup`, or `.elan` loads under `LD_DEBUG=libs`) |
| **`D1.1` / `D1.2`** | 8 (`glibc` 6 + `libgcc_s.so.1` + `libz.so.1`) | Unhardened bundle + `cargo-anneal-patched` (no RPATH, bundled `cargo`) | `scalar-cargo` (`--manifest-path`) | `0` | `20,903` (`14` for `cargo metadata`) | `status: "crate_verified"`, `exactType: true` |
| **`D2-7.0`** | 7 (`libz.so.1` removed from host) | **Unhardened** bundle + `cargo-anneal-patched` (negative control) | `scalar-pos` (`--request`) | `2` | `31` | Fails in `capture`: `bin/anneal-rustc-capture: error while loading shared libraries: libz.so.1: cannot open shared object file` |
| **`D2-7.1`..`D2-7.5`** | 7 (`libz.so.1` removed from host) | **Hardened** bundle + `cargo-anneal-patched` (no RPATH) | `scalar-pos`, `scalar-cargo` (`--manifest-path`), `neg-spec`, `neg-proof`, `neg-unsupp` | `0` / `0` / `1` / `1` / `1` | `13,789` / `14,000` / `14,475` / `13,803` / `46` | Both positive runs verify (`crate_verified`); all 3 negative mutations rejected at `proof`, `audit` (`sorryAx`), and `model` |
| **`D2-6.0`** | 6 (`glibc` only; `libz` & `libgcc_s` removed) | **Hardened** bundle + `cargo-anneal-patched` (no RPATH; negative control) | `scalar-pos` (`--request`) | `127` | `4` | `cargo-anneal` itself fails at `ld.so` startup: `libgcc_s.so.1: cannot open shared object file` (prebuilt `libstd-*.rlib` carries `#[link(name = "gcc_s")]` even under `-C panic=abort`) |
| **`D2-6.1`..`D2-6.5`** | **6 (`glibc` only: `ld-linux-x86-64.so.2`, `libc.so.6`, `libm.so.6`, `libpthread.so.0`, `libdl.so.2`, `librt.so.1`)** | **Hardened** bundle + `cargo-anneal-rpath-bundle` | `scalar-pos`, `scalar-cargo` (`--manifest-path`), `neg-spec`, `neg-proof`, `neg-unsupp` | `0` / `0` / `1` / `1` / `1` | `14,768` / `13,951` / `13,949` / `14,033` / `40` | All 5 verification modes succeed with **only the 6 core `glibc` libraries** on the host |
| **`D2-6.6`** | 5 (`librt.so.1` also removed from host) | **Hardened** bundle + `cargo-anneal-rpath-bundle` (lower-bound control) | `scalar-pos` (`--request`) | `2` | `19` | Fails in `capture`: `bin/anneal-rustc-capture: error while loading shared libraries: librt.so.1: cannot open shared object file` |

Basis: **source** and **execution** ([`support/linux-x86-64-clean-env-qualification/elf_audit.json`](support/linux-x86-64-clean-env-qualification/elf_audit.json), [`support/linux-x86-64-clean-env-qualification/clean_env_qualification_results.json`](support/linux-x86-64-clean-env-qualification/clean_env_qualification_results.json), [`support/linux-x86-64-clean-env-qualification/track_d_q1_q2_results.json`](support/linux-x86-64-clean-env-qualification/track_d_q1_q2_results.json)).

---

### 7. `GLIBC` Symbol Version Floor (`GLIBC_2.39` vs. `GLIBC_2.34` vs. `GLIBC_2.17`) and `VER_FLG_WEAK` Loader Semantics (`elf/dl-version.c`)

#### 7.1 Strong (`STB_GLOBAL`) vs. weak (`STB_WEAK`) `libc.so.6` version bindings across the toolchain
Using [`support/linux-x86-64-clean-env-qualification/probe_glibc_verneed.py`](support/linux-x86-64-clean-env-qualification/probe_glibc_verneed.py) ([`support/linux-x86-64-clean-env-qualification/track_d_q3_verneed_results.json`](support/linux-x86-64-clean-env-qualification/track_d_q3_verneed_results.json)), we parsed `.dynsym`, `.gnu.version`, and `.gnu.version_r` (`DT_VERNEED`) across all toolchain executables, shared libraries, and four compiler/linker builds of `cargo-anneal`:

| Binary / Shared Object | Compiler & Linker (`.comment`) | Highest `libc.so.6` Version (Any) | Effective `ld.so` Startup Floor (`vna_flags == 0`) | Highest Strong (`STB_GLOBAL`) Version | Weak-Only `libc.so.6` Version Nodes (`GLIBC_2.18`, `2.25`, `2.27`, `2.28`, `2.29`, `2.30`, `2.39`) |
| :--- | :--- | :---: | :---: | :---: | :--- |
| `cargo-anneal` (pinned toolchain + `rust-lld`) | `rustc 1.98.0-nightly` + `LLD 22.1.6` | `GLIBC_2.39` | **`GLIBC_2.39`** | **`GLIBC_2.34`** | Emitted with **`vna_flags = 0x0` (`none`)** |
| `cargo-anneal` (pinned toolchain + host `ld.bfd`) | `rustc 1.98.0-nightly` + `GNU ld.bfd 2.45` | `GLIBC_2.39` | **`GLIBC_2.39`** | **`GLIBC_2.34`** | Emitted with **`vna_flags = 0x0` (`none`)** |
| `cargo-anneal` (newer nightly + `rust-lld`) | `rustc 1.101.0-nightly` + `LLD 23.1.4` | `GLIBC_2.39` | **`GLIBC_2.34`** | **`GLIBC_2.34`** | Emitted with **`vna_flags = 0x2` (`VER_FLG_WEAK`)** |
| `bin/anneal-rustc-capture` | `rustc 1.98.0-nightly` + `GCC 15.2.0` (Nix) | `GLIBC_2.34` | **`GLIBC_2.34`** | **`GLIBC_2.34`** | *(none; `libstd` is linked dynamically via `librustc_driver`)* |
| `rust/bin/cargo` & `rust/bin/rustc` | Upstream Rust CI (`glibc 2.17` sysroot) | `GLIBC_2.17` | **`GLIBC_2.17`** | **`GLIBC_2.17`** | *(none; post-2.17 syscalls are unversioned `STB_WEAK` with `ver_index = 0`)* |
| `rust/lib/librustc_driver-5d5a3c5207375ffc.so` & `libLLVM.so` | Upstream Rust CI (`glibc 2.17` sysroot) | `GLIBC_2.16` | **`GLIBC_2.16`** | **`GLIBC_2.16`** | *(none; post-2.17 syscalls are unversioned `STB_WEAK` with `ver_index = 0`)* |
| `lean/bin/lean` & `lean/lib/lean/libleanshared.so` | `Clang 22.1.4` + `LLD 22.1.4` | `GLIBC_2.17` | **`GLIBC_2.17`** | **`GLIBC_2.17`** | *(none)* |
| `lean/lib/{libz.so.1.2.11, libgcc_s.so.1}` | `GCC 7.3.0` | `GLIBC_2.14` | **`GLIBC_2.14`** | **`GLIBC_2.14`** | *(none)* |

In `cargo-anneal`, the strong (`STB_GLOBAL`) symbols above `GLIBC_2.17` are `pthread_getattr_np@GLIBC_2.32`, `stat64`/`fstat64`/`lstat64`/`fstatat64@GLIBC_2.33`, and `__libc_start_main`/`dlsym`/`pthread_*@GLIBC_2.34` (from the build host's `Scrt1.o` and `glibc 2.34`'s `libpthread`/`libdl` consolidation into `libc.so.6`). All seven remaining version nodes (`__cxa_thread_atexit_impl@GLIBC_2.18`, `getrandom@GLIBC_2.25`, `copy_file_range@GLIBC_2.27`, `statx@GLIBC_2.28`, `posix_spawn_file_actions_addchdir_np@GLIBC_2.29`, `gettid@GLIBC_2.30`, and `pidfd_spawnp`/`pidfd_getpid@GLIBC_2.39`) are referenced **exclusively by `STB_WEAK` symbols** generated by `libstd`'s `weak!` / `syscall!` macros. Because upstream Rust CI links `cargo` and `librustc_driver` against a `glibc 2.17` sysroot whose `libc.so.6` lacks those symbols, they remain unversioned (`ver_index = 0`) in `cargo` and `librustc_driver`, whereas linking `libstd-*.rlib` statically into `cargo-anneal` on a `glibc 2.39+` host binds them to `@@GLIBC_2.18`..`@@GLIBC_2.39`.

#### 7.2 How `ld-linux-x86-64.so.2` (`_dl_check_map_versions`) treats `vna_flags = 0x0`, `VER_FLG_WEAK (0x2)`, and `ver_index = 0`
In GNU `glibc`'s `elf/dl-version.c:_dl_check_map_versions`, startup version checking iterates over `.gnu.version_r` (`Elf64_Verneed` / `Elf64_Vernaux`) and **never inspects `.dynsym` (`st_bind`)**. We verified all four combinations on the live host `ld-linux-x86-64.so.2` (`glibc 2.42`) in [`support/linux-x86-64-clean-env-qualification/probe_glibc_verneed.py`](support/linux-x86-64-clean-env-qualification/probe_glibc_verneed.py):

| Case | `.dynsym` Binding | `.gnu.version_r` (`vna_flags`) | Runtime Provider Library | Exit Code | `stdout` | `stderr` Behavior |
| :--- | :---: | :---: | :--- | :---: | :--- | :--- |
| **Cases 1A & 2A** (`LLD 22.1.6` & `ld.bfd 2.45`) | `STB_WEAK` (`2`) | `0x0` (`none`) | Missing `PROV_2.0` / `GLIBC_2.99` | **`1`** | `""` | Aborts before `main()`: `version 'GLIBC_2.99' not found (required by ...)` |
| **Cases 1B & 2B** (`LLD 23.1.4` behavior) | `STB_WEAK` (`2`) | `0x2` (`VER_FLG_WEAK`) | Missing `PROV_2.0` / `GLIBC_2.99` | **`0`** | `pidfd_spawnp=NULL_fallback` | Runs and exits `0`, **but** `dl_main` (`verbose = 1`) prints `weak version 'GLIBC_2.99' not found (required by ...)` to `stderr` on every invocation |
| **Case 1C** (Strong sym + weak verneed) | `STB_GLOBAL` (`1`) | `0x2` (`VER_FLG_WEAK`) | Missing `PROV_2.0` | **`127`** | `""` | Prints weak-version warning in `_dl_check_map_versions`, then aborts in `_dl_lookup_symbol_x` (`undefined symbol: optional_fn, version PROV_2.0`) |
| **Case 1D** (`rust/bin/cargo` pattern) | `STB_WEAK` (`2`) | *(unversioned `ver_index = 0`)* | Missing `PROV_2.0` | **`0`** | `base=10 optional=NULL (graceful_fallback)` | **`""`** *(completely silent fallback)* |

Thus, while `LLD 23.1.4` (`VER_FLG_WEAK`) lowers the fatal `ld.so` startup floor of `cargo-anneal` from `GLIBC_2.39` to `GLIBC_2.34`, running a `VER_FLG_WEAK` binary on `glibc 2.34`..`2.38` still writes `weak version 'GLIBC_2.39' not found` to `stderr`. Achieving a clean, warning-free `GLIBC_2.17` or `GLIBC_2.34` floor requires linking `cargo-anneal` and `bin/anneal-rustc-capture` against a target sysroot matching that floor so post-floor weak symbols remain unversioned (`ver_index = 0`, Case 1D).

Basis: **source** and **execution** ([`support/linux-x86-64-clean-env-qualification/probe_glibc_verneed.py`](support/linux-x86-64-clean-env-qualification/probe_glibc_verneed.py), [`support/linux-x86-64-clean-env-qualification/track_d_q3_verneed_results.json`](support/linux-x86-64-clean-env-qualification/track_d_q3_verneed_results.json)).

## Boundaries

- **Known not to apply (Rust target triples vs. Anneal host platforms)**: Target triples listed in Charon's `rust-toolchain` (such as Windows, i686 Linux, PowerPC64 Linux, and RISC-V bare metal) are cross-compilation standard-library targets, not supported Anneal host platforms.
- **Known not to apply (best-effort Linux ELF loop and empty RPATH in `google/zerocopy@41f5b37afe`)**: In `google/zerocopy@41f5b37afe`, `packages.omnibus-tar`'s Linux ELF rewrite is guarded with `|| true`, filters on `-executable`, and clears RPATH to `""`, so archived executables require Anneal's `LD_LIBRARY_PATH` environment variables at runtime rather than functioning as standalone self-locating binaries. By contrast, `joshlf/anneal@f2bc17e9be` sets `dontPatchELF = true` to preserve upstream `$ORIGIN` `DT_RUNPATH` entries.
- **Known not to apply (macOS final staging pass and IFD in production packages)**: `packages.omnibus-tar` performs no Mach-O rewriting or `codesign` pass on Darwin, and production `packages.{rust-toolchain,lean-toolchain,default}` do not use `packages.test-ifd`.
- **Known not to apply (`VER_FLG_WEAK` as a silent `glibc` downgrade mechanism)**: Setting `VER_FLG_WEAK (0x2)` on `Elf64_Vernaux` entries prevents `ld.so` from aborting when a weak symbol's `GLIBC_2.*` version node is absent on an older host, but `dl_main` (`verbose = 1`) still prints `weak version '...' not found` to `stderr`; only unversioned `STB_WEAK` symbols (`ver_index = 0`) degrade silently.
- **Not examined (Linux AArch64 post-omnibus Charon execution and macOS omnibus `codesign` scan)**: No post-`omnibus-tar` Linux AArch64 execution of `charon` or complete Mach-O `otool -L`/`codesign` scan of the final macOS omnibus archive was performed.
- **Unknown (root cause of `mathlib-cache-download` hash instability on `aarch64-darwin`)**: The two `mathlib-cache-download` runs on `aarch64-darwin` yielded distinct recursive hashes; isolating which downloaded cache or package metadata file differed requires comparing the two failed store trees directly.

## Evidence

All supporting source maps, inventories, scripts, smoke fixtures, and execution logs are preserved under `support/`:

1. **Host-Platform Matrix (`support/host-platform-matrix/`)**:
   - [`support/host-platform-matrix/source-map.json`](support/host-platform-matrix/source-map.json) and [`support/host-platform-matrix/host-matrix.json`](support/host-platform-matrix/host-matrix.json).
2. **Linux ELF Interpreter and RPATH Relocation (`support/linux-elf-relocation/`)**:
   - [`support/linux-elf-relocation/source-map.json`](support/linux-elf-relocation/source-map.json) and [`support/linux-elf-relocation/relocation-contract.json`](support/linux-elf-relocation/relocation-contract.json).
3. **macOS Mach-O Relocation and Signing (`support/macos-macho-relocation/`)**:
   - [`support/macos-macho-relocation/source-map.json`](support/macos-macho-relocation/source-map.json) and [`support/macos-macho-relocation/relocation-contract.json`](support/macos-macho-relocation/relocation-contract.json).
4. **Nix Fixed-Output Downloads (`support/nix-fixed-output-downloads/`)**:
   - [`support/nix-fixed-output-downloads/source-map.json`](support/nix-fixed-output-downloads/source-map.json), [`support/nix-fixed-output-downloads/fod-inventory.json`](support/nix-fixed-output-downloads/fod-inventory.json), and [`support/nix-fixed-output-downloads/execution-observations.json`](support/nix-fixed-output-downloads/execution-observations.json).
5. **Nix Import-From-Derivation (`support/nix-ifd-version-extraction/`)**:
   - [`support/nix-ifd-version-extraction/source-map.json`](support/nix-ifd-version-extraction/source-map.json), [`support/nix-ifd-version-extraction/metadata-flow.json`](support/nix-ifd-version-extraction/metadata-flow.json), [`support/nix-ifd-version-extraction/execution-results.json`](support/nix-ifd-version-extraction/execution-results.json), and [`support/nix-ifd-version-extraction/execution/test-ifd-build.txt`](support/nix-ifd-version-extraction/execution/test-ifd-build.txt).
6. **Nix Toolchain-Tree Relocation (`support/nix-toolchain-tree-relocation/`)**:
   - [`support/nix-toolchain-tree-relocation/source-map.json`](support/nix-toolchain-tree-relocation/source-map.json), [`support/nix-toolchain-tree-relocation/relocation-observations.json`](support/nix-toolchain-tree-relocation/relocation-observations.json), [`support/nix-toolchain-tree-relocation/relocate.py`](support/nix-toolchain-tree-relocation/relocate.py), [`support/nix-toolchain-tree-relocation/Smoke.lean`](support/nix-toolchain-tree-relocation/Smoke.lean), and [`support/nix-toolchain-tree-relocation/smoke.rs`](support/nix-toolchain-tree-relocation/smoke.rs).
7. **Linux `x86_64` Clean-Environment Qualification, `DT_RUNPATH` Hardening, and `GLIBC` `DT_VERNEED` Reproducers (`support/linux-x86-64-clean-env-qualification/`)**:
   - [`support/linux-x86-64-clean-env-qualification/elf_audit.py`](support/linux-x86-64-clean-env-qualification/elf_audit.py) and [`support/linux-x86-64-clean-env-qualification/elf_audit.json`](support/linux-x86-64-clean-env-qualification/elf_audit.json).
   - [`support/linux-x86-64-clean-env-qualification/run_clean_env_qualification.py`](support/linux-x86-64-clean-env-qualification/run_clean_env_qualification.py) and [`support/linux-x86-64-clean-env-qualification/clean_env_qualification_results.json`](support/linux-x86-64-clean-env-qualification/clean_env_qualification_results.json).
   - [`support/linux-x86-64-clean-env-qualification/run_track_d_qualification.py`](support/linux-x86-64-clean-env-qualification/run_track_d_qualification.py) and [`support/linux-x86-64-clean-env-qualification/track_d_q1_q2_results.json`](support/linux-x86-64-clean-env-qualification/track_d_q1_q2_results.json).
   - [`support/linux-x86-64-clean-env-qualification/probe_glibc_verneed.py`](support/linux-x86-64-clean-env-qualification/probe_glibc_verneed.py) and [`support/linux-x86-64-clean-env-qualification/track_d_q3_verneed_results.json`](support/linux-x86-64-clean-env-qualification/track_d_q3_verneed_results.json).

## Revalidation

1. **Host-Platform and FOD Inventory Check**:
   - Inspect `anneal/flake.nix` for changes to the four-system mappings (`rustPlatform`, `leanPlatform`, `aeneasTarget`, `leantarPlatform`) or expected SHA-256 hashes, and compare against [`support/nix-fixed-output-downloads/fod-inventory.json`](support/nix-fixed-output-downloads/fod-inventory.json).
   - Check `packages.test-ifd` with both `nix build .#test-ifd` and `nix build --option allow-import-from-derivation false .#test-ifd`, and inspect `packages.aeneas-unpacked` to verify whether `RUST_DATE` is still injected from static `rustDate` or parsed from Aeneas/Charon metadata.
2. **Fail-Closed Linux ELF, `bwrap --tmpfs /`, and `DT_VERNEED` Audit**:
   - Run [`support/linux-x86-64-clean-env-qualification/elf_audit.py`](support/linux-x86-64-clean-env-qualification/elf_audit.py) across all ELF files in the unpacked Linux omnibus archive to verify `PT_INTERP`, `DT_RPATH`/`DT_RUNPATH` (asserting zero `/nix/store` or build-host `.rustup` paths in dynamic loader sections), and `DT_NEEDED` closure.
   - Run [`support/linux-x86-64-clean-env-qualification/run_track_d_qualification.py`](support/linux-x86-64-clean-env-qualification/run_track_d_qualification.py) and [`support/linux-x86-64-clean-env-qualification/probe_glibc_verneed.py`](support/linux-x86-64-clean-env-qualification/probe_glibc_verneed.py) to verify `--manifest-path` execution and positive/negative proofs inside a zero-executable `bwrap --tmpfs /` rootfs with only the 6 core `glibc` SONAMEs mounted, and inspect `.gnu.version_r` (`vna_flags`) and `.dynsym` (`st_bind`) for any `GLIBC_2.*` version above `GLIBC_2.34`.
3. **macOS Mach-O and Code-Signature Audit**:
   - Extract the macOS `x86_64` and `aarch64` omnibus archives into a directory outside `/nix/store` (preferably in a VM or environment without `/nix/store`), run `otool -L` and `otool -l` across every Mach-O executable and `.dylib` to verify the absence of `/nix/store` load commands, run `codesign --verify --strict` on signed binaries, and execute the relocated toolchain entry points using [`support/nix-toolchain-tree-relocation/relocate.py`](support/nix-toolchain-tree-relocation/relocate.py), [`support/nix-toolchain-tree-relocation/smoke.rs`](support/nix-toolchain-tree-relocation/smoke.rs), and [`support/nix-toolchain-tree-relocation/Smoke.lean`](support/nix-toolchain-tree-relocation/Smoke.lean).
