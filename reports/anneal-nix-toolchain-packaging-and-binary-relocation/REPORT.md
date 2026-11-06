# Anneal Nix Toolchain Packaging, Host-Platform Matrix, Fixed-Output Acquisition, Import-From-Derivation, and ELF/Mach-O Relocation

## Summary

This report synthesizes the Nix toolchain acquisition, evaluation-time metadata extraction, host-platform support matrix, and Linux ELF / macOS Mach-O binary relocation architecture of Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

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

## Applicability

These findings apply to:

- **Zerocopy Anneal**: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix` blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, `anneal/flake.lock` blob `92ac56b0a777d280f0a76e28f163b20ff6fb2003`, `anneal/src/setup.rs`, `anneal/src/resolve.rs`, `anneal/src/main.rs`, `anneal/v1/src/charon.rs`, `anneal/v1/src/aeneas.rs`, and `.github/workflows/anneal.yml`).
- **Aeneas and Charon Packaging**: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`, `flake.nix` blob `05e71549416ac622d6f12edc1fc7c74e338949ba`, `.github/workflows/release.yml` blob `e248e9fdbecb3809f54ef58456db3faee448175f`) and `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`, `flake.nix` blob `844a2ca996e86acb053bbecd52ff251134341da8`, `rust-toolchain`).
- **Lean 4 and PatchELF / Nixpkgs**: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) and `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1` (`patchelf-0.15.2`, `pkgs/development/tools/misc/patchelf/default.nix` blob `086e18e941858c130e684a5476d2f2bc681a4eea`).
- **Host Execution Environment (for FOD, IFD, and tree-relocation runs)**: `aarch64-darwin` (Apple Silicon, Darwin `25.6.0`, 8 GiB RAM) running Nix `2.35.2` on 2026-09-27.

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

## Boundaries

- **Known not to apply (Rust target triples vs. Anneal host platforms)**: Target triples listed in Charon's `rust-toolchain` (such as Windows, i686 Linux, PowerPC64 Linux, and RISC-V bare metal) are cross-compilation standard-library targets, not supported Anneal host platforms.
- **Known not to apply (best-effort Linux ELF loop and empty RPATH)**: `packages.omnibus-tar`'s Linux ELF rewrite is guarded with `|| true`, filters on `-executable`, and clears RPATH to `""`, so archived executables require Anneal's `LD_LIBRARY_PATH` environment variables at runtime rather than functioning as standalone self-locating binaries.
- **Known not to apply (macOS final staging pass and IFD in production packages)**: `packages.omnibus-tar` performs no Mach-O rewriting or `codesign` pass on Darwin, and production `packages.{rust-toolchain,lean-toolchain,default}` do not use `packages.test-ifd`.
- **Not examined (store-unmounted relocation and Linux AArch64 post-omnibus Charon execution)**: During the `aarch64-darwin` toolchain-tree relocation test, `/nix/store` remained mounted on the host, and no post-`omnibus-tar` Linux AArch64 execution of `charon` or complete Mach-O `otool -L`/`codesign` scan of the final macOS omnibus archive was performed.
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

## Revalidation

1. **Host-Platform and FOD Inventory Check**:
   - Inspect `anneal/flake.nix` for changes to the four-system mappings (`rustPlatform`, `leanPlatform`, `aeneasTarget`, `leantarPlatform`) or expected SHA-256 hashes, and compare against [`support/nix-fixed-output-downloads/fod-inventory.json`](support/nix-fixed-output-downloads/fod-inventory.json).
   - Check `packages.test-ifd` with both `nix build .#test-ifd` and `nix build --option allow-import-from-derivation false .#test-ifd`, and inspect `packages.aeneas-unpacked` to verify whether `RUST_DATE` is still injected from static `rustDate` or parsed from Aeneas/Charon metadata.
2. **Fail-Closed Linux ELF Audit**:
   - Extract the built Linux `x86_64` and `aarch64` omnibus archives, enumerate **all** ELF files by magic bytes (without `-executable` filtering), verify `PT_INTERP` matches `/lib64/ld-linux-x86-64.so.2` or `/lib/ld-linux-aarch64.so.1` (especially on `charon` and `charon-driver` on `aarch64-linux`), assert zero `/nix/store` strings in `RPATH`/`RUNPATH`/`PT_INTERP`, and execute `aeneas --help`, `charon --help`, `rustc --version`, `lean --version`, and `lake --version`.
3. **macOS Mach-O and Code-Signature Audit**:
   - Extract the macOS `x86_64` and `aarch64` omnibus archives into a directory outside `/nix/store` (preferably in a VM or environment without `/nix/store`), run `otool -L` and `otool -l` across every Mach-O executable and `.dylib` to verify the absence of `/nix/store` load commands, run `codesign --verify --strict` on signed binaries, and execute the relocated toolchain entry points using [`support/nix-toolchain-tree-relocation/relocate.py`](support/nix-toolchain-tree-relocation/relocate.py), [`support/nix-toolchain-tree-relocation/smoke.rs`](support/nix-toolchain-tree-relocation/smoke.rs), and [`support/nix-toolchain-tree-relocation/Smoke.lean`](support/nix-toolchain-tree-relocation/Smoke.lean).
