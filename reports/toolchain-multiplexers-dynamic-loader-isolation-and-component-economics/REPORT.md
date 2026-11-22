# Toolchain Multiplexers, Transitive ELF Dynamic-Loader Isolation, Component Economics, and Sysroot Resolution

## Summary

Multi-toolchain workspaces and compiler-internal verification drivers (`#![feature(rustc_private)]`) fail silently across four distinct system boundaries unless version multiplexing, ELF dynamic-loader search closures, distribution component footprints, and sysroot discovery are isolated together:

1. **Toolchain Multiplexer Selection, Authentication, and Environment Leakage (`Basis: source + execution`):**
   - **Go `1.21+` (`golang/go@2aae1000ea1d4b28923b96db28acf4e3b99d6aff`, `go1.27.3`)** orthogonally separates language compatibility (`go 1.X` forwarded per package as `-lang=go1.X` in `cmd/compile` plus `stdversion` API gating in `go vet`) from minimum binary selection (`toolchain go1.Y.Z` read solely from the main workspace `go.work`/`go.mod` under `GOTOOLCHAIN={local,<name>,auto,path,<name>+auto,<name>+path}`), while forcing non-bypassable `GOSUMDB` transparency-log verification on `golang.org/toolchain` module zips (`fetch.go:884` ignores workspace `go.sum`; `sumdb.go:35-65` overrides `GONOSUMDB` and rejects `GOSUMDB=off`).
   - **`anyzig` (`marler8997/anyzig@847a1628dd81f0b17335a024b16c97d4a03fabcb`) vs. `zigup` (`marler8997/zigup@659aa0024ad2139c5d45ad1f4663834f14972c67`)** replaces `zigup`'s unverified global mutable `$PATH` symlink with ancestor `build.zig.zon` `.minimum_zig_version` discovery and pre-download Ed25519 + BLAKE2b-512 `minisign` verification against the embedded Zig Software Foundation public key (binding both the archive digest and the signed filename in the trusted comment to block mirror rollback attacks). **`corepack` (`nodejs/corepack@4210ff8b4dba03ab347098c3f59225f34cb05652`, `v0.35.0`)** enforces in-manifest `packageManager` SHA-512 digests (`pnpm@<ver>+sha512.<hex>`) or registry ECDSA-SHA256 signatures, whereas **`bazelisk` (`bazelbuild/bazelisk@1e6aaf11d51e83ec8d18e66b461f49d4b7877321`, `v1.28.1`)** short-circuits `BAZELISK_VERIFY_SHA256` whenever `downloads/metadata/...` is already warm on disk (`core/core.go:436-454`).
   - **`rustup` (`rust-lang/rustup@edbc831cec44dc2858a4a4dce768c74361d027dc`, `1.29.3`) vs. `elan` (`leanprover/elan@3d5138e1526a569a23901b8ee559032793cf445e`, `v4.2.1`):** `rustup` authenticates Channel v2 manifests and component archives via SHA-256 and rejects relative `toolchain.path` overrides (`InvalidName::PathToolchainRelative`), but prepends `<toolchain>/lib` to `LD_LIBRARY_PATH` and sets `RUSTUP_TOOLCHAIN`—which overrides `rust-toolchain.toml` even when a child invokes `<sysroot-B>/bin/cargo` directly without setting `RUSTC`. Conversely, `elan` `v4.2.1` omits `LD_LIBRARY_PATH` but performs **zero archive checksum or signature verification** (`download.rs:29-37`) and resolves relative `lean-toolchain` strings against the repository directory first (`try_parse_path_toolchain`, `toolchain.rs:49-51, 208-226`), allowing an untrusted checkout containing `lean-toolchain` + `<subpath>/bin/lean` to execute arbitrary repository binaries on the first `lean` or `lake` invocation.
   - **Build-graph and Nix multi-toolchain composition (`bazelbuild/rules_rust@5d99ff2e58d1a0c9387fc4945029df11144bc8a3`, `oxalica/rust-overlay@5aa410a1df0e4e9c25f3818320651c2bddf66aff`, `nix-community/fenix@012c1a71bd93921f320def3d0e586cc4dd332b65`):** `rules_rust` orthogonalizes `(exec_triple, target_triple, channel)` toolchains and enforces `rust_sysroot_anchor` identity on `rustc_driver` companions (`clippy`, `rustdoc`). Both `rust-overlay` (zero-IFD compressed Nix manifests) and `fenix` deduplicate `libLLVM.so.*` (~`199 MiB`) across profiles via symlinks, but must physically copy `librustc_driver-*.so` (~`156 MiB`) per `symlinkJoin` derivation because `rustc` infers its default sysroot via `dladdr` + `realpath` on `librustc_driver-*.so`.

2. **Non-Inheritance of Executable `DT_RPATH` Across `DT_RUNPATH` Shared Libraries (`glibc` `elf/dl-load.c:1982`) and Live Cross-Toolchain Hijack Proofs (`Basis: source + execution`):**
   - In GNU `glibc` (`bminor/glibc@04e750e75b73957cf1c791535a3f4319534a52fc`, `elf/dl-load.c:1982`), `_dl_map_new_object` consults `loader` ancestor `DT_RPATH` tags and `main_map->l_rpath_dirs` (the main executable's `DT_RPATH`) **if and only if `loader == NULL || loader->l_info[DT_RUNPATH] == NULL`**.
   - Because upstream `librustc_driver-<hash>.so` ships with `DT_RUNPATH = $ORIGIN/../lib` (`DT_RPATH = NULL`), stamping a custom `rustc_private` driver executable `E` alone with `patchelf --force-rpath` (`DT_RPATH`) protects only Hop 1 (`E -> librustc_driver`). On Hop 2 (`librustc_driver -> libLLVM.so.23.1-rust-1.102.0-nightly`), `loader->l_info[DT_RUNPATH]` is non-NULL, skipping `E`'s `DT_RPATH` and searching `LD_LIBRARY_PATH` *before* `$ORIGIN/../lib`.
   - Live execution proves that leaked `LD_LIBRARY_PATH` silently splices `6905905bb`'s `libLLVM.so.23.1-rust-1.102.0-nightly` (`LLVM 23.1.6`) underneath `3ef0c22cd`'s `librustc_driver-789fff502791d0da.so` (`LLVM 23.1.5`) with exit code `0` while a `librustc_driver`-only `/proc/self/maps` check **passes falsely (`true`)**, and silently downgrades `leanprover/lean4` `v4.35.0/bin/lean` to execute the `v4.34.1` kernel (`libleanshared.so` unversioned `DT_SONAME`). Sound isolation requires scrubbing `LD_LIBRARY_PATH`/`LD_PRELOAD`/`LD_AUDIT` (and Darwin `DYLD_*`) in the parent orchestrator **plus** full-closure `/proc/self/maps` verification across `librustc_driver*`, `libLLVM*`, `libstd-*`, and `librustc_codegen*`.

3. **`rustc-dev` Build-Time vs. Runtime Component Economics (`Basis: source + execution`):**
   - In official `x86_64-unknown-linux-gnu` Channel v2 manifests (`channel-rust-1.100.0.toml` SHA-256 `3051e859...` and `2026-11-12` nightly `0e29758e...`), `rustc-dev` (`116.37 MiB` `.tar.xz`, `642.07 MiB` unpacked across `3,220` files on `1.100.0`) accounts for **`51.2%` of compressed download** (`116.37 / 227.22 MiB`) and **`53.3%` of installed disk footprint** (`642.07 / 1,205.31 MiB`) of `{rustc, rust-std, rustc-dev}`, yet **zero bytes of `rustc-dev` are loaded at verification runtime**.
   - Once a zero-dependency `#![feature(rustc_private)]` MIR-capture shim is compiled (`377.13 ms` warm median, `592.15 ms` cold, `310.70 MiB` peak RSS, yielding a **`25,320`-byte / `24.73 KiB` stripped binary**), it executes cleanly (`returncode = 0`) against standard `rustc` + `rust-std` installations (`103` files, `110.85 MiB` `.tar.xz` / `563.25 MiB` unpacked) with `0` `rustc-dev` files present.

4. **Causal Provenance of `filesearch.rs:339-341` `AT_FDCWD` `"lib/rustlib"` (`1.54.0`–`1.102.0-nightly`) and All Seven Residual `Sysroot::default` Channels (`Basis: source + execution`):**
   - Commit `rust-lang/rust@b7c5599d22018ab6be88442c4668bc1697f85b8e` (`2021-05-10`, first released in Rust `1.54.0`, preserved across the `1.80.0` rename in `b4c439c3de913953a2968c6917e125fafaacf886`) changed `from_env_args_next()` in `compiler/rustc_session/src/filesearch.rs` to call `exists()` on a **relative** `"lib/rustlib"` `PathBuf` without joining the candidate sysroot `p`. Across all 7 tested releases (`1.56.0` through `1.102.0-nightly`), invoking a symlinked/CAS `rustc` without `--sysroot` ignores the CAS sysroot in clean directories and hijacks sysroot resolution whenever the caller's working directory contains `./lib/rustlib`.
   - Passing explicit `--sysroot <path>` seals `Sysroot::path()` for 100% of target (`core`, `std`) and host (`proc_macro`) crate lookups, while **seven residual code paths (`P1`–`P7`)** still read `Sysroot::all_paths()` or `Sysroot::default` (including bundled `rust-lld` lookup in `Session::get_tools_search_paths`, `session.rs:676-691`); overwriting `config.opts.sysroot.default` inside `Callbacks::config` closes every post-startup fallback channel.

## Applicability

These findings govern multi-toolchain workspace launchers, hermetic build systems, and compiler-internal (`rustc_private`) verification harnesses across the subjects recorded in `REPORT.json`:

- **Toolchain Multiplexers & Portable Distributions (`Basis: source + execution`):**
  - `rust-lang/rustup@edbc831cec44dc2858a4a4dce768c74361d027dc` (`1.29.3`, source + live execution on `x86_64-unknown-linux-gnu`).
  - `golang/go@2aae1000ea1d4b28923b96db28acf4e3b99d6aff` (`go1.27.3`, source + live execution on `linux/amd64`).
  - `marler8997/zigup@659aa0024ad2139c5d45ad1f4663834f14972c67` and `marler8997/anyzig@847a1628dd81f0b17335a024b16c97d4a03fabcb` (source inspection).
  - `leanprover/elan@3d5138e1526a569a23901b8ee559032793cf445e` (`v4.2.1`, source + live environment inspection) alongside `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) and `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`).
  - `nodejs/corepack@4210ff8b4dba03ab347098c3f59225f34cb05652` (`v0.35.0`), `bazelbuild/bazelisk@1e6aaf11d51e83ec8d18e66b461f49d4b7877321` (`v1.28.1`), `astral-sh/python-build-standalone@98b27f721dbc67ded8c7d562aa5dd60c5507eda0`, `astral-sh/uv@264d8b4a5e10d195d2cc2a34dffa807cfbe6298c`, and `ziglang/zig@e4cbd752c8c05f131051f8c873cff7823177d7d3` (`0.15.2`) (source inspection).
  - `bazelbuild/rules_rust@5d99ff2e58d1a0c9387fc4945029df11144bc8a3`, `oxalica/rust-overlay@5aa410a1df0e4e9c25f3818320651c2bddf66aff`, and `nix-community/fenix@012c1a71bd93921f320def3d0e586cc4dd332b65` (source inspection).
- **Dynamic Loader, Rust Releases, and Channel Manifests (`Basis: source + execution`):**
  - GNU `glibc` `bminor/glibc@04e750e75b73957cf1c791535a3f4319534a52fc` (`elf/dl-load.c`, source inspection) and live execution on `x86_64-unknown-linux-gnu` (`GNU libc 2.43`, `patchelf 0.15.2`, Python `3.13.15`).
  - `rust-lang/rust` historical and current revisions: `3f679fef23cd006c336e2a4f7c6707e119d22206` (`1.50.0` CAS sysroot introduction), `b7c5599d22018ab6be88442c4668bc1697f85b8e` (`1.54.0` `AT_FDCWD` regression), `09c42c45858d5f3aedfa670698275303a3d19afa` (`1.56.0`), `fe5b13d681f25ee6474be29d748c65adcd91f69e` (`1.61.0`), `9b00956e56009bab2aa15d7bff10916599e3d6d6` (`1.78.0`), `b4c439c3de913953a2968c6917e125fafaacf886` (`1.80.0` rename), `9fc6b43126469e3858e2fe86cafb4f0fd5068869` (`1.84.0`), `01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf` (`1.93.1`), `0ef1bc386059596dada8fb65b50425aab2ea637a` (`1.100.0`, `channel-rust-1.100.0.toml` SHA-256 `3051e859570f64a8c5acb9d09e87425db52c7d97287c67e8f6d57d7d34ef9258`), `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly` `2026-11-11`, `channel-rust-nightly.toml` SHA-256 `0e29758e4495709044396db6992e8bc44cd0109e7dbb21e430216cf368ac6c9d`), `8eb778d04094d3af4b26580cab327e0413eb1e02` (`1.102.0-nightly` `2026-11-12`), and `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2` (`1.102.0-nightly` `2026-11-19`).
- **Relationship to Companion Corpus Coverage:** [`anneal-nix-toolchain-packaging-and-binary-relocation`](../anneal-nix-toolchain-packaging-and-binary-relocation/REPORT.md) establishes single-toolchain Nix fixed-output acquisition, `patchelf` `PT_INTERP`/`DT_RUNPATH` relocation, and `GLIBC` `VER_FLG_WEAK` version-node semantics. This report extends that baseline to **multi-toolchain coexistence**: cross-ecosystem version-selection cascades, the exact `glibc` `dl-load.c:1982` transitive `DT_RPATH` non-inheritance mechanism when an intermediate shared library carries `DT_RUNPATH`, `rustc-dev` build-vs-runtime component economics, and `rustc`'s `filesearch.rs` `AT_FDCWD` regression and `Sysroot` fallback channels.

## Findings

### 1. Comparative Taxonomy of Toolchain Multiplexers and Hermetic Distributions

#### 1.1 Cross-Ecosystem Architecture and Security Matrix

`Basis: source + execution`

| System & Pin | Project Pin File & Semantics | Override Cascade (Highest $\to$ Lowest) | Archive Integrity Verification | Child Process Env / Loader Mutation | Key Isolation Property or Hazard |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`golang/go`** (`go1.27.3`, `2aae1000ea1d...`) | `go.mod` / `go.work`: splits **`go 1.X`** (per-pkg `-lang=go1.X` + module floor) from **`toolchain go1.Y.Z`** (workspace minimum binary suggestion) | `GOTOOLCHAIN` OS env $\succ$ `$GOENV` $\succ$ `$GOROOT/go.env` (`auto`); `go.work` shadows `go.mod` at startup (`select.go:527-547`) | **Non-bypassable `GOSUMDB`** (`fetch.go:884` ignores repo `go.sum`; `sumdb.go:35-65` overrides `GONOSUMDB` & fails closed on `GOSUMDB=off`) | Sets `GOROOT` (for module cache) + `GOTOOLCHAIN_INTERNAL_SWITCH_{VERSION,COUNT}` (`maxSwitch=100`); zero `LD_LIBRARY_PATH` | `cmd/compile` gates syntax via `-lang=`, while newer stdlib symbols are gated only by `go vet` (`stdversion`) |
| **`rust-lang/rustup`** (`1.29.3`, `edbc831cec44...`) | `rust-toolchain.toml` / `rust-toolchain` (conflates compiler binary, stdlib, and profile/components) | `+toolchain` CLI $\succ$ `RUSTUP_TOOLCHAIN` env $\succ$ per-ancestor `(OverrideDb(d) > d/rust-toolchain > d/rust-toolchain.toml)` $\succ$ default (`config.rs:592-738`) | **SHA-256** on `channel-rust-*.toml.sha256` and per-component `.tar.{zst,xz,gz}` (`download.rs:84-149`); unsigned GPG path unused by default | **Prepends `<tc>/lib` to `LD_LIBRARY_PATH`** (`DYLD_FALLBACK_LIBRARY_PATH` on macOS), sets `RUSTUP_TOOLCHAIN`, increments `RUST_RECURSION_COUNT` (`MAX=20`) | Rejects relative `toolchain.path` (`names.rs:391-393`), **but** leaked `LD_LIBRARY_PATH` & `RUSTUP_TOOLCHAIN` poison child toolchains |
| **`leanprover/elan`** (`v4.2.1`, `3d5138e1526a...`) | `lean-toolchain` (or legacy `leanpkg.toml` `lean_version`) | `+toolchain` CLI $\succ$ `ELAN_TOOLCHAIN` env $\succ$ per-ancestor `(OverrideDB(d) > d/lean-toolchain > d/leanpkg.toml > InToolchainDirectory)` $\succ$ default | **NONE (`HTTPS` only)**: `download_and_check` (`download.rs:29-37`) performs zero SHA-256 or signature checks (`gpg_key` commented out) | Sets `ELAN_TOOLCHAIN`, `ELAN_HOME`, `LEAN_RECURSION_COUNT`, prepends `ELAN_HOME/bin` to `PATH`; **never sets `LD_LIBRARY_PATH`** | **Repo-relative code execution**: `try_parse_path_toolchain` (`toolchain.rs:208-226`) executes `<repo>/<name>/bin/lean` and fetches arbitrary `<org>/<repo>:<tag>` GitHub releases |
| **`marler8997/zigup`** (`659aa0024ad2...`) | None (imperative global CLI: `zigup <ver>`, `zigup default`, `zigup run <ver>`) | Explicit `zigup run <ver>` CLI $\succ$ global mutable `zig` symlink (`--path-link` or `<zigup_dir>/zig`, `zigup.zig:283-290, 920-935`) | **NONE**: downloads URLs from `ziglang.org/download/index.json` (`L635, 1264-1325`) without `shasum` or `minisign` verification | Mutates global filesystem symlink; `verifyPathLink` (`L939-1045`) fails if an earlier `$PATH` entry shadows `path_link` | Cannot isolate concurrent projects using different Zig versions without `zigup run` wrappers |
| **`marler8997/anyzig`** (`847a1628dd81...`) | `build.zig.zon` `.minimum_zig_version` (or `.mach_zig_version`) | CLI `zig <VERSION> ...` $\succ$ ancestor `build.zig` + `build.zig.zon` (`main.zig:204-251, 2052-2073`) $\succ$ `ad-hoc` version file (`L1136-1185`) | **Embedded ZSF Ed25519 + BLAKE2b-512 `minisign`** (`minisign.zig:24-97`, `main.zig:1561-1712`) verifying both archive digest and trusted filename on mirrors | Raw `execve` preserving `ZIG_PROGRESS` (`main.zig:494-500`); per-version `.lock` + self-cleaning `TmpFile` locks (`TmpFile.zig:8-200`); zero `LD_LIBRARY_PATH` | Mirror `.minisig` filename check blocks signed-downgrade attacks; direct non-mirrored fallback checks `index.json` membership (`main.zig:866-874`) |
| **`nodejs/corepack`** (`v0.35.0`, `4210ff8b4dba...`) | `package.json` `packageManager` (`<name>@<ver>[+<algo>.<hex>]`) & `devEngines.packageManager` | Ancestor `package.json` `packageManager` (`specUtils.ts:162-254`) + `.corepack.env`; fails closed on cross-tool invocation (`Engine.ts:296-306`) | **Dual-mode**: streaming `crypto.createHash` against pinned `+sha512.<hex>` (`corepackUtils.ts:175, 308`), or **npm ECDSA-SHA256** registry signature (`npmRegistryUtils.ts:35-68`) | Rewrites cached locator with `+sha512.<hash>`; supports offline `corepack pack` + `install -g --cache-only` (`COREPACK_ENABLE_NETWORK=0`) | Blocks arbitrary URLs unless `COREPACK_ENABLE_UNSAFE_CUSTOM_URLS=1` (`specUtils.ts:48-50`) |
| **`bazelbuild/bazelisk`** (`v1.28.1`, `1e6aaf11d51e...`) | `.bazelversion` and `.bazeliskrc` (`USE_BAZEL_VERSION`, `BAZELISK_VERIFY_SHA256`) | `USE_BAZEL_VERSION` (`OS env > <ws>/.bazeliskrc > ~/.bazeliskrc`) $\succ$ `<ws>/.bazelversion` $\succ$ `USE_BAZEL_FALLBACK_VERSION` (`core.go:58-79, 312-380`) | Two-tier `downloads/metadata` $\to$ `downloads/sha256/<hex>/bin/bazel` CAS (`core.go:418-575`) with optional `BAZELISK_VERIFY_SHA256` | Chains `<ws>/tools/bazel` wrapper with `BAZELISK_SKIP_WRAPPER=true` and `BAZEL_REAL=<cas_path>` (`core.go:616-740`) | **Warm-cache verification bypass**: existing `mappingPath` returns cached CAS path *before* checking `BAZELISK_VERIFY_SHA256` (`core.go:436-454`) |
| **`python-build-standalone` + `uv`** (`98b27f7...` / `264d8b4...`) | `.python-version`, `pyproject.toml` `requires-python`, PEP 723 inline `# /// script` | `--python`/`UV_PYTHON` $\succ$ `.python-version` (bounded at `workspace_root`, intersected with PEP 723 `requires-python` in scripts) $\succ$ `requires-python` | SHA-256 release asset digests in `uv-python` download metadata | PBS stamps **`DT_RPATH = $ORIGIN/../lib`** (`--force-rpath`) + `$ORIGIN`-prefixed `DT_NEEDED` on `libpython3.so` (`build-cpython.sh:895-949`); `uv` patches macOS `-id` | Rejects `ExecutableName` in `.python-version` (`version_files.rs:203-209`) and stops discovery at `workspace_root` (`project.rs:130`) |
| **`bazelbuild/rules_rust`** (`5d99ff2e58d1...`) | `MODULE.bazel` / `WORKSPACE` `rust_repository_set` per `(exec, target, channel)` | Bazel toolchain resolution over `exec_compatible_with`, `target_compatible_with`, `target_settings` (`channel`), and `cfg = "exec"` on `proc_macro_deps` | Bazel repository-rule SHA-256 pinning over upstream `.tar.xz` archives | Passes explicit `--sysroot`; `companion_rust_toolchain` (`sysroot.bzl:195-204`) enforces identical `sysroot_anchor` for `clippy`/`rustdoc` | Decouples source-only tools (`rustfmt`, `rust_analyzer`) from ABI-coupled `.rmeta` consumers (`clippy-driver`) |
| **`oxalica/rust-overlay` & `nix-community/fenix`** (`5aa410a...` / `012c1a7...`) | `flake.lock` + `rust-toolchain.toml` (`fromRustupToolchainFile` / `fromToolchainFile`) | Pure Nix attribute selection per derivation (zero global proxy shims) | Per-component SHA-256 FODs (`rust-overlay` embeds compressed Nix manifests for **zero IFD**; `fenix` uses HTTP/IFD for historical dates) | Rewrites ELF `PT_INTERP` + `DT_RUNPATH` (`$out/lib`) and wraps `rust-lld`; zero `LD_LIBRARY_PATH` on Linux | Both must physically `cp` `~156 MiB` `librustc_driver-*.so` per `symlinkJoin` (`mk-aggregated.nix:63-83`, `combine.nix:30-32`) while symlinking `libLLVM.so.*` |

#### 1.2 Go `1.21+` Language-vs-Binary Decoupling, Non-Bypassable `GOSUMDB`, and Race-Safe Unpacking (`golang/go@2aae1000ea1d4b28923b96db28acf4e3b99d6aff`)

`Basis: source + execution`

Go `1.21+` splits two roles that `rust-toolchain.toml` and `lean-toolchain` conflate:

1. **`go 1.X` (Language Semantics & Module-Graph Floor) vs. `toolchain go1.Y.Z` (Main-Workspace Binary Suggestion):**
   - Across `go.work`, the main `go.mod`, and every transitive dependency `go.mod`, `modload` (`src/cmd/go/internal/modload/init.go:842-844`, blob `6e3f9251be9b1ed8bed42893a4797cc3b00e6bbe`) and `modfetch` (`src/cmd/go/internal/modfetch/fetch.go:65-70`, blob `74cbbe06468c8eef7ba9e5f6f4f563875a647195`) check `gover.Compare(goVersion, gover.Local()) > 0`, raising `&gover.TooNewError` (`src/cmd/go/internal/gover/toolchain.go:65-91`) to trigger dynamic upward switching via `toolchain.Switcher` (`src/cmd/go/internal/toolchain/switch.go:34-113`) whenever `GOTOOLCHAIN` allows `auto` or `path`.
   - During compilation (`src/cmd/go/internal/work/gc.go:69-83, 112-114`, blob `49b26e15609bb8da854c06ba3a225d28a2d0413d`), `gcToolchain.gc` passes **`-lang=go` + `gover.Lang(p.Module.GoVersion)`** per package alongside `-goversion ToolchainVersion`. Under `go1.27.3`, standard-library packages compile with `-lang=go1.27 -std` while a user module declaring `go 1.21` compiles in the same invocation with `-lang=go1.21 -goversion go1.27.3`.
   - Crucially, `cmd/compile` (`src/cmd/compile/internal/types2/{version.go:16-68, check.go:312-346}`) gates **language syntax and type-checker rules** (such as Go `1.22` `for range <int>` and per-iteration loop variables), **not standard-library symbols**. A `go 1.21` module calling Go `1.23`'s `slices.Backward` compiles with `returncode = 0` under `go build`; standard-library API gating is enforced only statically by `go vet`'s `stdversion` analyzer (`src/cmd/vendor/golang.org/x/tools/go/analysis/passes/stdversion/stdversion.go:46-114`, `typesinternal.TooNewStdSymbols`).
   - Conversely, `toolchain go1.Y.Z` is read **exclusively** from the enclosing `go.work` or main `go.mod` (`modGoToolchain`, `src/cmd/go/internal/toolchain/select.go:527-547`, blob `bd2ae4ee2ed030c131a8756c17ea8a9ee7fa6d29`; `fetch.go:66` ignores `toolchain` in dependency `go.mod` files) and acts strictly as a **minimum** (`select.go:194-226`): a local `go1.27.3` never downgrades when `go.mod` specifies `toolchain go1.24.0`, and `toolchain default` (`select.go:178-192`) locks selection to the configured default, failing closed with `TooNewError` rather than auto-upgrading.

2. **Non-Bypassable `GOSUMDB` Authentication, Race-Safe Module Unpacking, and Loop Guards:**
   - `cmd/distpack` (`src/cmd/distpack/pack.go:57-59, 212-248`, blob `53e9dbd73b64caa49b3bcbe39591f4466b523350`) distributes toolchains as module zips `golang.org/toolchain@v0.0.1-go<ver>.<goos>-<goarch>`, renaming nested `go.mod` files to `_go.mod` (`pack.go:221`).
   - Two security guards prevent repository-controlled toolchain poisoning: (i) `checkModSum` (`fetch.go:884`) writes `if done && mod.Path != "golang.org/toolchain" { return nil }`, refusing to trust hashes planted in a workspace's `go.sum`; and (ii) `useSumDB` (`src/cmd/go/internal/modfetch/sumdb.go:35-65, 102-104`, blob `6fb435b010d67c40d4a069f3049487af69b61535`) forces `GOSUMDB` lookup regardless of `GONOSUMDB` and aborts with `checksum database disabled by GOSUMDB=off` when `GOSUMDB=off` (except pure single-entry `GOPROXY=file://...`).
   - Post-unpack initialization in `Exec()` (`select.go:379-522`) is race-safe across concurrent `go` processes without holding a global execution lock: `0o111` execute bits are applied to `pkg/tool` and `bin/gofmt` **strictly before** `bin/go` (`select.go:384-426`), and `_go.mod -> go.mod` files are written via `os.O_CREATE|os.O_WRONLY` **without `O_TRUNC`** (`select.go:506`) with `src/go.mod` materialized last as the completion sentinel (`select.go:436-450`).
   - Re-dispatch (`select.go:59, 71, 243-264, 311-318`; `exec.go:23-63`) sets `GOTOOLCHAIN_INTERNAL_SWITCH_VERSION=<target>` (forcing the child to verify `gover.LocalToolchain() == target` and then unset the variable) and increments `GOTOOLCHAIN_INTERNAL_SWITCH_COUNT` up to `maxSwitch = 100` (stripped from user commands by `FilterEnv`, `select.go:76-86`). `GOTOOLCHAIN=path` (`switch.go:166-198`) scans only absolute `$PATH` entries (`if dir == "" || !filepath.IsAbs(dir) { continue }`) and never touches the network.

Live execution of `go1.27.3` via [`support/probe_toolchain_isolation.py`](support/probe_toolchain_isolation.py) ([`support/probe_toolchain_isolation_results.json`](support/probe_toolchain_isolation_results.json), `part_a_go_toolchain`) confirms all nine state transitions:

| Probe Scenario | `go.mod` Directives | Environment | Exit | Observed Compiler Flag or Fail-Closed Diagnostic |
| :--- | :--- | :--- | :---: | :--- |
| Language `1.21` dry-run | `go 1.21` | `GOTOOLCHAIN=local` or `path` | `0` | User pkg: `-lang=go1.21 -goversion go1.27.3`; stdlib: `-lang=go1.27` |
| Language `1.24` dry-run | `go 1.24` | `GOTOOLCHAIN=local` or `path` | `0` | User pkg: `-lang=go1.24 -goversion go1.27.3`; stdlib: `-lang=go1.27` |
| Go `1.22` `for range 3` syntax | `go 1.21` | `GOTOOLCHAIN=local` | `1` | `./main.go:7:12: cannot range over 3 (untyped int constant): requires go1.22 or later (-lang was set to go1.21; check go.mod)` |
| Go `1.23` `slices.Backward` stdlib | `go 1.21` | `GOTOOLCHAIN=local` | `build`: `0`<br>`vet`: `1` | `go build` succeeds (`0`); `go vet` fails: `main.go:6:13: slices.Backward requires go1.23 or later (module is go1.21)` |
| Future `toolchain` line only | `go 1.24` + `toolchain go1.99.0` | `GOTOOLCHAIN=local` | `0` | `go: using local toolchain go1.27.3` (ignores `toolchain` suggestion; compiles `-lang=go1.24`) |
| Future `toolchain` line only | `go 1.24` + `toolchain go1.99.0` | `GOTOOLCHAIN=path` | `1` | `go: upgrading toolchain to go1.99.0 ...` / `go: cannot find "go1.99.0" in PATH` |
| Future `go` floor | `go 1.99.0` + `toolchain go1.99.0` | `GOTOOLCHAIN=local` | `1` | `go: go.mod requires go >= 1.99.0 (running go 1.27.3; GOTOOLCHAIN=local)` |
| Switch loop guard | `toolchain go1.99.0` | `GOTOOLCHAIN_INTERNAL_SWITCH_COUNT=100` | `1` | `go: switching from go1.27.3 to go1.99.0 [depth 100]` / `go: too many toolchain switches` |
| Dishonest `$PATH` target shim | `toolchain go1.99.0` | `GOTOOLCHAIN_INTERNAL_SWITCH_VERSION=go1.99.0` | `1` | `go: toolchain go1.27.3 invoked to provide go1.99.0` |

#### 1.3 `rustup` vs. `elan`, `RUSTUP_TOOLCHAIN` Split-Brain Builds, and `elan`'s Repo-Relative Execution Hazard

`Basis: source + execution`

1. **`elan` `v4.2.1` Arbitrary Repository-Relative Binary Execution & Unverified Downloads (`leanprover/elan@3d5138e1526a569a23901b8ee559032793cf445e`):**
   - Whereas `rustup` (`rust-lang/rustup@edbc831cec44dc2858a4a4dce768c74361d027dc`, `src/config.rs:202-220` blob `511b6de7e8f15927671efdf50aee5b053afa086b`, `src/toolchain/names.rs:346-400` blob `f5181246b59331195bae2d81ae72e1957719c743`) explicitly forbids relative paths in `rust-toolchain.toml` (`if !value.is_absolute() { Err(InvalidName::PathToolchainRelative(...)) }`, noting at `config.rs:212-215` that relative paths *"permit trivial completely arbitrary code execution in a directory"*), `elan` `v4.2.1` (`src/elan/toolchain.rs:42-52, 208-226`, blob `b5e90905a8cfe55ad6bafcc1aa972d3c50376209`) passes `Some(toolchain_file_dir)` into `lookup_unresolved_toolchain_desc`, which calls **`try_parse_path_toolchain(name, base_dir)` first** (`toolchain.rs:49-51`).
   - `try_parse_path_toolchain` resolves relative strings via `toolchain_file_dir.join(path_str)` (`toolchain.rs:216`) and admits `ToolchainDesc::Path { path }` whenever `<path>/bin/lean` `is_file()` (`toolchain.rs:220-225`). Consequently, running `lean --version` or `lake` inside an untrusted checkout containing `lean-toolchain` = `local-tc` and `<repo>/local-tc/bin/lean` immediately executes `<repo>/local-tc/bin/lean`.
   - Even when `lean-toolchain` names a remote release, `ToolchainDesc::from_resolved_str` (`src/elan-dist/src/dist.rs:47-61`, blob `fb903926f5781bb68c57f23ec8d143cad30f70a8`) accepts arbitrary `<org>/<repo>:<tag>` origins fetched from `https://github.com/<origin>/releases/...` (`src/elan-dist/src/manifestation.rs:115-131`), and `DownloadCfg::download_and_check` (`src/elan-dist/src/download.rs:29-37`, blob `efaa6f5db4cea68d79a6c9a8034863934cd292cb`) performs **zero SHA-256 or cryptographic signature checks**. Any automated verifier invoking `lean` or `lake` on untrusted inputs must bypass `elan` shims completely and execute a hash-pinned `bin/lean` directly.

2. **`rustup` `1.29.3` Override Precedence & `RUSTUP_TOOLCHAIN` Split-Brain Hijacking (`support/probe_toolchain_isolation_results.json`, `cargo_inheritance_matrix`):**
   - In `rustup` (`src/config.rs:592-738`), `ActiveSource::Environment` (`RUSTUP_TOOLCHAIN`) outranks `find_override_from_dir_walk` (`settings.toml` `OverrideDb(d)` $\succ$ `d/rust-toolchain` $\succ$ `d/rust-toolchain.toml` checked together at each ancestor directory `d`).
   - Live execution inside a crate pinning `channel = "1.100.0"` in `rust-toolchain.toml` demonstrates that when a parent running under `1.93.1` (`RUSTUP_TOOLCHAIN=1.93.1-x86_64-unknown-linux-gnu`) spawns **even the direct `<RUSTUP_HOME>/toolchains/1.100.0-x86_64-unknown-linux-gnu/bin/cargo` binary** (`cargo 1.100.0 (3acc79c0c 2026-11-05)`) without setting `RUSTC` or scrubbing `RUSTUP_TOOLCHAIN`, `cargo 1.100.0` resolves `"rustc"` via `$PATH` (`<CARGO_HOME>/bin/rustc` proxy), which reads `RUSTUP_TOOLCHAIN` and dispatches to **`rustc 1.93.1`** (`BUILD_RS_RUSTC=<RUSTUP_HOME>/toolchains/1.93.1-.../bin/rustc`)! Eliminating proxy cross-talk requires scrubbing `RUSTUP_TOOLCHAIN` **and** passing explicit `RUSTC=<sysroot>/bin/rustc` (and `RUSTDOC=<sysroot>/bin/rustdoc`) to direct `<sysroot>/bin/cargo`.

#### 1.4 Portable Binary Hardening (`python-build-standalone`, `zig`) and Nix `librustc_driver` Deduplication Limits (`rust-overlay`, `fenix`)

`Basis: source`

- **ELF & `glibc` Portability Strategies (`astral-sh/python-build-standalone@98b27f721dbc67ded8c7d562aa5dd60c5507eda0`, `ziglang/zig@e4cbd752c8c05f131051f8c873cff7823177d7d3`):** `python-build-standalone` (`cpython-unix/build-cpython.sh:895-949`, blob `722ece906a569d19a8539b1073c9660ed68a7f3f`) defeats `LD_LIBRARY_PATH` poisoning on `glibc` both by stamping `DT_RPATH = '$ORIGIN/../lib'` (`patchelf --force-rpath`) on `bin/python3.x` **and** by rewriting `lib/libpython3.so`'s `DT_NEEDED` entry via `patchelf --replace-needed libpython3.x.so.1.0 '$ORIGIN/../lib/libpython3.x.so.1.0'` (`L940-941`; because the `DT_NEEDED` string contains `'/'`, `glibc` `ld.so` opens the `$ORIGIN`-expanded path directly without consulting `LD_LIBRARY_PATH`, `DT_RPATH`, or `DT_RUNPATH`, whereas `musl` does not expand `$ORIGIN` inside `DT_NEEDED`). Meanwhile, `zig` (`0.15.2`, `src/libs/glibc.zig:38-56` blob `b228ad60ad540d9ab3d491e33bfb84b55a8a0a39`) avoids container build sysroots by synthesizing target-versioned stub `.so`s on demand from its `< 800 KiB` `lib/libc/glibc/abilists` database (explicitly encoding the `glibc 2.34` `libpthread`/`libdl`/`librt`/`libutil` merge via `removed_in = 2.34.0`).
- **Why Nix Multi-Toolchain Aggregators Must Copy `librustc_driver-*.so` (`oxalica/rust-overlay@5aa410a1df0e4e9c25f3818320651c2bddf66aff` vs. `nix-community/fenix@012c1a71bd93921f320def3d0e586cc4dd332b65`):** Both `rust-overlay` (`lib/mk-aggregated.nix:63-83`, blob `a59c319f46eb0062e8b0ea5b6b3c1dc5c7450cca`) and `fenix` (`lib/combine.nix:12-32`, blob `12e2ff77d4c3ef30bc22f52fa7bb5da172d3b639`) merge per-component store derivations (`rustc`, `rust-std-*`, `rust-src`, `rustc-dev`) with `symlinkJoin`, sharing `libLLVM.so.*` (~`199 MiB`) across combinations via zero-cost symlinks, **except** both physically copy `bin/rustc` and `lib/librustc_driver-*.so` (~`156 MiB`) into `$out` and prepend `$out/lib` to `DT_RUNPATH`. If `$out/lib/librustc_driver-*.so` remained a symlink into the bare `/nix/store/<hash>-rustc/lib/` derivation, `rustc`'s `default_from_rustc_driver_dll()` (`dladdr` + `realpath`) would resolve its default sysroot to the bare `rustc` store path and fail to locate `rust-std` in the `symlinkJoin` tree. A custom verification runner that always passes explicit `--sysroot <merged_sysroot>` avoids this `156 MiB` per-combination copy completely.

---

### 2. Transitive `glibc` `ld.so` `DT_RPATH` Non-Inheritance (`elf/dl-load.c:1982`) and `/proc/self/maps` Full-Closure Verification

#### 2.1 Primary-Source Mechanism in `bminor/glibc@04e750e75b73957cf1c791535a3f4319534a52fc`

`Basis: source`

In GNU `glibc`, ELF dynamic library search precedence is controlled by two routines in `elf/dl-load.c`:

1. **Tag Initialization (`_dl_init_paths`, `elf/dl-load.c:763-797`):** When mapping an ELF object `l`, if `l->l_info[DT_RUNPATH]` (`d_tag = 29`) is non-NULL, `ld.so` populates `l->l_runpath_dirs` and unconditionally disables `l`'s `DT_RPATH` (`l->l_rpath_dirs.dirs = (void *) -1; /* The RPATH is ignored. */`, lines `763-777`). Only when `DT_RUNPATH` is absent does `ld.so` populate `l->l_rpath_dirs` from `DT_RPATH` (`d_tag = 15`, lines `778-797`).
2. **Per-Hop `loader->l_info[DT_RUNPATH]` Gate (`_dl_map_object` $\to$ `_dl_map_new_object`, `elf/dl-load.c:1980-2045`):** When an already-loaded object `loader` requests a `DT_NEEDED` SONAME `name` containing no `'/'`, `_dl_map_new_object` executes:

   ```c
   /* elf/dl-load.c:1980-2045 (bminor/glibc@04e750e75b73957cf1c791535a3f4319534a52fc) */
   /* When the object has the RUNPATH information we don't use any
      RPATHs.  */
   if (loader == NULL || loader->l_info[DT_RUNPATH] == NULL)
     {
       struct link_map *main_map = GL(dl_ns)[LM_ID_BASE]._ns_loaded;
       bool did_main_map = false;

       for (l = loader; l; l = l->l_loader)
         if (cache_rpath (l, &l->l_rpath_dirs, DT_RPATH, "RPATH"))
           {
             fd = open_path (name, namelen, mode, &l->l_rpath_dirs, ...);
             if (fd != -1)
               break;
             did_main_map |= l == main_map;
           }

       if (fd == -1 && !did_main_map
           && main_map != NULL && main_map->l_type != lt_loaded
           && cache_rpath (main_map, &main_map->l_rpath_dirs, DT_RPATH, "RPATH"))
         fd = open_path (name, namelen, mode, &main_map->l_rpath_dirs, ...);
     }

   /* Try the LD_LIBRARY_PATH environment variable.  */
   if (fd == -1 && __rtld_env_path_list.dirs != (void *) -1)
     fd = open_path (name, namelen, mode, &__rtld_env_path_list, ...);

   /* Look at the RUNPATH information for this binary.  */
   if (fd == -1 && loader != NULL
       && cache_rpath (loader, &loader->l_runpath_dirs, DT_RUNPATH, "RUNPATH"))
     fd = open_path (name, namelen, mode, &loader->l_runpath_dirs, ...);
   ```

   (The identical `if (loader->l_info[DT_RUNPATH] == NULL)` guard appears in `_dl_rtld_di_serinfo` at `elf/dl-load.c:2261-2292`.)

3. **Why `patchelf --force-rpath` on a Driver Executable `E` Alone Fails at Hop 2:**
   Upstream Rust bootstrap (`rust-lang/rust@0ef1bc386059596dada8fb65b50425aab2ea637a`, `src/bootstrap/src/core/builder/cargo.rs:347-365`) links `librustc_driver-<hash>.so` with `-Clink-args=-Wl,-rpath,$ORIGIN/../lib` under `--enable-new-dtags`, emitting **`DT_RUNPATH = $ORIGIN/../lib`** (`DT_RPATH = NULL`). If a `rustc_private` capture binary `E` is stamped with `patchelf --force-rpath --set-rpath <sysroot_A>/lib` while `<sysroot_A>/lib/librustc_driver-<hash_A>.so` retains its upstream ELF header:
   - **Hop 1 (`loader = E`, requesting `librustc_driver-<hash_A>.so`):** `E->l_info[DT_RUNPATH] == NULL`, so `ld.so` enters `dl-load.c:1982`, searches `E`'s `DT_RPATH` *before* `LD_LIBRARY_PATH`, and maps `L = <sysroot_A>/lib/librustc_driver-<hash_A>.so`.
   - **Hop 2 (`loader = L`, requesting `libLLVM.so.23.1-rust-1.102.0-nightly`):** Now `loader` is `L`, for which **`loader->l_info[DT_RUNPATH] != NULL`**. The guard at `dl-load.c:1982` evaluates to **`false`**, bypassing **both** the `l->l_loader` ancestor chain (`lines 1991-2002`) **and** `main_map->l_rpath_dirs` (`E`'s `DT_RPATH`, `lines 2006-2013`). `ld.so` searches `LD_LIBRARY_PATH` (`line 2032`) *before* `L`'s own `DT_RUNPATH = $ORIGIN/../lib` (`line 2040`).

#### 2.2 Live Cross-Nightly `libLLVM.so` Splicing and Lean 4 `libleanshared.so` Kernel Downgrade Proofs

`Basis: execution + source`

Unlike `librustc_driver-<16-hex>.so`, Rust's nightly `libLLVM` shared library uses an unhashed `DT_SONAME` keyed solely on `(llvm_major.minor, rust_channel_version)`. Three distinct `rustup` nightly toolchains examined in [`support/probe_loader_and_component_economics.py`](support/probe_loader_and_component_economics.py) ([`support/probe_loader_and_component_economics.json`](support/probe_loader_and_component_economics.json), `probe1_glibc_rpath_and_maps_closure`) export the **identical `DT_SONAME` `libLLVM.so.23.1-rust-1.102.0-nightly`** across incompatible LLVM builds:

- **Target toolchain (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`):** **LLVM `23.1.5`**, `librustc_driver-789fff502791d0da.so` (`DT_RUNPATH = $ORIGIN/../lib`), `libLLVM.so.23.1-rust-1.102.0-nightly` (`208,261,552` bytes, SHA-256 prefix `e504d51948337472`).
- **Colliding toolchain 2 (`8eb778d04094d3af4b26580cab327e0413eb1e02`, `2026-11-12`):** **LLVM `23.1.5`**, `libLLVM.so.23.1-rust-1.102.0-nightly`.
- **Poisoning toolchain 3 (`6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`, `2026-11-19`):** **LLVM `23.1.6`**, `libLLVM.so.23.1-rust-1.102.0-nightly` (`207,572,304` bytes, SHA-256 prefix `d57545f290b3417c`).

Compiling the `#![feature(rustc_private)]` MIR-capture executable `E` (`MIR_CAPTURE_DRIVER_RS`) against `3ef0c22cd` and executing Cases A, B, and C under `LD_DEBUG=libs` and in-process `/proc/self/maps` inspection establishes:

| Case | Executable `E` ELF Tags | `librustc_driver-*.so` ELF Tags | `LD_LIBRARY_PATH` | `LD_DEBUG=libs` Search Path Used for `libLLVM.so.23.1-rust-1.102.0-nightly` | Actual `/proc/self/maps` Loaded Closure | Driver-Only `/proc/self/maps` Check | Full-Closure `/proc/self/maps` Check |
| :--- | :--- | :--- | :--- | :--- | :--- | :---: | :---: |
| **Case A** (`patchelf --force-rpath` on `E` only) | `DT_RPATH = <3ef0c22cd>/lib`, `DT_RUNPATH = null` | Upstream `DT_RUNPATH = $ORIGIN/../lib`, `DT_RPATH = null` | `<6905905bb>/lib` (poisoned) | `<6905905bb>/lib (LD_LIBRARY_PATH)` (`E`'s `DT_RPATH` skipped!) | **`librustc_driver` from `3ef0c22cd` (`LLVM 23.1.5`) + `libLLVM` from `6905905bb` (`LLVM 23.1.6`)** (`rc = 0`!) | **`true` (FALSE PASS)** | **`false` (catches splice)** |
| **Case B** (`patchelf --force-rpath` on both `E` & staged driver) | `DT_RPATH = <staged>/lib`, `DT_RUNPATH = null` | Patched `DT_RPATH = $ORIGIN/../lib`, `DT_RUNPATH = null` | `<6905905bb>/lib` (poisoned) | `<staged>/lib/../lib (RPATH from .../librustc_driver-789fff502791d0da.so)` | Both `librustc_driver` and `libLLVM` from `3ef0c22cd` | `true` | `true` (mutates `.so`) |
| **Case C** (`env_remove("LD_LIBRARY_PATH")` + unmodified ELF) | Upstream `DT_RUNPATH = <3ef0c22cd>/lib`, `DT_RPATH = null` | Upstream `DT_RUNPATH = $ORIGIN/../lib`, `DT_RPATH = null` | Scrubbed (`unset`) | `<3ef0c22cd>/lib/../lib (RUNPATH from .../librustc_driver-789fff502791d0da.so)` | Both `librustc_driver` and `libLLVM` from `3ef0c22cd` | `true` | **`true` (zero ELF mutation)** |

**Parallel Lean 4 Unversioned `libleanshared.so` Downgrade (`support/probe_toolchain_isolation_results.json`, `cross_lean_unhashed_soname_hijack`):**
Lean 4's `bin/lean` links against unversioned, unhashed SONAMEs (`libleanshared.so`, `libleanshared_1.so`, `libleanshared_2.so`, `libInit_shared.so`) via `DT_RUNPATH = $ORIGIN/../lib:$ORIGIN/../lib/lean`. Invoking `<ELAN_HOME>/toolchains/leanprover--lean4---v4.35.0/bin/lean --version` cleanly prints `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`. Invoking **that exact `v4.35.0/bin/lean` binary** with `LD_LIBRARY_PATH=<ELAN_HOME>/toolchains/leanprover--lean4---v4.34.1/lib/lean` exits **`0`** and **silently executes the `v4.34.1` kernel** (`Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`).

**`libstd` Static-vs-`dlopen` Mapping Nuance and Complete Mitigation Contract (`Basis: source + execution + derived`):**
- Bootstrap's compiler wrapper (`rust-lang/rust@0ef1bc386059596dada8fb65b50425aab2ea637a`, `src/bootstrap/src/bin/rustc.rs:95-106`) strips `-C prefer-dynamic` when building `rustc_driver`, linking `std` statically into `librustc_driver-*.so`. However, `<sysroot>/lib/rustlib/<host>/lib/libstd-<hash>.so` enters `/proc/self/maps` via `dlopen` whenever `rustc_driver` expands a host `proc-macro` dylib (linked with `-C prefer-dynamic` and no `DT_RPATH`/`DT_RUNPATH`) or loads an external codegen backend (`librustc_codegen_*`).
- Therefore, sound multi-toolchain isolation requires two reinforcing defenses:
  1. **Parent Orchestrator Environment Scrubbing:** Unset `LD_LIBRARY_PATH`, `LD_PRELOAD`, `LD_AUDIT`, `DYLD_LIBRARY_PATH`, `DYLD_FALLBACK_LIBRARY_PATH`, `DYLD_INSERT_LIBRARIES`, `RUSTUP_TOOLCHAIN`, `ELAN_TOOLCHAIN`, `RUSTC_WRAPPER`, `RUSTC_WORKSPACE_WRAPPER`, and `RUSTC_OVERRIDE_VERSION_STRING` before spawning any compiler, MIR-capture driver, or proof-checker subprocess.
  2. **In-Process Full-Closure `/proc/self/maps` Verification:** Inside the `rustc_private` driver on Linux, parse `/proc/self/maps` after compiler initialization and verify that **every** mapped shared object matching `librustc_driver*`, `libLLVM*`, `libstd-*`, or `librustc_codegen*` canonicalizes (`realpath`) underneath `<expected_sysroot>`, and that both `librustc_driver` and `libLLVM` mappings are non-empty when running an LLVM-backed toolchain.

---

### 3. `rustc-dev` Component Economics, Driver Compilation Cost, and Monorepo Symbol Mangling

#### 3.1 Official Channel v2 Compressed vs. Unpacked Byte Footprints (`x86_64-unknown-linux-gnu`)

`Basis: execution + source`

Upstream `static.rust-lang.org` Channel v2 manifests (`channel-rust-1.100.0.toml`, SHA-256 `3051e859570f64a8c5acb9d09e87425db52c7d97287c67e8f6d57d7d34ef9258`; `2026-11-12` `channel-rust-nightly.toml`, SHA-256 `0e29758e4495709044396db6992e8bc44cd0109e7dbb21e430216cf368ac6c9d`) publish `.tar.xz` (`xz_url`/`xz_hash`) and `.tar.gz` (`url`/`hash`) archives (`.tar.zst` keys are supported by `rustup`'s `manifest.rs:183-206` parser but omitted on `static.rust-lang.org`). Exact HTTP `Content-Length` archive sizes and on-disk `lib/rustlib/manifest-*` file summations ([`support/probe_loader_and_component_economics.json`](support/probe_loader_and_component_economics.json), `probe3_component_economics`) are:

| Component (`x86_64-unknown-linux-gnu`) | Required at Capture Runtime? | `1.100.0` `.tar.xz` (`MiB` / Bytes) | `1.100.0` `.tar.gz` (`MiB` / Bytes) | `1.100.0` Installed (`MiB` / Bytes / Files) | `1.102.0-nightly` (`2026-11-12`) `.tar.xz` (`MiB` / Bytes) | `1.102.0-nightly` Installed (`MiB` / Bytes / Files) | Primary Payload Breakdown (`1.100.0`) |
| :--- | :---: | ---: | ---: | ---: | ---: | ---: | :--- |
| **`rustc`** | **YES** | **81.02 MiB** (`84,955,936`) | **136.94 MiB** (`143,589,524`) | **402.88 MiB** (`422,451,133` / `40` files) | **81.28 MiB** (`85,223,784`) | **405.69 MiB** (`425,400,882` / `42` files) | `libLLVM.so.23.1-rust-1.100.0-stable` (`198.60 MiB`), `librustc_driver-62d0ff9ea62999cc.so` (`156.49 MiB`), `bin/rustc`, `rust-lld` |
| **`rust-std`** | **YES** | **29.83 MiB** (`31,283,108`) | **47.88 MiB** (`50,206,772`) | **160.36 MiB** (`168,145,260` / `63` files) | **30.49 MiB** (`31,970,112`) | **141.57 MiB** (`148,451,676` / `64` files) | Target `.rmeta` (`113.83 MB`), `.rlib` (`36.79 MB`), `libstd-*.so` (`2.71 MiB`), sanitizer `.a` archives |
| **`rustc-dev`** | **NO (`0 B` at runtime; build-time only)** | **116.37 MiB** (`122,021,200`) | **210.87 MiB** (`221,116,662`) | **642.07 MiB** (`673,263,211` / `3,220` files) | **117.66 MiB** (`123,379,324`) | **595.10 MiB** (`624,005,105` / `3,263` files) | `rustc_macros` `.so` (`315.55 MB`), `librustc_*.rmeta` (`308.72 MB`), `.rs` (`34.63 MB`), `.rlib` (`13.23 MB`) |
| **`cargo`** | Orchestrator only | **10.44 MiB** (`10,946,408`) | **13.83 MiB** (`14,503,535`) | **34.91 MiB** (`36,605,223` / `44` files) | **10.32 MiB** (`10,822,836`) | **35.50 MiB** (`37,225,557` / `44` files) | `bin/cargo` (`34.54 MiB`) + manpages |
| **`rust-src`** | Optional (stdlib/Miri) | **5.67 MiB** (`5,943,864`) | **9.08 MiB** (`9,520,317`) | *(not installed on `1.100.0`)* | **5.75 MiB** (`6,034,488`) | **70.63 MiB** (`74,056,540` / `3,811` files) | `lib/rustlib/src/rust/library/**` |
| **Runtime Closure (`rustc` + `rust-std`)** | **100% sufficient** | **110.85 MiB** (`116,239,044`) | **184.82 MiB** (`193,796,296`) | **563.25 MiB** (`590,596,393` / `103` files) | **111.77 MiB** (`117,193,896`) | **547.26 MiB** (`573,852,558` / `106` files) | Complete runtime sysroot for prebuilt `rustc_private` shim |
| **Over-Provisioned (`rustc` + `rust-std` + `rustc-dev`)** | Bloated by `rustc-dev` | **227.22 MiB** (`238,260,244`) | **395.69 MiB** (`414,912,958`) | **1,205.31 MiB** (`1,263,859,604` / `3,323` files) | **229.43 MiB** (`240,573,220`) | **1,142.36 MiB** (`1,197,857,663` / `3,369` files) | `rustc-dev` adds **`51.2%` of `.tar.xz` download** and **`53.3%` of unpacked bytes** (`3,220` extra files) |

#### 3.2 Sub-Second Shim Compilation, `24.73 KiB` Binary Footprint, and Zero-`rustc-dev` Runtime Proof

`Basis: execution + source`

Compiling the zero-external-dependency `#![feature(rustc_private, cfg_version)]` MIR-capture shim (`MIR_CAPTURE_DRIVER_RS` in [`support/probe_loader_and_component_economics.py`](support/probe_loader_and_component_economics.py), which adapts across the `1.100.0` $\to$ `1.102.0` `rustc_driver::run_compiler` $\to$ `rustc_driver::compiler_entrypoint` rename via `#[cfg(version("1.102"))]`) yields:

| Toolchain | `RUSTC_BOOTSTRAP` Required? | Cold Compile Wall-Clock (`rustc -O`) | Warm Compile Median (3 Runs) | Peak RSS (`/usr/bin/time -v`) | Unstripped Binary | Stripped Binary (`strip --strip-all`) |
| :--- | :---: | ---: | ---: | ---: | ---: | ---: |
| **`rustc 1.100.0`** (`0ef1bc386`) | `true` (`"1"`) | **`592.15 ms`** | **`377.13 ms`** (`[398.91, 364.48, 377.13]`) | **`310.70 MiB`** (`318,152 KiB`) | `35,048` B (`34.23 KiB`) | **`25,320` B (`24.73 KiB`)** |
| **`rustc 1.102.0-nightly`** (`3ef0c22cd`) | `false` | **`399.33 ms`** | **`387.85 ms`** (`[382.21, 389.62, 387.85]`) | **`300.16 MiB`** (`307,364 KiB`) | `35,032` B (`34.21 KiB`) | **`25,296` B (`24.70 KiB`)** |

- **Zero-`rustc-dev` Runtime Execution Proofs (`zero_rustc_dev_runtime_proofs`):**
  1. Executing the stripped `25,320`-byte `1.100.0` shim against an official `rustup` `1.100.0-x86_64-unknown-linux-gnu` sysroot lacking `manifest-rustc-dev-x86_64-unknown-linux-gnu` (`0` bytes of `rustc-dev` installed; the 10 `librustc_*` files in `lib/rustlib/x86_64-unknown-linux-gnu/lib/` are `rustc-std-workspace-*`, `rustc_demangle`, and `librustc-stable_rt.*.a` shipped inside `rust-std`) succeeded with **`returncode = 0`** (`CAPTURE_REPORT ok=true version_str=Some("1.100.0 (0ef1bc386 2026-11-09)") bodies=2 bbs=21 stmts=96 terms=21 crates=19`).
  2. Executing the shim against a staged directory containing strictly the `40` files of `manifest-rustc-x86_64-unknown-linux-gnu` plus the `63` files of `manifest-rust-std-x86_64-unknown-linux-gnu` (`0` of the `3,220` `rustc-dev` files) likewise exited **`0`** with identical MIR counts.
- **When Prebuilt Spokes Suffice vs. When On-Demand Source Compilation (~`380 ms`) Is Mandatory (`probe2_monorepo_abi_and_version_formats`):**
  - For official upstream releases, shipping prebuilt per-release spoke binaries costs ~`25 KiB` per release (`< 510 KiB` for 20 releases) and allows developers with default `rustup` installations (`rustc` + `rust-std` only) to run MIR capture without downloading `116.37 MiB` / unpacking `642.07 MiB` of `rustc-dev`.
  - Conversely, custom monorepo compiler builds (which alter `__CARGO_DEFAULT_LIB_METADATA` / `-C metadata` or `CFG_VERSION` via `config.description`, `omit-git-hash = true`, or `channel = "dev"`, as in `rust-lang/rust@0ef1bc386059596dada8fb65b50425aab2ea637a` `src/bootstrap/src/core/session.rs:1373-1383` and `compiler/rustc_span/src/def_id.rs:152-195` `StableCrateId::new`) change both `librustc_driver-<unit_id>.so`'s `DT_SONAME` and every v0/legacy mangled symbol disambiguator (`CsdPlp0IeVrYh` vs. `Cs1dFbv31IN5J` vs. `Cs1eSHgjnL34m` vs. `Cs7AmVuOeRGaO` on identical compiler binary `3ef0c22cd`). Those custom toolchains cannot dynamically link an upstream prebuilt spoke and instead compile the zero-dependency shim from source against their own `rustc` + `rustc-dev` in ~`380 ms`.

---

### 4. Causal Provenance of `filesearch.rs:339-341` `AT_FDCWD` `"lib/rustlib"` (`1.54.0`–`1.102.0-nightly`) and All Seven Residual `Sysroot::default` Channels

#### 4.1 Exact Three-Commit History and Seven-Release Empirical Matrix

`Basis: source + execution`

Tracing `from_env_args_next()` in `compiler/rustc_session/src/filesearch.rs` across `rust-lang/rust` identifies the exact regression boundary:

1. **Working CAS Symlink Sysroot Introduction (Rust `1.50.0`–`1.53.0`, `rust-lang/rust@3f679fef23cd006c336e2a4f7c6707e119d22206`, `2020-11-20`):**
   Popped `<argv0>/bin/rustc` twice to obtain candidate sysroot `p`, constructed `let mut libdir = PathBuf::from(&p); libdir.push(find_libdir(&p).as_ref());`, and checked `if libdir.exists() { Some(p) } else { None }` (`filesearch.rs:160-164` at `1.53.0` tag `53cb7b09b00cbea8754ffb78e7e3cb521cb8af4b`), correctly testing `<p>/lib`.
2. **Causal Regression Commit (First Shipped in Rust `1.54.0`, `rust-lang/rust@b7c5599d22018ab6be88442c4668bc1697f85b8e`, `2021-05-10`, merged via `6fd7a6dc0f5c4c8fd51d57c0f4f795d52481f904`):**
   Introduced `rustc_target::target_rustlib_path(sysroot, target_triple)` returning a **relative** `PathBuf` (`"lib/rustlib/dummy"`). Every other caller in `b7c5599d2201` joined `sysroot`, **except** `from_env_args_next()` (`filesearch.rs:154-160`):

   ```rust
   p.pop();
   p.pop();
   let mut rustlib_path = rustc_target::target_rustlib_path(&p, "dummy");
   rustlib_path.pop(); // leaves relative PathBuf("lib/rustlib")
   if rustlib_path.exists() { Some(p) } else { None } // stats AT_FDCWD/"lib/rustlib"!
   ```

3. **Function Rename Preserving the Unjoined Relative Check (Rust `1.80.0`–`1.102.0-nightly`, `rust-lang/rust@b4c439c3de913953a2968c6917e125fafaacf886`, `2024-06-06`):**
   Renamed `target_rustlib_path` $\to$ `relative_target_rustlib_path` to clarify its relative return path (`make_target_lib_path` became `sysroot.join(rustlib_path).join("lib")`), while mechanically updating `from_env_args_next()` without adding `p.join(...)` (`compiler/rustc_session/src/filesearch.rs:339-341` in `0ef1bc386059596dada8fb65b50425aab2ea637a` and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).

Live execution across 7 installed releases ([`support/probe_loader_and_component_economics.json`](support/probe_loader_and_component_economics.json), `at_fdcwd_symlink_sysroot_matrix`) using a valid symlinked CAS sysroot `<TMPDIR>/cas_<tc>/bin/rustc -> <real_rustc>` (with `<TMPDIR>/cas_<tc>/lib/rustlib/x86_64-unknown-linux-gnu/lib` populated) confirms the two-sided failure across every tested release since `1.56.0`:

| Installed Toolchain | Commit SHA | `rustc --print sysroot` (Clean `CWD`) | `rustc --print sysroot` (`CWD` Contains `./lib/rustlib`) | `AT_FDCWD` Bug Present? |
| :--- | :--- | :--- | :--- | :---: |
| `1.56.0` (`2021-10-18`) | `09c42c45858d5f3aedfa670698275303a3d19afa` | `<RUSTUP_HOME>/toolchains/1.56.0-...` (ignores CAS!) | `<TMPDIR>/cas_1.56.0-...` (triggered by `CWD/lib/rustlib`) | **`true`** |
| `1.61.0` (`2022-05-18`) | `fe5b13d681f25ee6474be29d748c65adcd91f69e` | `<RUSTUP_HOME>/toolchains/1.61.0-...` | `<TMPDIR>/cas_1.61.0-...` | **`true`** |
| `1.78.0` (`2024-04-29`) | `9b00956e56009bab2aa15d7bff10916599e3d6d6` | `<RUSTUP_HOME>/toolchains/1.78.0-...` | `<TMPDIR>/cas_1.78.0-...` | **`true`** |
| `1.84.0` (`2025-01-07`) | `9fc6b43126469e3858e2fe86cafb4f0fd5068869` | `<RUSTUP_HOME>/toolchains/1.84.0-...` | `<TMPDIR>/cas_1.84.0-...` | **`true`** |
| `1.93.1` (`2026-02-11`) | `01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf` | `<RUSTUP_HOME>/toolchains/1.93.1-...` | `<TMPDIR>/cas_1.93.1-...` | **`true`** |
| `1.100.0` (`2026-11-09`) | `0ef1bc386059596dada8fb65b50425aab2ea637a` | `<RUSTUP_HOME>/toolchains/1.100.0-...` | `<TMPDIR>/cas_1.100.0-...` | **`true`** |
| `1.102.0-nightly` (`2026-11-11`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `<RUSTUP_HOME>/toolchains/nightly-...` | `<TMPDIR>/cas_nightly-...` | **`true`** |

#### 4.2 Complete Audit of `Sysroot::path()` vs. All Seven `Sysroot::all_paths()` / `Sysroot::default` Channels

`Basis: source + execution`

In `rust-lang/rust@0ef1bc386059596dada8fb65b50425aab2ea637a` (`compiler/rustc_session/src/config.rs:1410-1429`), `Sysroot` stores **both** `pub explicit: Option<PathBuf>` (`--sysroot`) and `pub default: PathBuf` (`filesearch::default_sysroot()`), exposing `path(&self)` (`explicit.as_deref().unwrap_or(&self.default)`) alongside `all_paths(&self)` (`explicit` chained before `default`):

1. **Target (`core`, `std`, `alloc`) and Host (`proc_macro`) Crate Loading Never Consults `Sysroot::default`:**
   `build_session` (`compiler/rustc_session/src/session.rs:1292, 1303, 1339-1371`) builds `Target::search` and all three `FileSearch` instances (`host_tlib_path`, `target_tlib_path`, `wasm_proc_macro_tlib_path`) strictly from **`sopts.sysroot.path()`**, which `CrateLocator` (`compiler/rustc_metadata/src/locator.rs:341, 347-353`) queries for all crate metadata/rlib lookups. Live probes (`sealed_sysroot_isolation_probes`) confirm fail-closed rejection (`returncode = 1`, `error[E0463]: can't find crate for 'core'` on `sealed_empty`; `error[E0463]: can't find crate for 'proc_macro'` on `sealed_no_proc_macro`) without falling back to `Sysroot::default`.

2. **All Seven Residual Channels Reading `Sysroot::all_paths()` or `Sysroot::default` Under Explicit `--sysroot`:**
   - **`P1` — Eager Startup Evaluation (`compiler/rustc_session/src/config.rs:1416-1418`):** `Sysroot::new(explicit)` unconditionally invokes `filesearch::default_sysroot()` (`from_env_args_next()` + `dladdr`) even when `explicit` is `Some(...)`.
   - **`P2` — Bundled Linker & Self-Contained Binaries (`compiler/rustc_session/src/session.rs:676-691`, `Session::get_tools_search_paths`):** Iterates `self.opts.sysroot.all_paths()` for `lib/rustlib/<host>/bin` (`rust-lld`, `gcc-ld/ld.lld`, `llvm-dwp`) and `bin/self-contained`. **Verified live (`sealed_sysroot_without_bin_tools_rust_lld_fallback`):** compiling `fn main() {}` with `--sysroot <TMPDIR>/sealed_no_tools_bin -Clinker-features=+lld -Clink-self-contained=+linker -Zunstable-options` (where `sealed_no_tools_bin` has no `bin/` directory) exits **`0`** by silently rescuing `rust-lld` from `Sysroot::default`!
   - **`P3` — External Dylib Codegen Backends (`compiler/rustc_interface/src/util.rs:540-560`, `get_codegen_sysroot`):** Iterates `sysroot.all_paths()` for `lib/rustlib/<host>/codegen-backends` when `-Zcodegen-backend=<non-builtin>` is requested.
   - **`P4` — Sanitizer Runtime Fallback (`compiler/rustc_codegen_ssa/src/back/link.rs:1778-1788`, `find_sanitizer_runtime`):** Checks `sess.target_tlib_path` (`--sysroot`) first, then explicitly falls back to `filesearch::make_target_lib_path(&sess.opts.sysroot.default, target_triple)` for `librustc*_rt.{asan,lsan,msan,tsan,ubsan}.a`.
   - **`P5` — GCC Codegen Backend `libgccjit.so` Search (`compiler/rustc_codegen_gcc/src/lib.rs:210-226`):** Iterates `sess.opts.sysroot.all_paths()`.
   - **`P6` — LLVM Enzyme and Offload Plugins (`compiler/rustc_codegen_llvm/src/llvm/enzyme_ffi.rs:440, 450` and `offload_ffi.rs:125`):** Iterates `sysroot.all_paths()`.
   - **`P7` — Sibling `rustc` Executable Lookup (`compiler/rustc_interface/src/util.rs:508-520`, `rustc_path`):** Ignores `sysroot.explicit` completely and probes `sysroot.default.join(env!("RUSTC_INSTALL_BINDIR")).join("rustc")` (used by `rustdoc`).

   **Complete Sysroot Sealing Contract (`Basis: derived`):** Passing `--sysroot <canonical_sysroot>` on the command line **and** assigning `config.opts.sysroot.default = canonical_sysroot.clone()` inside `rustc_driver::Callbacks::config` neutralizes `filesearch.rs:339-341` (`AT_FDCWD`) and seals all post-startup `all_paths()` / `sysroot.default` channels (`P2`–`P7`).

## Boundaries

- **Known not to apply (`patchelf --force-rpath` on the main executable alone as a transitive `LD_LIBRARY_PATH` defense):** Because `glibc` `elf/dl-load.c:1982` checks `loader->l_info[DT_RUNPATH] == NULL` on the **immediate** loading object (`librustc_driver-*.so`) rather than the main executable, setting `DT_RPATH` on a `rustc_private` binary alone does **not** protect `librustc_driver`'s own `DT_NEEDED` children (`libLLVM.so.*`) from `LD_LIBRARY_PATH` hijacking unless `librustc_driver-*.so` itself is also rewritten to `DT_RPATH` or `LD_LIBRARY_PATH` is scrubbed.
- **Known not to apply (`librustc_driver`-only `/proc/self/maps` residency checks):** Verifying only that `librustc_driver-<hash>.so` resolves inside the expected toolchain directory returns a false positive (`true`) during a live cross-nightly `libLLVM.so.23.1-rust-1.102.0-nightly` splice (`Case A`).
- **Known not to apply (Go `-lang=go1.X` as a standard-library symbol gate during `go build`):** Passing `-lang=go1.21` to `cmd/compile` rejects Go `1.22+` syntax, but `go build` still links newer `GOROOT` standard-library functions (such as Go `1.23`'s `slices.Backward`) unless `go vet` (`stdversion`) is executed.
- **Known not to apply (`rustc-dev` as a runtime dependency of compiled `rustc_private` drivers):** Prebuilt `rustc_private` binaries dynamically link `<sysroot>/lib/librustc_driver-*.so` and `<sysroot>/lib/libLLVM.so.*` from the `rustc` component and load target metadata from `rust-std`; `rustc-dev`'s `3,220` compiler `.rmeta`/proc-macro files (`642.07 MiB` on `1.100.0`) are unused at capture runtime.
- **Unsupported (dynamic linking of one prebuilt `rustc_private` binary across custom monorepo `librustc_driver.so` builds):** `rustc` provides no stable C/Rust dynamic ABI across `CFG_VERSION` or `-C metadata` changes; custom monorepo compilers alter `DT_SONAME` and `StableCrateId` symbol hashes and require compiling the shim against `rustc-dev`.
- **Unsupported (`$ORIGIN` inside `DT_NEEDED` on `musl` libc):** `python-build-standalone`'s `patchelf --replace-needed libpython3.x.so.1.0 '$ORIGIN/../lib/...'` technique works on GNU `glibc` `ld.so` but is explicitly unsupported by `musl`'s dynamic linker (`build-cpython.sh:923-936`).
- **Not examined (live dynamic-loader execution on macOS `dyld`, Windows PE loader, and Linux `musl`):** While macOS `@rpath`/`DYLD_FALLBACK_LIBRARY_PATH` (`rustup`), `install_name_tool -id` (`uv`), `lndir` (`rust-overlay`), and Windows `.lock` byte-offset / `PATH` mechanics (`anyzig`, `rustup`) were inspected in primary source, all live process-execution probes in `support/` ran on `x86_64-unknown-linux-gnu` (`glibc 2.43`). Live Apple SIP `DYLD_*` stripping and Windows DLL search-order hijacking across coexisting toolchains were not examined by execution.
- **Unknown (upstream `rust-lang/rust` disposition of `filesearch.rs:339-341` beyond `2026-11-22`):** Whether a future `rust-lang/rust` commit after `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` / `bdf712ee87c22a2b5c60db2e1af8a63e3cfd1a2e` fixes `from_env_args_next()` to check `p.join(&rustlib_path).exists()`—or removes implicit CAS symlink sysroot probing—is unknown; explicit `--sysroot` remains required for all released compilers in `1.54.0`..`1.102.0-nightly`.

## Evidence

### Primary Upstream Sources

- **`golang/go@2aae1000ea1d4b28923b96db28acf4e3b99d6aff` (`go1.27.3`):**
  - `src/cmd/go/internal/toolchain/select.go:45-86, 116-264, 283-285, 311-321, 353-547` (blob `bd2ae4ee2ed030c131a8756c17ea8a9ee7fa6d29`): `GOTOOLCHAIN` grammar, `modGoToolchain` (`go.work` shadowing `go.mod`), `GOTOOLCHAIN_INTERNAL_SWITCH_{VERSION,COUNT}`, ordered execute-bit and `_go.mod` unpacking.
  - `src/cmd/go/internal/toolchain/switch.go:34-113, 138-140, 166-198` (blob `b6a8910ff7f89600c1847b89c439bd4d96428086`) and `exec.go:23-63` (blob `df385e7b4712e346063cb0bd7319af5a81e2191e`).
  - `src/cmd/go/internal/modfetch/fetch.go:65-70, 182-250, 884-895` (blob `74cbbe06468c8eef7ba9e5f6f4f563875a647195`) and `sumdb.go:35-65, 102-104` (blob `6fb435b010d67c40d4a069f3049487af69b61535`): `golang.org/toolchain` non-bypassable `GOSUMDB` checks.
  - `src/cmd/go/internal/work/gc.go:69-83, 112-114` (blob `49b26e15609bb8da854c06ba3a225d28a2d0413d`) and `src/cmd/vendor/golang.org/x/tools/go/analysis/passes/stdversion/stdversion.go:46-114` (blob `3d44c4e86da6f9aa7bc984d850da9707532090fa`).
  - `src/cmd/distpack/pack.go:57-59, 212-248` (blob `53e9dbd73b64caa49b3bcbe39591f4466b523350`).
- **`rust-lang/rustup@edbc831cec44dc2858a4a4dce768c74361d027dc` (`1.29.3`):**
  - `src/config.rs:202-220, 356-359, 592-738` (blob `511b6de7e8f15927671efdf50aee5b053afa086b`), `src/toolchain/names.rs:346-435` (blob `f5181246b59331195bae2d81ae72e1957719c743`), `src/toolchain.rs:167-280` (blob `57ed54a6c66dd86483afb46888146dd20456a721`), `src/dist/manifest.rs:45-520` (blob `2540baa54448202efad969f4cb0b296cc6c56b07`), and `src/dist/download.rs:48-160` (blob `bbb1f785efb505995c938cb68a220cbbd72c4dd7`).
- **`leanprover/elan@3d5138e1526a569a23901b8ee559032793cf445e` (`v4.2.1`):**
  - `src/elan/config.rs:82-94, 156-240` (blob `4c7b6492b9be35ebb710a94c70a3a3e571204e62`), `src/elan/toolchain.rs:42-52, 147-158, 208-226, 262-274, 513-537` (blob `b5e90905a8cfe55ad6bafcc1aa972d3c50376209`), `src/elan-dist/src/dist.rs:47-61` (blob `fb903926f5781bb68c57f23ec8d143cad30f70a8`), `src/elan-dist/src/manifestation.rs:103-163` (blob `810fd05644bf90505b03037591d464616ee5e474`), and `src/elan-dist/src/download.rs:29-37` (blob `efaa6f5db4cea68d79a6c9a8034863934cd292cb`).
- **`marler8997/zigup@659aa0024ad2139c5d45ad1f4663834f14972c67` and `marler8997/anyzig@847a1628dd81f0b17335a024b16c97d4a03fabcb`:**
  - `zigup.zig:143-160, 283-290, 560-570, 635, 699-719, 920-1045, 1264-1325` (blob `6f7e86122e31fcad86b0c2df13e57790dafb4f5f`).
  - `anyzig` `src/main.zig:129-158, 204-251, 494-500, 785-907, 1461-1482, 1561-1712, 2052-2073` (blob `44fbd1e54039d3ef3585e2f4e201e64e451819ed`), `src/minisign.zig:24-97, 160-163` (blob `664656e5b4434ebd2c90ea2efe973e39e80797e3`), and `src/TmpFile.zig:8-200` (blob `0e3b1d5dd4aa560e0b603a33bce55cb1de4eee69`).
- **Other Multiplexer, Build-Graph, and Portable Runtime Sources:**
  - `nodejs/corepack@4210ff8b4dba03ab347098c3f59225f34cb05652`: `sources/specUtils.ts:18-57, 80-118, 162-254` (blob `8b73aacd20cbde57050278f59c7fedb6150b693a`), `sources/corepackUtils.ts:175, 210-211, 297-309` (blob `c02571ab6f093de5ef30afe83cc73dfbdbb23cee`), `sources/npmRegistryUtils.ts:19-20, 35-68` (blob `a7d110e95d54158fa5e4995c9941e30a240a25d1`), `sources/Engine.ts:216-223, 296-306` (blob `d935015964e69b9790452631754361a8c4ad2340`), `sources/commands/Pack.ts:38-78`, `sources/commands/InstallGlobal.ts:76-122`.
  - `bazelbuild/bazelisk@1e6aaf11d51e83ec8d18e66b461f49d4b7877321`: `core/core.go:58-79, 312-380, 418-575, 616-794` (blob `15b131a22fc28377d3cc3d70ac602123d1530c08`).
  - `astral-sh/python-build-standalone@98b27f721dbc67ded8c7d562aa5dd60c5507eda0`: `cpython-unix/build-cpython.sh:243-303, 703-705, 802-842, 895-949, 1219, 1423-1454` (blob `722ece906a569d19a8539b1073c9660ed68a7f3f`).
  - `astral-sh/uv@264d8b4a5e10d195d2cc2a34dffa807cfbe6298c`: `crates/uv-python-managed/src/{macos_dylib.rs:8-32, managed.rs:581-624}` and `crates/uv-python-discovery/src/{project.rs:115-208, version_files.rs:104-219, script.rs:153-200, 426-485}`.
  - `ziglang/zig@e4cbd752c8c05f131051f8c873cff7823177d7d3`: `src/libs/glibc.zig:38-56` (blob `b228ad60ad540d9ab3d491e33bfb84b55a8a0a39`) and `lib/libc/glibc/README.md:50-79`.
  - `bazelbuild/rules_rust@5d99ff2e58d1a0c9387fc4945029df11144bc8a3`: `rust/private/{repositories.bzl:224-348, 1401-1560, rust.bzl:827-833, sysroot.bzl:14-31, 92-106, 195-204, clippy_toolchain.bzl:204-212}`.
  - `oxalica/rust-overlay@5aa410a1df0e4e9c25f3818320651c2bddf66aff`: `lib/{manifests.nix:61-155, mk-component-set.nix:66-145, mk-aggregated.nix:24-120}` and `nix-community/fenix@012c1a71bd93921f320def3d0e586cc4dd332b65`: `default.nix:43-82`, `lib/{mk-toolchain.nix:30-83, 178-183, combine.nix:9-33}`.
- **`bminor/glibc@04e750e75b73957cf1c791535a3f4319534a52fc` and `rust-lang/rust`:**
  - `elf/dl-load.c:763-797, 1980-2045, 2261-2292`: `_dl_init_paths`, `_dl_map_new_object`, `_dl_rtld_di_serinfo`.
  - `rust-lang/rust@0ef1bc386059596dada8fb65b50425aab2ea637a` (`1.100.0`): `src/bootstrap/src/core/builder/cargo.rs:347-365, 965-1008`, `src/bootstrap/src/bin/rustc.rs:95-106`, `src/bootstrap/src/core/session.rs:1373-1383`, `compiler/rustc_span/src/def_id.rs:152-195`, `compiler/rustc_session/src/filesearch.rs:323-346`, `compiler/rustc_session/src/config.rs:1410-1429`, `compiler/rustc_session/src/session.rs:676-691, 1292-1371`, `compiler/rustc_metadata/src/locator.rs:341-353`, `compiler/rustc_interface/src/util.rs:508-560`, `compiler/rustc_codegen_ssa/src/back/link.rs:1778-1788`, `compiler/rustc_codegen_gcc/src/lib.rs:210-226`, `compiler/rustc_codegen_llvm/src/llvm/{enzyme_ffi.rs:440, 450, offload_ffi.rs:125}`.
  - `rust-lang/rust@3f679fef23cd006c336e2a4f7c6707e119d22206` (`1.50.0`), `rust-lang/rust@b7c5599d22018ab6be88442c4668bc1697f85b8e` (`1.54.0`), `rust-lang/rust@b4c439c3de913953a2968c6917e125fafaacf886` (`1.80.0`), and `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `compiler/rustc_driver_impl/src/lib.rs:172`).
- **Official Channel v2 Manifests & Component SHA-256 Digests (`2026-11-22`):**
  - `channel-rust-1.100.0.toml` (`3051e859570f64a8c5acb9d09e87425db52c7d97287c67e8f6d57d7d34ef9258`): `rustc` `.tar.xz` `f1d0b1dec81dab6f523cd098507763487b0d4bd7fd2c87582f154128719be03b`, `rust-std` `.tar.xz` `4591b6486594ded52ecd6135db95bf9355bbd3ca7a380888b141528bbcf9a5d4`, `rustc-dev` `.tar.xz` `d392d050c615f9aa85b46e6267c1d2a72ca41d8b2216a13895c872a2ee18cac6`, `cargo` `.tar.xz` `7e29ce07d7c6e92d1826870575ba27d57fff6cb3e754aa57d99099cb88fab35d`, `rust-src` `.tar.xz` `107afa7819b500c573b21a160b08f1a20bc2dfd99550717e1ffbbdb09da7ec6e`.
  - `2026-11-12/channel-rust-nightly.toml` (`0e29758e4495709044396db6992e8bc44cd0109e7dbb21e430216cf368ac6c9d`): `rustc` `.tar.xz` `67e94fee687d6fc8bbbf515f1bd67cead67334252bff3a015c7dcfb0e5beaa81`, `rust-std` `.tar.xz` `7c4e2d7e7f8826e34fb82a8ecac1bd954d8396186d1efe7f2a87116a1b036fc6`, `rustc-dev` `.tar.xz` `f4b3b21222355e7648e8762e620c8f1ee747bd64454c4f962c4741903773e609`.

### Preserved Package Support Artifacts (`2026-11-22`)

- [`support/probe_toolchain_isolation.py`](support/probe_toolchain_isolation.py) and [`support/probe_toolchain_isolation_results.json`](support/probe_toolchain_isolation_results.json): Standalone Python 3.10+ stdlib probe and recorded JSON output covering Go `1.27.3` `-lang=`/`stdversion`/`GOTOOLCHAIN`/sentinel checks, `rustup` `1.29.3` environment mutations, cross-nightly `libLLVM.so.23.1-rust-1.102.0-nightly` splicing, Lean `v4.35.0` $\to$ `v4.34.1` `libleanshared.so` hijacking, and `RUSTUP_TOOLCHAIN` split-brain `cargo` inheritance.
- [`support/probe_loader_and_component_economics.py`](support/probe_loader_and_component_economics.py) and [`support/probe_loader_and_component_economics.json`](support/probe_loader_and_component_economics.json): Standalone Python 3.10+ stdlib probe and recorded JSON output covering `glibc` `DT_RPATH` vs. `DT_RUNPATH` Cases A/B/C + `/proc/self/maps` closure checks, `CFG_VERSION`/`-C metadata` symbol-mangling divergence, Channel v2 component byte economics + `24.73 KiB` MIR-capture shim compile/runtime benchmarks with `0` bytes of `rustc-dev`, and the 7-release `filesearch.rs` `AT_FDCWD` matrix + sealed `--sysroot` probes.

## Revalidation

To check whether these findings still hold on a newer OS dynamic linker, multiplexer release, or `rustc` / `lean` version without repeating full source crawls:

1. **Rerun the Standalone Multiplexer & Loader Poisoning Probe (< 10 s, offline):**
   ```sh
   python3 -B support/probe_toolchain_isolation.py
   ```
   Inspect `support/probe_toolchain_isolation_results.json`: check `hijacked_llvm_from_toolchain_A` (confirming whether same-cycle Rust nightlies still share an unhashed `libLLVM.so.*` `DT_SONAME` and use `DT_RUNPATH`), `cross_lean_unhashed_soname_hijack.poisoned_stdout` (confirming whether `bin/lean` still links unversioned `libleanshared.so` via `DT_RUNPATH`), and `cargo_inheritance_matrix`.

2. **Rerun the Transitive `DT_RPATH`, Component Economics, and `filesearch.rs` Suite (< 15 s with `--offline`):**
   ```sh
   python3 -B support/probe_loader_and_component_economics.py --offline --output /tmp/reval_economics.json
   ```
   - Check `probe1_glibc_rpath_and_maps_closure.case_a_exe_dt_rpath_only`: if `driver_only_maps_check_passes_falsely` is `true` while `full_closure_maps_check_passes` is `false`, `librustc_driver-*.so` still ships with `DT_RUNPATH` (`readelf -d <sysroot>/lib/librustc_driver-*.so | grep -E 'RPATH|RUNPATH'`) and `glibc` `dl-load.c` still skips executable `DT_RPATH` when `loader->l_info[DT_RUNPATH] != NULL`.
   - Check `probe3_component_economics.driver_compile_and_runtime_benchmarks.zero_rustc_dev_runtime_proofs`: `returncode == 0` confirms prebuilt `rustc_private` shims still execute without `rustc-dev`.
   - Check `probe4_filesearch_and_sysroot_audit.at_fdcwd_symlink_sysroot_matrix`: `at_fdcwd_bug_present == false` on a newer `rustc` indicates `compiler/rustc_session/src/filesearch.rs` (`from_env_args_next`) was patched to join `p` before calling `.exists()`.

3. **Targeted Source Diff Checks on Multiplexer Upgrades:**
   - **`elan`:** Inspect `src/elan/toolchain.rs` (`lookup_unresolved_toolchain_desc` / `try_parse_path_toolchain`) and `src/elan-dist/src/download.rs` (`download_and_check`) to check whether relative path toolchains were blocked or SHA-256 verification was added.
   - **`rustc` `Sysroot`:** Run `git grep -n 'sysroot\.all_paths\|sysroot\.default' compiler/` in `rust-lang/rust` to check whether any new fallback channel beyond `P1`–`P7` was introduced.
