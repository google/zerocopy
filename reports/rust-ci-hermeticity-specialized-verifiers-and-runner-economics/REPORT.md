# Rust CI Hermeticity, Specialized Verifiers, and GitHub Actions Runner Economics

## Summary

Hermetic, cacheable Rust CI across heterogeneous check matrices requires closing concrete leakage vectors in `rustc`/`cargo`, specialized verification tools (`trybuild`, `cargo-semver-checks`, `cargo-llvm-cov`, `cargo-show-asm`, Miri, Kani, and `qemu-user`), and GitHub Actions runner packing:

1. **Path remapping vs. coverage:** Debug and test builds embed absolute checkout paths into DWARF debuginfo, breaking content-addressed caching across directories. Cargo `trim-paths` stabilized in Cargo `1.101` (unavailable on `<= 1.100.0`, which must use `RUSTFLAGS="--remap-path-prefix=..."`), while `rustc --remap-path-scope` is stable in `1.100.0`. Crucially, `rustc` defines `--remap-path-scope=object` (and therefore Cargo `trim-paths = "object"`) as `MACRO | DOCUMENTATION | DEBUGINFO | COVERAGE` — it **includes `coverage`**, which breaks `llvm-cov show` source resolution and `cargo-llvm-cov`'s workspace-anchored `-ignore-filename-regex` unless coverage is excluded (`--remap-path-scope=macro,debuginfo`), remapped relatively via `cargo llvm-cov --remap-path-prefix`, or paired with `LLVM_COV_FLAGS="-path-equivalence=..."`.
2. **Offline Cargo & Miri sysroot builds:** `cargo --offline` still creates/mutates `Cargo.lock`; only `--frozen` (`--locked --offline`) enforces strict offline lockfile hermeticity. For Miri, `rustc-build-sysroot` constructs a synthetic temporary workspace in `/tmp/rustc-build-sysroot-*` without copying `rust-src/library/.cargo/config.toml`, causing offline `cargo miri setup` to fail against `crates.io`. Because Cargo explicitly does not support `CARGO_SOURCE_*` environment variables (and silently ignores them), offline `cargo miri setup` requires either a pre-built `MIRI_SYSROOT` (which bypasses `setup` completely) or a dedicated `$CARGO_HOME/config.toml` pointing `[source.vendored-sources].directory` at `<sysroot>/lib/rustlib/src/rust/library/vendor`.
3. **Semver, UI, codegen, and randomized-layout determinism:** `cargo-semver-checks@v0.51.0` (`trustfall-rustdoc@v0.41.0`) supports rustdoc JSON `format_version`s `{57, 60, 61}` and requires an **exact** `format_version` match between baseline and current; pre-generated `--baseline-rustdoc` artifacts must be keyed by `(baseline_rev, rustdoc_format_version)`. `rustc -Z randomize-layout` defaults to a deterministic `seed = 0` (not OS randomness), so unseeded runs only exercise one fixed permutation while dynamic CI seeds break caching.
4. **Kani & cross-QEMU closures:** Kani `kani-0.68.0` couples a pinned nightly `rustc` to `kani-compiler`, `kani-driver`, CBMC `6.11.0` (with built-in CaDiCaL), and Kissat `4.0.1`, and supports offline installation via `--use-local-bundle` + `--use-local-toolchain` or pre-packaged `KANI_HOME`. Cross-execution via `CARGO_TARGET_<TRIPLE>_RUNNER="qemu-<arch> -L <sysroot>"` avoids host-global `binfmt_misc`, though `qemu-user` still delegates syscalls, `/proc`, and page size to the host Linux kernel.
5. **Runner economics:** Standard GitHub-hosted Linux runners provide 14 GB free SSD and a 10 GB per-repository Actions cache cap (7-day TTL, ~125 MB/s). Batching checks that share a toolchain closure onto one runner while retaining per-check derivation/cache granularity avoids both 14 GB disk exhaustion from monolithic multi-toolchain OCI images and $N \times$ fixed startup/transfer overhead from 1-check-per-job fan-out.

## Applicability

This report covers the interaction of:

- **Rust toolchains:** Stable `rustc 1.100.0 (0ef1bc386)` / `cargo 1.100.0 (3acc79c0c)` compared against nightly `rustc 1.102.0-nightly (3ef0c22cd)` / `cargo 1.102.0-nightly (c07ac2c4d)` on `x86_64-unknown-linux-gnu`. Behavior shared across both toolchains (path leakage in `dev` profile, `--offline` vs. `--frozen`, `--remap-path-scope=object` including `coverage`) is distinguished in **Findings** from version-specific behavior (`trim-paths` stabilization in Cargo `1.101`, rustdoc JSON `format_version` 57 vs. 61).
- **Specialized Rust verification and inspection tools:** `dtolnay/trybuild` (`1.0.125`), `obi1kenobi/cargo-semver-checks` (`v0.51.0`) paired with `obi1kenobi/trustfall-rustdoc` (`v0.41.0`), `taiki-e/cargo-llvm-cov` (`v0.9.2`), `pacak/cargo-show-asm` (`5c0b140c004b`), `rust-lang/miri` (`7e679961edcf`) paired with `RalfJung/rustc-build-sysroot` (`6534cd367f8d`), and `model-checking/kani` (`kani-0.68.0`).
- **CI runner and caching infrastructure:** Standard GitHub-hosted Linux runners (`ubuntu-24.04` / `ubuntu-latest`, `ubuntu-24.04-arm`, `ubuntu-slim`), `DeterminateSystems/nix-installer-action` (`v23`), and `Swatinem/rust-cache` (`v2.9.3`).

**Exact observation vs. broader applicability:**
- All execution probes ran on `x86_64-unknown-linux-gnu` (including network-isolated `bwrap --unshare-net` sandboxes for Miri). Findings derived from Rust/Cargo/tool source code (`rustc_span`, `cargo`, `trybuild`, `cargo-semver-checks`, `trustfall-rustdoc`, `cargo-llvm-cov`, `cargo-show-asm`, `miri`, `rustc-build-sysroot`, `kani`) apply across Unix hosts running those exact versions, except where host-kernel or OS-specific behavior is explicitly noted (e.g., Linux `binfmt_misc` and `qemu-user`).
- GitHub Actions runner specifications and cache limits have no immutable upstream revision hash; they reflect GitHub's published documentation as retrieved on `2026-11-21` and are subject to platform changes.

## Findings

### 1. Rust Check Hermeticity and Determinism Traps

#### 1.1 Path Leakage, `--remap-path-prefix`, `--remap-path-scope`, and `trim-paths`

Basis: execution + source + documentation

- **Debug/test builds leak absolute checkout paths by default:** Compiling an identical crate in two different directories (`dir_alpha_unique_path` vs. `dir_beta_unique_path`) with `cargo build --offline` (`dev` profile, also used by `cargo test`) on `rustc 1.100.0` embedded the absolute directory path into DWARF debuginfo and produced different binary SHA-256 digests (`e034afc1...` vs. `108ae748...`). Passing `RUSTFLAGS="--remap-path-prefix=<dir>=/src"` eliminated the leaked path and produced bit-for-bit identical debug binaries (`c4a6a702...`). In contrast, `cargo build --release --offline` (default `debug = 0`, crate invoking `file!()`) produced identical binaries (`6855691d...`) without leaking the checkout directory because Cargo passes relative source paths (`src/main.rs`) to `rustc`.
- **Stabilization boundary (`rustc 1.100.0` vs. `cargo 1.101+`):**
  - `rustc --remap-path-scope <macro,diagnostics,debuginfo,coverage,object,all>` is stable in `rustc 1.100.0`.
  - Cargo `profile.<name>.trim-paths` is **not** stabilized in `cargo 1.100.0` (`--config profile.dev.trim-paths="object"` exits with `101`: `feature 'trim-paths' is required`).
  - On `cargo 1.102.0-nightly`, passing `-Z trim-paths` warns `flag '-Z trim-paths' has been stabilized in the 1.101 release, and is no longer necessary`, and `--config profile.dev.trim-paths="object"` produces bit-for-bit identical debug binaries across checkout directories (`2e220f49...`) with zero leaked temp-dir bytes.
  - Consequently, multi-toolchain CI matrices that include toolchains `< 1.101` (such as MSRV pins) cannot rely solely on stable `trim-paths` and must pass explicit `RUSTFLAGS="--remap-path-prefix=..."` (covering workspace root, `CARGO_HOME`, and sysroot) when path-independent outputs are required.

#### 1.2 `CARGO_HOME`, Vendoring, `--offline` vs. `--frozen`, and `build.rs` Host Probing

Basis: execution + documentation

- **`--offline` mutates `Cargo.lock`; `--frozen` enforces strict lockfile and offline hermeticity:** Running `cargo check --offline` on a crate with no `Cargo.lock` on `cargo 1.100.0` succeeded (`exit 0`) and created `Cargo.lock`. Running `cargo check --frozen` failed (`exit 101`: `cannot create the lock file ... because --frozen was passed to prevent this`). Hermetic offline builds require `cargo vendor` paired with `[source.crates-io] replace-with = "vendored-sources"` in `.cargo/config.toml` (or `$CARGO_HOME/config.toml`), an isolated `CARGO_HOME`, and `--frozen` (equivalent to `--locked --offline`).
- **`build.rs` scripts are a primary host-leak vector:** `build.rs` executes arbitrary host Rust code with access to host `PATH`, `HOST` vs. `TARGET`, absolute `OUT_DIR`, `RUSTC`, `CC`/`CFLAGS`, and `pkg-config` system search paths. Even inside a vendored `--frozen` build, unisolated `PATH` or `pkg-config` allows `build.rs` (including `cc` and `pkg-config` crates) to bind silently to host compilers or system headers/libraries unless executed inside a Nix sandbox or minimal pinned OCI rootfs.

#### 1.3 `trybuild` UI Stderr Tests

Basis: source (`dtolnay/trybuild` `1.0.125`, `src/normalize.rs`, `src/env.rs`)

- `src/normalize.rs` applies 25 sequential normalization passes (`Basic`, `RustLib`, `CargoRegistry`, `PathDependencies`, `WorkspaceLines`, `RelativeToDir`, `DependencyVersion`, `CustomRegistry`, etc.) parameterized by `Context { krate, source_dir, workspace, input_file, target_dir, path_dependencies }`, and accepts a match against any historical normalization variation so upgrading `trybuild` does not invalidate older snapshots.
- `src/env.rs` parses `TRYBUILD`: unset or `"wip"` runs in verification mode; `"overwrite"` mutates committed `.stderr` files in place and must never be enabled in CI verification jobs.
- Despite path/version normalization, `rustc` diagnostic wording, span formatting, lint suggestions, and target-dependent type layouts (pointer width, `usize`/`isize`, target `#[cfg]`) vary across compiler releases and target triples. `trybuild` checks are therefore hermetic only when pinned to an exact `rustc` toolchain and target triple.

#### 1.4 `cargo-semver-checks` Offline Baselines and Rustdoc JSON Version Matching

Basis: source (`obi1kenobi/cargo-semver-checks` `v0.51.0`; `obi1kenobi/trustfall-rustdoc` `v0.41.0`) + execution

- **Network vs. offline baselines (`cargo-semver-checks/src/main.rs:456-510, 641-660`):**
  - `--baseline-version <VER>` constructs `Rustdoc::from_registry(baseline_version)`, fetching from the mutable crates.io index (non-hermetic).
  - Hermetic offline alternatives supported directly in `src/main.rs`:
    1. `--baseline-rustdoc <JSON_PATH>` (`Rustdoc::from_path`): consumes a pre-generated, content-pinned rustdoc JSON artifact with zero network access and zero baseline compilation.
    2. `--baseline-root <DIR>` (`lenient_baseline_root`): compiles a locally checked-out, vendored baseline directory (paired with `--offline`).
    3. `--baseline-rev <REV>` (with `--baseline-root`): checks out a local git revision (`Rustdoc::from_git_revision`), which still requires vendored dependencies for that baseline revision if offline.
- **Strict rustdoc JSON `format_version` equality requirement:**
  - `cargo-semver-checks@v0.51.0` (`Cargo.toml:21`) enables only `v57`, `v60`, and `v61` on `trustfall_rustdoc = "0.41.0"` (`default-features = false, features = ["v57", "v60", "v61", "rayon", "rustc-hash"]`). Format versions `58` and `59` are not supported.
  - Spot-checking via `RUSTC_BOOTSTRAP=1 rustdoc +<tc> -Z unstable-options --output-format=json` showed `rustc 1.93.1`, `1.94.0`, and `1.96.0` emit `format_version=57`, while `rustc 1.99.1`, `1.100.0`, and `1.102.0-nightly (2026-11-11)` emit `format_version=61`.
  - In `obi1kenobi/trustfall-rustdoc@v0.41.0` (`src/versioned.rs:139-206`), `VersionedRustdocAdapter::new(current, baseline)` matches **only identical version pairs**: `(V57, Some(V57))`, `(V60, Some(V60))`, and `(V61, Some(V61))`. Any cross-version pair falls through to:
    ```rust
    bail!(
        "version mismatch between current (v{}) and baseline (v{}) format versions",
        c.version(),
        b.version()
    )
    ```
  - **Implication:** A pre-generated `--baseline-rustdoc` JSON produced by an older `rustc` works with a newer `rustc` **only if both emit the exact same `format_version`** (and that version is in `{57, 60, 61}`). It is not sufficient for both versions to be individually supported. Cached baseline JSONs must be keyed by `(baseline_rev, rustdoc_format_version)` or regenerated with the current toolchain whenever a toolchain update changes `format_version`.

#### 1.5 `cargo-llvm-cov`, Coverage + Path Remapping, `cargo-show-asm`, and `-Z randomize-layout`

Basis: source (`taiki-e/cargo-llvm-cov` `v0.9.2`; `rust-lang/rust` `compiler/rustc_span/src/lib.rs`, `compiler/rustc_session/src/options.rs`; `rust-lang/cargo` `src/compiler/trim_paths.rs`; `pacak/cargo-show-asm` `5c0b140c004b`) + execution + documentation

- **`cargo-llvm-cov@v0.9.2` tooling and cache isolation (`src/context.rs:130-185, 202`, `src/main.rs:157-290`, `src/cargo.rs:89-90`):**
  - Requires `$sysroot/lib/rustlib/$host_triple/bin` from `llvm-tools-preview` (or explicit `LLVM_COV` and `LLVM_PROFDATA` environment variables in Nix/custom toolchains).
  - Injects `-C instrument-coverage` into `RUSTFLAGS` / `CARGO_ENCODED_RUSTFLAGS` / `CARGO_TARGET_<TRIPLE>_RUSTFLAGS` and redirects artifacts into `<target_dir>/llvm-cov-target` because coverage-instrumented artifacts cannot share a cache with uninstrumented builds.
  - Sets `LLVM_PROFILE_FILE` for `.profraw` outputs, which must be writable and isolated per run to avoid cross-run profile contamination.
- **Path remapping interaction — `--remap-path-scope=object` and `trim-paths = "object"` break `llvm-cov show`:**
  - In `rust-lang/rust` (`compiler/rustc_span/src/lib.rs:243-258`), `RemapPathScopeComponents::OBJECT` is defined as:
    ```rust
    const OBJECT = Self::MACRO.bits() | Self::DOCUMENTATION.bits() | Self::DEBUGINFO.bits() | Self::COVERAGE.bits();
    ```
  - In `rust-lang/cargo` (`src/compiler/trim_paths.rs:65-81`), Cargo forwards the profile `trim-paths` value directly as `--remap-path-scope={trim_paths}` plus `--remap-path-prefix=...`.
  - Consequently, `--remap-path-scope=object` and `trim-paths = "object"` **include `coverage`** and rewrite LLVM coverage mapping paths identically to `all` or `coverage`.
  - Empirical execution on `rustc 1.100.0` + `llvm-profdata` + `llvm-cov`:

    | Remapping Flags | `lcov` `SF:` Path | `llvm-cov report` | `llvm-cov show` (Source Resolution) |
    |---|---|---|---|
    | None (default) | `/tmp/.../lib.rs` | OK | OK (`has_source=True`) |
    | `--remap-path-prefix=<tmp>=/src` (default `all`) | `/src/lib.rs` | OK (counts only) | Broken (`error: /src/lib.rs: No such file or directory`) |
    | `--remap-path-prefix=<tmp>=/src --remap-path-scope=object` | `/src/lib.rs` | OK (counts only) | Broken (`error: /src/lib.rs: No such file or directory`) |
    | `--remap-path-prefix=<tmp>=/src --remap-path-scope=coverage` | `/src/lib.rs` | OK (counts only) | Broken (`error: /src/lib.rs: No such file or directory`) |
    | `--remap-path-prefix=<tmp>=/src --remap-path-scope=debuginfo` | `/tmp/.../lib.rs` | OK | OK (`has_source=True`) |
    | `--remap-path-prefix=<tmp>=/src --remap-path-scope=macro,debuginfo` | `/tmp/.../lib.rs` | OK | OK (`has_source=True`) |
    | `--remap-path-prefix=<tmp>=/src` + `llvm-cov -path-equivalence=/src,<tmp>` | `/src/lib.rs` | OK | OK (`has_source=True`) |
    | `--remap-path-prefix=<tmp>/=` (relative, as in `cargo llvm-cov --remap-path-prefix`) | `lib.rs` | OK | OK (`has_source=True`, when run from `<tmp>`) |

  - Additionally, `cargo-llvm-cov@v0.9.2` (`src/report.rs:942-979`) anchors its default `-ignore-filename-regex` on `^{workspace_root}`, so external `RUSTFLAGS="--remap-path-prefix=..."` breaks workspace-anchored exclusions (`tests/`, `examples/`, `benches/`, `--exclude-from-report`).
  - **Hermetic mitigations for coverage jobs:**
    1. Exclude `coverage` from remapping (`--remap-path-scope=macro,debuginfo` in `RUSTFLAGS`, or disable `trim-paths` on the coverage profile).
    2. Use `cargo llvm-cov --remap-path-prefix`, which injects `--remap-path-prefix {workspace_root}/=` (relative paths) and switches `-ignore-filename-regex` to relative matching (`src/cli.rs:75` notes this is not fully compatible with doctests).
    3. Pair synthetic-prefix remapping with `LLVM_COV_FLAGS="-path-equivalence=/src,<workspace_root>"` (`src/context.rs:202` forwards `LLVM_COV_FLAGS` directly to `llvm-cov`) plus an explicit `--ignore-filename-regex` if workspace-anchored exclusions are needed.
- **`cargo-show-asm` (`5c0b140c004b`, `src/opts.rs:210-217`):** Passing `--native` sets `-C target-cpu=native`, probing the runner's host CPU features (AVX2/AVX-512, etc.) and causing non-determinism across heterogeneous CI runners. Hermetic codegen snapshots must pin both the exact `rustc`/LLVM version and an explicit `--target-cpu <cpu>` (or target baseline).
- **`-Z randomize-layout` defaults to seed `0`, not OS randomness:** In `rust-lang/rust` (`compiler/rustc_session/src/options.rs:2718, 2910`), `layout_seed: Option<u64>` defaults to `None`. Executing an 8-field struct layout probe on `rustc 1.102.0-nightly (3ef0c22cd)` confirmed that 5/5 unseeded runs produced the exact same layout (`12,24,4,32,2,0,8,16`) and identical binary hash as `-Z layout-seed=0`, whereas default (non-randomized) layout was `28,24,16,0,29,26,20,8`, `-Z layout-seed=1` yielded `18,32,0,8,19,16,36,24`, and `-Z layout-seed=42` yielded `0,8,28,32,24,2,4,16` (each deterministic for a fixed seed). Thus: (a) passing `-Z randomize-layout` alone is deterministic but tests only one fixed permutation (`seed = 0`); (b) injecting a dynamic seed (e.g., `$RANDOM` or timestamp) breaks cacheability unless seeds are pinned constants per CI matrix entry (`-Z layout-seed=<pinned_constant>`).

### 2. Specialized Verifier Packaging: Miri and Kani

#### 2.1 Miri (`rust-lang/miri@7e679961edcf`, `RalfJung/rustc-build-sysroot@6534cd367f8d`)

Basis: source + execution (inside `bwrap --unshare-net`)

- **Pre-built sysroot fast path (`cargo-miri/src/setup.rs:28-31`):** When `MIRI_SYSROOT` is set and the subcommand is not `cargo miri setup`, `cargo-miri` skips sysroot setup entirely and uses `MIRI_SYSROOT` directly. Building `MIRI_SYSROOT` once per target triple in a dedicated Nix derivation or OCI layer and exporting `MIRI_SYSROOT` at test time is the cleanest hermetic pattern.
- **Source discovery (`cargo-miri/src/setup.rs:34-67`):** When `cargo miri setup` runs, it locates `rust-src` via `MIRI_LIB_SRC` (must end in `.../library`) or auto-detects `$sysroot/lib/rustlib/src/rust/library` (attempting `rustup component add rust-src` if absent, which fails offline).
- **The `rustc-build-sysroot` temp-dir vendor trap and Cargo env-var non-support:**
  - Modern `rust-src` (`rustc 1.102.0-nightly`) bundles `library/Cargo.lock`, `library/vendor/` (`hashbrown`, `libc`, `cfg-if`, `addr2line`, `gimli`, `miniz_oxide`, etc.), and `library/.cargo/config.toml` (`[source.crates-io] replace-with = "vendored-sources"`).
  - However, `SysrootBuilder::build_from_source` (`RalfJung/rustc-build-sysroot@6534cd367f8d`, `src/lib.rs:350-371, 451-510`) creates a fresh temporary workspace in `/tmp/rustc-build-sysroot-*`, copies `Cargo.lock`, generates `Cargo.toml` + `lib.rs`, and invokes `cargo` **without copying `library/.cargo/config.toml`**. It inherits `CARGO_HOME` (overriding only `CARGO_ENCODED_RUSTFLAGS`, `CARGO_TARGET_DIR`, `CARGO_BUILD_BUILD_DIR`, and `__CARGO_DEFAULT_LIB_METADATA`).
  - Furthermore, per `rust-lang/cargo` (`doc/book/src/reference/config.md:231-233, 1390-1400`), both `source.<name>.replace-with` and `source.<name>.directory` are explicitly marked `Environment: not supported`; Cargo silently ignores `CARGO_SOURCE_*` environment variables.
  - Empirical verification inside `bwrap --unshare-net` (empty `CARGO_HOME`, fresh `MIRI_SYSROOT`, `rustc 1.102.0-nightly (3ef0c22cd)`):

    | Configuration | Exit | Observed Behavior |
    |---|---:|---|
    | No vendor config | `1` | Cargo tries to fetch `cfg-if` from `index.crates.io` (`Could not resolve host: index.crates.io`). |
    | `CARGO_NET_OFFLINE=true`, `CARGO_SOURCE_CRATES_IO_REPLACE_WITH=vendored-sources`, `CARGO_SOURCE_VENDORED_SOURCES_DIRECTORY=<sysroot>/lib/rustlib/src/rust/library/vendor` | `1` | Cargo silently ignores `CARGO_SOURCE_*` and still searches `crates.io index` (`no matching package named 'cfg-if' found`). |
    | Dedicated `$CARGO_HOME/config.toml` with `[net] offline = true`, `[source.crates-io] replace-with = "vendored-sources"`, `[source.vendored-sources] directory = "<sysroot>/lib/rustlib/src/rust/library/vendor"` | `0` | Succeeds completely offline in `24.51s`, producing all 27 `.rlib` files in `$MIRI_SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/lib`. |

  - Keep this dedicated `CARGO_HOME` scoped to the Miri sysroot build step so its `[source.vendored-sources]` entry does not collide with the workspace's own vendored crates.

#### 2.2 Kani (`model-checking/kani@kani-0.68.0`)

Basis: source (`src/setup.rs:22-244`, `kani-dependencies`, `kani-driver/src/call_cbmc.rs:153-155, 437-463`, `kani-driver/src/session.rs:43, 72, 423-473`)

- **Default online setup:** `cargo kani setup` downloads `kani-<VERSION>-<TARGET>.tar.gz` from GitHub Releases into `${KANI_HOME:-$HOME/.kani}/kani-<VERSION>`, reads `rust-toolchain-version` from the unpacked bundle, runs `rustup toolchain install <toolchain_version>`, and creates `${KANI_HOME}/kani-<VERSION>/toolchain` symlink (`src/setup.rs:88-90, 150-184, 218-244`).
- **Pinned runtime/solver closure in `kani-0.68.0`:**
  - `kani-compiler` (linked against the exact pinned nightly `rustc` named in `rust-toolchain-version`), `kani-driver`, and Kani standard libraries (`lib/`).
  - **CBMC `6.11.0`** (`cbmc`, `goto-cc`, `goto-instrument`, `goto-synthesizer`).
  - **CaDiCaL** (compiled into CBMC; default solver in `call_cbmc.rs:155`: `DEFAULT_SOLVER = CbmcSolver::Cadical`).
  - **Kissat `4.0.1`** (bundled external SAT solver invoked via `--external-sat-solver`).
  - Optional SMT backends (`Z3` via `--z3`, `Bitwuzla`, `Cvc5` if selected via `--solver`).
- **Offline/hermetic packaging mechanisms built into `kani-0.68.0`:**
  1. `cargo kani setup --use-local-bundle <tar.gz> --use-local-toolchain <path>` (`src/setup.rs:77-78, 104, 157-173`) verifies that the local toolchain's `rustc --version` matches `rust-toolchain-version` and unpacks/symlinks completely offline.
  2. Pre-packaging `${KANI_HOME}/kani-<VERSION>` (including the `toolchain` symlink and `bin/` with `kani-compiler`, `kani-driver`, `cbmc`, `kissat`) as a Nix derivation or OCI image layer and exporting `KANI_HOME` allows `cargo kani` to run completely offline without invoking `setup` or `rustup`.

### 3. Cross-Compilation and QEMU User-Mode Host Coupling

Basis: documentation (Linux Kernel `binfmt_misc`; Cargo Target Configuration; QEMU User Mode Emulation)

- **`binfmt_misc` vs. explicit `CARGO_TARGET_<TRIPLE>_RUNNER`:**
  - `binfmt_misc` registrations reside in host-global `/proc/sys/fs/binfmt_misc` (not namespaced per container/Nix sandbox in standard Linux CI). Relying on `binfmt_misc` couples execution to whichever `qemu-user` binary and flags (`F` fix-binary) the host runner registered, and fails inside unprivileged Nix sandboxes.
  - Setting `CARGO_TARGET_<UPPER_SNAKE_TRIPLE>_RUNNER="qemu-<arch> -L <sysroot>"` invokes an explicit, pinned `qemu-user` binary and pinned dynamic-linker sysroot inside the container or Nix derivation with zero host `binfmt_misc` dependency.
- **Residual host-kernel leaks under explicit `qemu-user`:**
  - `qemu-user` translates guest instructions and syscall ABI structures, but delegates syscalls directly to the **host Linux kernel**.
  - Observable host coupling remains for: (a) syscall availability and translation gaps (`statx`, `io_uring` often returning `ENOSYS`, `getrandom`, seccomp/namespace syscalls), (b) `/proc` and `auxv` values (`/proc/cpuinfo`, `/proc/self/maps`, and `sysconf(_SC_PAGESIZE)` reflecting host 4 KiB pages rather than 64 KiB on some `aarch64` hardware), and (c) unaligned-access trap behavior on big-endian targets (`aarch64_be`, `powerpc64`, `s390x`) even though endian-swapped syscall translation catches endianness bugs.
  - **Non-Linux targets:** `avr` has no Linux syscall ABI and therefore no `qemu-user` binary (requires `simavr` or compile-only checks); `wasm32-wasip1`/`wasm32-wasip2` executes hermetically via pinned `wasmtime` (`CARGO_TARGET_WASM32_WASIP1_RUNNER="wasmtime"`) in a capability-based sandbox independent of host syscalls; `wasm32-unknown-unknown` requires `wasm-bindgen-test-runner` plus a headless browser or Node.js.

### 4. Summary of Rust CI Hermeticity Hazards

| Tool / Mechanism | Primary Non-Hermeticity / Non-Determinism Hazard | Hermetic Mitigation | Basis |
|---|---|---|---|
| `rustc` / `cargo` (`dev`/`test`) | Absolute checkout and `CARGO_HOME` paths leak into DWARF debuginfo, `file!()`, and binaries | `trim-paths = "object"` / `"all"` (Cargo `>= 1.101`, excluding coverage jobs) or `RUSTFLAGS="--remap-path-prefix=..."` | execution, documentation |
| `cargo` dependency resolution | `--offline` still creates/mutates `Cargo.lock`; default fetches crates.io | `cargo vendor` + `.cargo/config.toml` source replacement + `--frozen` + isolated `CARGO_HOME` | execution, documentation |
| `build.rs` (`cc`, `pkg-config`) | Probes host `PATH`, system C compilers, host headers/libs, `OUT_DIR` | Run inside Nix sandbox or minimal pinned OCI rootfs; avoid implicit host tool discovery | documentation |
| `trybuild` (`1.0.125`) | Diagnostic wording/spans vary by exact `rustc` version and target triple; `TRYBUILD=overwrite` mutates snapshots | Pin exact `rustc` version and target triple; forbid `TRYBUILD=overwrite` in CI | source |
| `cargo-semver-checks` (`v0.51.0`) / `trustfall-rustdoc` (`v0.41.0`) | `--baseline-version` fetches live crates.io index; `VersionedRustdocAdapter::new` requires exact rustdoc JSON `format_version` match in `{57, 60, 61}` | Pin `--baseline-rustdoc <json>` keyed by `(baseline_rev, rustdoc_format_version)` or `--baseline-root <vendored_dir>` + `--offline` | source, execution |
| `cargo-llvm-cov` (`v0.9.2`) | Needs `llvm-tools-preview`; `-C instrument-coverage` invalidates normal build cache; `--remap-path-scope=object` and `trim-paths = "object"` include `coverage` and break `llvm-cov show` and workspace-anchored ignore regexes | Bundle `llvm-tools-preview` (or `LLVM_COV`/`LLVM_PROFDATA`); keep `llvm-cov-target` separate; isolate `LLVM_PROFILE_FILE`; use `--remap-path-scope=macro,debuginfo`, `cargo llvm-cov --remap-path-prefix`, or `LLVM_COV_FLAGS="-path-equivalence=..."` | source, execution |
| `cargo-show-asm` (`5c0b140c004b`) | `--native` (`-C target-cpu=native`) leaks runner CPU microarchitecture; output sensitive to LLVM version | Pin exact `rustc`/LLVM version and explicit `--target-cpu` | source, documentation |
| `-Z randomize-layout` | Unseeded defaults to `seed = 0` (single fixed layout); dynamic CI seeds break determinism/caching | Explicitly pin `-Z layout-seed=<N>` per matrix entry | execution, source |
| Miri (`7e679961edcf`) / `rustc-build-sysroot` (`6534cd367f8d`) | `cargo miri setup` runs in `/tmp` without copying `library/.cargo/config.toml`; `CARGO_SOURCE_*` env vars are silently ignored by Cargo | Pre-build `MIRI_SYSROOT` per target in a dedicated derivation/layer, or pass a dedicated `$CARGO_HOME/config.toml` pointing `[source.vendored-sources].directory` at `<sysroot>/lib/rustlib/src/rust/library/vendor` | source, execution |
| Kani (`kani-0.68.0`) | `cargo kani setup` downloads release tarball and runs `rustup toolchain install` into `~/.kani/kani-<ver>` | Pre-package `${KANI_HOME}/kani-<ver>` (`kani-compiler`, `kani-driver`, `cbmc 6.11.0`, `kissat 4.0.1`, `toolchain` symlink) via Nix/OCI or `--use-local-bundle` + `--use-local-toolchain` | source |
| Cross `qemu-user` | `binfmt_misc` is host-kernel global; even explicit `qemu-user` leaks host kernel syscalls (`io_uring`, `statx`), `/proc`, page size | Use explicit `CARGO_TARGET_<TRIPLE>_RUNNER="qemu-<arch> -L <sysroot>"`; use `simavr`/compile-only for `avr` and `wasmtime` for `wasm32-wasip*` | documentation |

### 5. GitHub Actions Runner Startup, Closure Transfer, and Packing Economics

Basis: documentation (GitHub Docs; `DeterminateSystems/nix-installer-action` `v23`; `Swatinem/rust-cache` `v2.9.3`) + derived

- **Standard GitHub-hosted Linux runner limits (`ubuntu-24.04` / `ubuntu-latest`, as documented on `2026-11-21`):**
  - Public repositories: 4 vCPU, 16 GB RAM, **14 GB SSD** free space (`x64` or `ubuntu-24.04-arm`), 20 concurrent jobs on Free.
  - Private repositories: 2 vCPU, 8 GB RAM, **14 GB SSD** free space.
  - `ubuntu-slim`: 1 vCPU, 5 GB RAM, 14 GB SSD (container-based).
  - Actions cache service: **10 GB** default total storage per repository (LRU eviction when exceeded; expandable on paid plans), **7-day** unused entry expiration, ~1 Gbps (~125 MB/s) effective cache transfer ceiling.
- **Closure transfer and caching architecture tradeoffs (derived from runner limits and tool architectures):**

  | Strategy | Closure Transfer & Disk Footprint (vs. 14 GB SSD) | Cache Granularity & 10 GB GHA Cap | Startup / Setup Overhead | Local ↔ CI Hermeticity | Best Fit |
  |---|---|---|---|---|---|
  | **Monolithic GHCR OCI image** | High (4–10+ GB unpacked); risks 14 GB SSD exhaustion on standard runners without disk cleanup | OCI layer cache (outside 10 GB GHA cache); coarse invalidation | High on cold pull (1–4 min), low once cached on self-hosted | High (same container runs locally) | Small number of heavy batched jobs or self-hosted runners |
  | **Nix (`nix-installer-action` `v23`) + external binary cache (S3/Cachix/Attic)** | Minimal per job (fetches only exact closure for that job's checks) | Derivation-level content-addressed; external store avoids 10 GB GHA cap | Medium (~15–30s Nix install + NAR fetch/unpack) | Very high (same flake/derivation locally and in CI) | Heterogeneous matrices (MSRV, nightly, Miri, Kani, cross-QEMU) with per-check caching |
  | **Nix + GHA-backed cache (Magic Nix Cache)** | Minimal per job | Derivation-level, but shares 10 GB GHA repo cap (LRU thrash risk) | Medium (~15–30s + ~125 MB/s GHA cache bandwidth) | Very high | Medium repos whose total active Nix closure fits comfortably under 10 GB |
  | **`actions/cache` / `Swatinem/rust-cache` (`v2.9.3`) + `rustup`** | Medium–High (`target/` tarballs multiply per target, feature set, toolchain, coverage flag) | Coarse (`target/` dir per key); easily thrashes 10 GB GHA cap and 7-day TTL | Low (~10–25s) when warm; high on cache miss | Low–Medium (runner OS and `rustup` drift) | Simple Rust repos with narrow matrix |
  | **Packing: 1 check per job** | $N \times$ closure download | Per-job | $N \times T_{\text{fixed}}$; queues at 20 concurrent jobs (public Free) | Same as underlying strategy | Long-running checks ($T_{\text{check}} \gg 2\text{ min}$, e.g., Kani, Miri) |
  | **Packing: Batched by toolchain/closure** | $1 \times$ closure download per group | Retain per-check derivation/cache keys inside each batched runner | $1 \times T_{\text{fixed}}$ per group; avoids concurrency queueing | Same as underlying strategy | Fast/medium checks sharing a toolchain (clippy, fmt, doc, feature powersets, trybuild) |

- **Job packing rationale (derived):** Each GitHub Actions job incurs a fixed startup cost $T_{\text{fixed}} \approx 30\text{–}90\text{s}$ (VM provisioning, `actions/checkout`, Nix/Docker setup). One-check-per-job minimizes critical-path wall-clock latency only when $T_{\text{check}} \gg T_{\text{fixed}}$ and concurrency quota is not saturated. For 40+ short checks ($T_{\text{check}} \approx 5\text{–}20\text{s}$), 1-check-per-job multiplies fixed overhead and closure transfer by $N$ and hits the 20-job concurrency cap (increasing wall-clock latency). Grouping checks that share the same toolchain closure onto one runner pays $1\times T_{\text{fixed}}$ and $1\times$ closure transfer per group while preserving independent per-check cache keys.

## Boundaries

- **Kani `kani-0.68.0` prebuilt tarball ELF ABI on NixOS (`not examined`):** The exact ELF `NEEDED` dynamic-library set (`glibc`/`libstdc++`) of `kani-0.68.0`'s prebuilt release binaries, and whether `autoPatchelfHook` alone suffices vs. `buildFHSEnv` or source builds in Nix, was not empirically measured.
- **Miri offline sysroot build for `no_std` / cross targets (`not examined`):** The `bwrap --unshare-net` probe verified offline `cargo miri setup` for host `x86_64-unknown-linux-gnu` (`std` + 27 `.rlib`s). Whether additional crates or target-specific configuration are required for `no_std` or cross-architecture Miri sysroot targets was not empirically executed.
- **Exact disk footprint of combined multi-toolchain Nix closures on `ubuntu-24.04` (`unknown`):** Standard `ubuntu-24.04` runners expose ~14 GB free on `/` (with additional space reclaimable by removing preinstalled SDKs). The exact unpacked Nix store size of a combined stable + nightly + Miri + Kani + cross-sysroots closure was not measured on a live GitHub Actions runner; disk-pressure thresholds for batched jobs remain empirically unmeasured.
- **`CARGO_SOURCE_*` environment variables (`unsupported`):** Cargo explicitly does not support `source.<name>.replace-with` or `source.<name>.directory` via environment variables (`rust-lang/cargo` `doc/book/src/reference/config.md`) and silently ignores them.
- **Cross-version rustdoc JSON comparison in `cargo-semver-checks@v0.51.0` (`unsupported`):** `trustfall-rustdoc@v0.41.0` explicitly rejects comparing a baseline and current rustdoc JSON with different `format_version`s even when both versions are in `{57, 60, 61}`.
- **`cargo llvm-cov --remap-path-prefix` with doctests (`known not to apply` / `unsupported`):** Per `taiki-e/cargo-llvm-cov@v0.9.2` (`src/cli.rs:75`), relative path remapping via `--remap-path-prefix` is not fully compatible with doctest coverage.
- **Non-Linux hosts (macOS, Windows) (`not examined`):** Execution probes and `qemu-user`/`binfmt_misc` analysis apply to Linux (`x86_64-unknown-linux-gnu`); Windows and macOS runner limits, path-remapping edge cases, and container/Nix behavior were not examined.
- **Non-Nix build-cache systems such as `sccache` (`not examined` empirically):** Limitations of `sccache` on the GHA cache backend (per-object HTTP round-trip latency; non-caching of proc-macros, `build.rs`, and link steps) are noted from upstream documentation rather than benchmarked directly.

## Evidence

All execution probes and source inspections were acquired on `2026-11-21` on `x86_64-unknown-linux-gnu`.

### Source Inspections

- `rust-lang/rust` (`compiler/rustc_span/src/lib.rs:243-258`): `RemapPathScopeComponents::OBJECT = MACRO | DOCUMENTATION | DEBUGINFO | COVERAGE`.
- `rust-lang/rust` (`compiler/rustc_session/src/options.rs:2718, 2910`): `-Z randomize-layout` and `-Z layout-seed` (`Option<u64>` defaulting to `None`).
- `rust-lang/cargo` (`src/compiler/trim_paths.rs:65-81`): Profile `trim-paths` forwarding directly to `--remap-path-scope={trim_paths}`.
- `rust-lang/cargo` (`doc/book/src/reference/config.md:231-233, 1390-1400`): `source.<name>.replace-with` and `source.<name>.directory` documented as `Environment: not supported`.
- `dtolnay/trybuild` (`1.0.125`): `src/normalize.rs` (25 normalization passes, `Context` fields, historical-variation matching) and `src/env.rs` (`TRYBUILD` parsing for `"wip"` vs. `"overwrite"`).
- `obi1kenobi/cargo-semver-checks` (`v0.51.0`): `Cargo.toml:21` (`trustfall_rustdoc = "0.41.0"` with `features = ["v57", "v60", "v61", "rayon", "rustc-hash"]`) and `src/main.rs:456-510, 641-660` (`--baseline-version`, `--baseline-rustdoc`, `--baseline-root`, `--baseline-rev`).
- `obi1kenobi/trustfall-rustdoc` (`v0.41.0`): `src/versioned.rs:139-206, 225-234` (`VersionedRustdocAdapter::new` exact-match dispatch and `bail!` on format-version mismatch).
- `taiki-e/cargo-llvm-cov` (`v0.9.2`): `src/context.rs:130-185, 202` (`llvm-tools-preview`, `LLVM_COV`, `LLVM_PROFDATA`, `LLVM_COV_FLAGS`), `src/main.rs:157-290`, `src/cargo.rs:89-90` (`llvm-cov-target`), `src/report.rs:942-979` (`^{workspace_root}` ignore regex), `src/cli.rs:75` (`--remap-path-prefix` doctest caveat).
- `pacak/cargo-show-asm` (`5c0b140c004b`): `src/opts.rs:210-217` (`--native` -> `-C target-cpu=native`).
- `rust-lang/miri` (`7e679961edcf`): `cargo-miri/src/setup.rs:28-172` (`MIRI_SYSROOT` skip-setup fast path, `MIRI_LIB_SRC` detection).
- `RalfJung/rustc-build-sysroot` (`6534cd367f8d`): `src/lib.rs:350-371, 451-510` (`SysrootBuilder::build_from_source` temporary workspace creation in `/tmp/rustc-build-sysroot-*`, inherited `CARGO_HOME`, omission of `library/.cargo/config.toml`).
- `model-checking/kani` (`kani-0.68.0`): `src/setup.rs:22-244` (`--use-local-bundle`, `--use-local-toolchain`, `KANI_HOME`), `kani-dependencies` (CBMC `6.11.0`, Kissat `4.0.1`), `kani-driver/src/call_cbmc.rs:153-155, 437-463` (`DEFAULT_SOLVER = CbmcSolver::Cadical`), `kani-driver/src/session.rs:43, 72, 423-473`.

### Execution Probes

1. **Path leakage and `trim-paths` (`rustc 1.100.0` / `cargo 1.100.0` vs. `cargo 1.102.0-nightly`):**
   - Built an identical single-binary crate invoking `file!()` in two sibling directories (`/tmp/.../dir_alpha_unique_path` and `/tmp/.../dir_beta_unique_path`):
     - `cargo +stable build --release --offline`: identical SHA-256 `6855691def421cb901e0e2a2921426f68faada469a6e047262ca3f2521505d23`, `dir_alpha` absent.
     - `cargo +stable build --offline` (`dev`): distinct SHA-256 (`e034afc1f93138793dc76dc69790aa978f57c34e5bd19f3f2e4e18aaee7b2072` vs. `108ae74850d757ea64d8c6847e405ff8748bfb52e0bbbb965822e8747a3af037`), `dir_alpha` present in DWARF debuginfo.
     - `RUSTFLAGS="--remap-path-prefix=<dir>=/src" cargo +stable build --offline`: identical SHA-256 `c4a6a702bd9128096605a4e657667e1a6f185d1d97f08b868a60735174564eb9`, `dir_alpha` absent.
     - `cargo +stable build --offline --config profile.dev.trim-paths="object"`: exit `101` (`feature 'trim-paths' is required`).
     - `cargo +nightly build --offline -Z trim-paths --config profile.dev.trim-paths="object"`: exit `0`, warns `flag '-Z trim-paths' has been stabilized in the 1.101 release`, identical SHA-256 (`2e220f49...`) across directories, zero leaked path bytes.
2. **`--offline` vs. `--frozen` (`cargo 1.100.0`):**
   - Crate with no `Cargo.lock`: `cargo +stable check --offline` exited `0` and created `Cargo.lock`; `cargo +stable check --frozen` exited `101` (`cannot create the lock file ... because --frozen was passed to prevent this`).
3. **`-Z randomize-layout` (`rustc 1.102.0-nightly (3ef0c22cd)`):**
   - Printed `std::mem::offset_of!` for an 8-field struct across 5 unseeded `-Z randomize-layout` builds (`12,24,4,32,2,0,8,16` in 5/5 runs, 1 unique binary hash), matching `-Z randomize-layout -Z layout-seed=0` (`12,24,4,32,2,0,8,16`). Default layout: `28,24,16,0,29,26,20,8`; `seed=1`: `18,32,0,8,19,16,36,24`; `seed=42`: `0,8,28,32,24,2,4,16`.
4. **Offline Miri sysroot (`rustc 1.102.0-nightly (3ef0c22cd)`, `miri 0.1.0 (3ef0c22cdb)`):**
   - Executed `cargo miri setup` inside `bwrap --ro-bind / / --tmpfs /tmp --bind <tmp> <tmp> --dev /dev --proc /proc --unshare-net` with fresh empty `CARGO_HOME` and fresh `MIRI_SYSROOT`: failed (`exit 1`) with no config, failed (`exit 1`) with `CARGO_SOURCE_*` env vars, succeeded (`exit 0`, `24.51s`, 27 `.rlib`s) with `$CARGO_HOME/config.toml` pointing `[source.vendored-sources].directory` to `<sysroot>/lib/rustlib/src/rust/library/vendor`.
5. **Rustdoc JSON `format_version` spot-check:**
   - `RUSTC_BOOTSTRAP=1 rustdoc +<tc> -Z unstable-options --output-format=json` emitted `format_version=57` on `1.93.1`, `1.94.0`, `1.96.0` and `format_version=61` on `1.99.1`, `1.100.0`, `1.102.0-nightly (2026-11-11)`.
6. **`llvm-cov` + `--remap-path-scope` (`rustc 1.100.0` + `llvm-profdata` + `llvm-cov`):**
   - Compiled an instrumented library with `-C instrument-coverage` under each scope combination in `/tmp/.../lib.rs`, ran the test binary to generate `.profraw`, merged via `llvm-profdata`, and ran `llvm-cov export --format=lcov`, `llvm-cov report`, and `llvm-cov show` (results recorded in Section 1.5).

### Documentation

- GitHub Docs (*About GitHub-hosted runners*, *Caching dependencies to speed up workflows*, retrieved `2026-11-21`).
- Cargo Reference (Source Replacement, Build Scripts, Target Configuration).
- `DeterminateSystems/nix-installer-action` (`v23`), `Swatinem/rust-cache` (`v2.9.3`), Linux Kernel `binfmt_misc`, and QEMU User Mode Emulation documentation.

## Revalidation

Each major finding can be revalidated with a targeted, low-cost check:

1. **Path remapping & `trim-paths`:** Build a minimal crate in two temp dirs with `--config profile.dev.trim-paths="object"` on the target Cargo version and compare `sha256sum` of the output binaries.
2. **`llvm-cov` + `trim-paths` / `--remap-path-scope=object`:** Check `RemapPathScopeComponents::OBJECT` in `rust-lang/rust` (`compiler/rustc_span/src/lib.rs`) or run `rustc -C instrument-coverage --remap-path-prefix=$PWD=/src --remap-path-scope=object` followed by `llvm-cov show` to verify whether `object` still includes `COVERAGE`.
3. **Offline Miri sysroot:** Check `SysrootBuilder::build_from_source` in `RalfJung/rustc-build-sysroot` (`src/lib.rs`) for whether `.cargo/config.toml` is copied into the temp workspace, or run `bwrap --unshare-net` with `cargo miri setup` and an empty `CARGO_HOME` vs. `$CARGO_HOME/config.toml`.
4. **`cargo-semver-checks` rustdoc JSON compatibility:** Check `trustfall_rustdoc` features in `cargo-semver-checks/Cargo.toml` and `VersionedRustdocAdapter::new` in `trustfall-rustdoc/src/versioned.rs`, and compare `format_version` emitted by `RUSTC_BOOTSTRAP=1 rustdoc -Z unstable-options --output-format=json` across the baseline and current toolchains.
5. **Kani offline bundle:** Inspect `kani-dependencies` and `src/setup.rs` (`--use-local-bundle`, `--use-local-toolchain`) in the target `model-checking/kani` release tag.
6. **GitHub Actions runner & cache limits:** Re-read GitHub's *About GitHub-hosted runners* and *Caching dependencies* docs before making disk-budget or cache-architecture decisions.
