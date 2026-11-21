# CI Enforced Source-Closure Check Skipping: Nix and Architectural Alternatives

## Summary

Sound CI check skipping requires two coupled properties: (1) computing each check's cache key over only its declared input subset, and (2) enforcing at execution time that any read outside that declared subset fails rather than silently succeeding and producing stale cache hits.

- **Nix (`lib.fileset.toSource` + `--lazy-trees` + binary-cache probing):** Scoping each check's `src` with `nixpkgs.lib.fileset.toSource` keeps unaffected checks' `drvPath` and `outPath` bit-for-bit identical across unrelated edits while kernel-enforcing the input closure on Linux. With `--lazy-trees`, flake evaluation avoids copying untouched large repository files into `/nix/store`. For standard input-addressed derivations, CI planners (`nix eval --json` or `nix-eval-jobs`) can probe remote binary caches via `<32-char-hash>.narinfo` or `nix path-info --store` without realizing derivations, subject to three sharp CLI/protocol edges: `builtins.toFile` rejects derivation string context without `builtins.unsafeDiscardStringContext`; Nix `toJSON` coerces any attribute set containing a key literally named `outPath` to a bare string; and `nix path-info --store <url> --json <outPath>` exits `0` on a cache miss (emitting `{"<outPath>": null}`). Floating content-addressed derivations (`__contentAddressed = true`) emit a 52-character placeholder `outPath` before realization and cannot be probed via `.narinfo` (they require `.doi` realization lookup).
- **Rust packaging in Nix (`crane` `v0.24.0`, `fenix`, `rust-overlay`):** `crane`'s `buildDepsOnly` + `mkDummySrc` decouples third-party crate compilation (`cargoArtifacts`) from workspace `.rs` and `build.rs` edits by laundering `Cargo.toml` manifests through `cargoTomlConservative` and generating synthetic `.rs` stubs. However, shared workspace `cargoArtifacts` still invalidates on any byte edit to `Cargo.lock` or `.cargo/config(.toml)`, any edit to retained `Cargo.toml` fields in any workspace member (`[dependencies]`, `[dev-dependencies]`, `[build-dependencies]`, `[features]`, `[profile]`, `[workspace.*]`, etc.), or adding/removing `src/lib.rs`, `src/main.rs`, or `src/bin/*`.
- **Nix cross-OS sandbox parity (`NixOS/nix` `2.36.0`):** Enforced confinement is not uniform across OSes. Linux defaults to `sandbox = true` (full namespaces + seccomp). macOS defaults to `sandbox = false` (only `sandbox-minimal.sb`); enabling `true`/`relaxed` uses Apple's private `sandbox_init_with_parameters()` Seatbelt API with no mount/PID/network namespaces, no path remapping, a ~10k–12k store-path profile ceiling, and host metadata/IPC exposure. Native Windows is officially unsupported and `WindowsDerivationBuilderImpl` provides zero sandboxing (inheriting host `PATH`), so enforced confinement on Windows requires WSL2 or a Linux VM.
- **Architectural alternatives:** Bazel (`rules_rust`) and Buck2 (`reindeer`) add per-crate `.rmeta` early cutoff but impose dual build-graph maintenance and friction with `trybuild`, Miri, Kani, and `no_std`/proc-macro splits. Lightweight Linux mount-namespace sandboxes (`bubblewrap` / BuildKit + OCI + signed CAS) enforce repo-file closures while running native `cargo`, but suffer coarse OCI-image invalidation and require custom signing, ACLs, and DAG caching. Non-sandboxed affected-selection (`git diff` + `cargo metadata`, or manual-glob task hashers) is unsound for Rust (`build.rs`, `include_bytes!`/`include_str!`, proc-macro side-channel reads, runtime fixtures, workspace feature unification), whereas compilation caches (`sccache`, `Swatinem/rust-cache`, `cargo-hakari`, `cargo-nextest` archives) remain essential on dirty core-file misses where whole-check skipping saves 0%.

## Applicability

This report characterizes and compares four architectural families for Rust CI check skipping and caching across the 15 durable subjects in `REPORT.json`:

1. **Nix evaluation, caching, sandboxing, and Rust packaging:**
   - `NixOS/nix` (`2.36.0`, commit `3705f35ddcdca8d777c1d75b939eb6a3a4ac9ebb`): inspected via C++ and Seatbelt source for binary-cache layout (`BinaryCacheStore`), `.doi` realizations, and Linux/macOS/Windows derivation builders.
   - `DeterminateSystems/nix-src` (`v3.24.3`, commit `a21b800b3c1640f2350cc311fee1a2f64576e33a`) and local Determinate Nix `3.17.0` (upstream Nix `2.33.3`): inspected via documentation and executed locally on `x86_64-linux` (`support/probe1_nix_source_filtering.sh`, `support/probe2_nix_lazy_trees_and_cache.sh`).
   - `nix-community/nix-eval-jobs` (`v2.35.4`, commit `9f1553afabd95f9f59951f5c946e86005af7196a`): inspected via source (`src/cache-status-resolver.cc`) and documentation; not executed locally.
   - `ipetkov/crane` (`v0.24.0`, commit `95e62def851e9d650f0eab63cb4f59a3306e20bd`): inspected via Nix source (`lib/mkDummySrc.nix`, `lib/findCargoFiles.nix`, `lib/cleanCargoToml.nix`, `lib/filters/cargoTomlConservative.nix`, `lib/buildDepsOnly.nix`, `lib/cleanCargoSource.nix`).
   - `nix-community/fenix` (commit `ea745d6a7730c73bb5e0c028818240234e7bda05`) and `oxalica/rust-overlay` (commit `a5c999945da3991d7aa3cc2a6075cfd22bd387e9`): inspected via upstream documentation.
2. **Per-crate build-system action caches:** `bazelbuild/rules_rust` (`0.75.0`, commit `5d99ff2e58d1a0c9387fc4945029df11144bc8a3`) and `facebookincubator/reindeer` (commit `5981c7a3faacee2efc15584a94c0caa851c6517b`), inspected via upstream documentation.
3. **Lightweight OS/container confinement:** `containers/bubblewrap` (`v0.12.0`, executed locally on `x86_64-linux` in `support/probe3_bwrap_closure.sh`) and `moby/buildkit` (`v0.35.1`, architectural comparison). Both are identified by upstream repository and release tag without pinned commit SHAs.
4. **Cargo-native compilation caches, feature unification, and test archive splitting:** `mozilla/sccache` (`v0.19.0`, commit `1616af1ba4881ad17d1619884042febaa5189055`), `Swatinem/rust-cache` (`v2.9.3`, commit `eedcf2fb1c22f010a0eb66b92f378c110977f266`), `guppy-rs/guppy` (`cargo-hakari`, commit `0cbe52c4cbf4ac55bc2fa9ba7f8f5d14288fe478`), and `nextest-rs/nextest` (`cargo-nextest-0.9.152`, commit `bb7472661992548512163aa563bee0948db47a4f`), inspected via upstream documentation and source.

Behavioral findings observed by execution apply directly to `x86_64-linux` with Determinate Nix `3.17.0` / Nix `2.33.3` and `bubblewrap 0.12.0`. Source-level findings on `NixOS/nix` `2.36.0` (`3705f35ddcdca8d777c1d75b939eb6a3a4ac9ebb`) apply to that exact revision; because Determinate Nix `3.17.0` is based on Nix `2.33.3`, minor CLI flag or default differences between `2.33.3` and `2.36.0` (notably `--lazy-trees` default behavior) are noted explicitly in **Findings**.

## Findings

### 1. Nix Per-Check Source Closures, Lazy Trees, and Cache Probing

#### 1.1 Scoped Source Closures (`lib.fileset.toSource` vs. `self`)

Basis: execution

Scoping a check derivation's `src` via `nixpkgs.lib.fileset.toSource { root = ./.; fileset = ...; }` computes a content-addressed store path containing only the selected file subset. Because the Linux Nix build sandbox bind-mounts only declared `/nix/store` inputs, any check that reads an undeclared repository file fails at build time rather than producing a stale cache hit. Conversely, passing `self` or unfiltered `./.` as `src` invalidates every check derivation on any tracked file change.

In `support/probe1_nix_source_filtering.sh` (Determinate Nix `3.17.0` / Nix `2.33.3`, recorded in `support/probe1_output.txt`), three check derivations (`check-core-fileset` scoped to `./crates/core`, `check-leaf-fileset` scoped to `./crates/core` + `./crates/leaf`, and `check-naive-self` scoped to `self`) behaved as follows across sequential edits:

| Repository Edit | `check-core-fileset` (`drvPath` / `outPath`) | `check-leaf-fileset` (`drvPath` / `outPath`) | `check-naive-self` (`drvPath` / `outPath`) |
| :--- | :--- | :--- | :--- |
| Edit `README.md` (unrelated) | Unchanged / Unchanged | Unchanged / Unchanged | Changed / Changed |
| Edit `crates/leaf/src/lib.rs` | Unchanged / Unchanged | Changed / Changed | Changed / Changed |
| Edit `crates/core/src/lib.rs` | Changed / Changed | Changed / Changed | Changed / Changed |

#### 1.2 Lazy Trees (`--lazy-trees` vs. `--no-lazy-trees`) and `libgit2` `reftable` Compatibility

Basis: execution + documentation

Without lazy trees, flake evaluation eagerly copies the entire Git working tree into `/nix/store/<hash>-source` before evaluating `flake.nix`, penalizing large repositories on every CI planning step even when `lib.fileset.toSource` selects a tiny subtree. With **lazy trees** (enabled by default in Determinate Nix `3.17.0` / `v3.24.3` and integrated in `NixOS/nix` `2.36.0`), flake inputs are backed by a virtual filesystem layer so only files demanded during evaluation or derivation instantiation are hashed and copied into `/nix/store`. (By contrast, Lix has declined to adopt the upstream/Determinate lazy-trees implementation due to complexity and non-determinism concerns, relying instead on opt-out mechanisms such as `copySourceTreeToStore = false` in `flake-compat`.)

In `support/probe2_nix_lazy_trees_and_cache.sh` Part A (`support/probe2_output.txt`), evaluating `.#checks.x86_64-linux.core.drvPath` (scoped to `./crates/core/hello.txt` in a repo containing a 2 MiB `unrelated-large.bin`):

- `--lazy-trees` produced `/nix/store/x72phvg87ykhd89j9api2a1ap99r853p-probe2-core.drv` and copied **zero** copies of `unrelated-large.bin` into `/nix/store` (`Found in /nix/store after --lazy-trees: NONE`).
- `--no-lazy-trees` produced the exact same `drvPath`, but eagerly copied the entire Git tree including `unrelated-large.bin` into `/nix/store/7z8zwi5sghy9rcbhrymcbf1dczisgwf2-source/unrelated-large.bin`.

**`reftable` incompatibility:** On hosts where `git init` defaults to Git's `reftable` ref storage (`extensions.refstorage`), Determinate Nix `3.17.0` / Nix `2.33.3`'s `libgit2` flake fetcher aborts with `error: opening Git repository "...": unsupported extension name extensions.refstorage`. Initializing repositories with `git init --ref-format=files` avoids this failure.

#### 1.3 Pre-Build CI Planning and CLI Serialization Contracts

Basis: source + documentation + execution

CI planners extract `{ drvPath, outPath }` check graphs without realizing checks via:

1. `nix eval --json` over a flake attribute set (single-process), or
2. `nix-community/nix-eval-jobs` (`v2.35.4`), which evaluates attribute sets across parallel worker processes with bounded RSS (`--workers`, `--max-memory-size`), streams NDJSON (`attr`, `drvPath`, `inputDrvs`, `outputs`, `system`, `stats`), and supports `--check-cache-status` via an async `CacheStatusResolver` (`src/cache-status-resolver.cc`) that queries local and configured substituter stores and emits `"cacheStatus"` (`cached`, `local`, `notBuilt`).

Two serialization traps affect Nix-based CI planners (`support/probe1_nix_source_filtering.sh`, steps 1a–1c):

- **String context in `builtins.toFile`:** Reading `d.drvPath` or `d.outPath` yields a string carrying Nix string context. Although `nix eval --json` strips context at the CLI boundary without realizing `d`, any in-Nix serialization via `builtins.toFile "plan.json" (builtins.toJSON ...)` fails (`error: files created by builtins.toFile may not reference derivations, but plan.json references =...drv`) unless `builtins.unsafeDiscardStringContext` is applied. Embedding raw `d.outPath` in a planner derivation without discarding context would force the planner derivation to depend on and realize every check.
- **`outPath` key coercion in `builtins.toJSON`:** Nix's JSON serializer treats any attribute set containing a key literally named `outPath` as a derivation-like object and coerces the entire attribute set to that single string. Structured planner schemas must use distinct field names (such as `drv_path` and `out_path`).

#### 1.4 Remote Binary-Cache Probing (`.narinfo`, `nix path-info --store`, and `ca-derivations`)

Basis: source + execution

For standard **input-addressed** derivations, `outPath` (`/nix/store/<32-char-nixbase32-hash>-<name>`) is fully determined at evaluation time. `BinaryCacheStore` (`NixOS/nix` `src/libstore/binary-cache-store.cc` L128, L347–348) indexes each store path at `<hashPart>.narinfo` (`std::string(storePath.hashPart()) + ".narinfo"`). Because `BinaryCacheStore` maintains the **closure invariant** — uploading a path's `.narinfo` only after uploading its NAR and all referenced `.narinfo` files — a single `HEAD`/`GET <32-char-hash>.narinfo` or `nix path-info --store <url> --json <outPath>` tests cache presence without downloading or realizing the closure.

In `support/probe2_nix_lazy_trees_and_cache.sh` Part B (`support/probe2_output.txt`), after realizing and copying only `core` to a `file://` binary cache:

- The cache contained `h0f60ka9axqjz52ymp0vkiag7w0yq8vm.narinfo` with `StorePath`, `URL`, `Compression`, `FileHash`, `FileSize`, `NarHash`, `NarSize`, `References`, and `Deriver`.
- **Exit-0 cache-miss contract:** Running `nix path-info --store file://.../cache --json <unbuilt-other-outPath>` exited **`0`** (not non-zero) while printing `don't know how to build these paths:` to stderr and emitting `{"/nix/store/kv7gdwh8wyzxq00j5pkal41ybk9d1m2i-probe2-other":null}` to stdout, without realizing `other` locally (`NOT_IN_LOCAL_STORE`). CI scripts must parse the JSON value for `null` rather than checking the exit code.

**Floating `ca-derivations` caveat:** For floating content-addressed derivations (`__contentAddressed = true`), the final `outPath` depends on the build output's NAR hash and is unknown before realization. In `support/probe2_nix_lazy_trees_and_cache.sh` Part C, `caCore.outPath` evaluated to a 52-character downstream placeholder (`/1q37br5pbz5sa9wy23mb8g7wwv84ajv1qriqwwj3zkhqwc4kim7i`) rather than a `/nix/store/<32-char>-<name>` path. Pre-build `<hash>.narinfo` probing is therefore impossible; remote lookup must query `realisations/<drv-modulo-hash>/<outputName>.doi` (`BinaryCacheStore::queryRealisationUncached`, `src/libstore/binary-cache-store.cc` L646–649).

### 2. Rust Packaging and Multi-Toolchain Matrices in Nix

#### 2.1 `crane` `mkDummySrc` Laundering and `buildDepsOnly` Invalidation Rules

Basis: source + documentation

`ipetkov/crane` (`v0.24.0`, commit `95e62def851e9d650f0eab63cb4f59a3306e20bd`) splits Rust builds into two tiers (`lib/buildDepsOnly.nix`, `lib/cleanCargoSource.nix`):

1. `craneLib.buildDepsOnly` runs `mkDummySrc` to replace workspace `.rs` files with minimal stubs, compiles third-party crates (including dev-dependencies by default via `doCheck = true` and `cargoTestExtraArgs = "--no-run"`), and outputs a cached `target/` artifact derivation (`cargoArtifacts`).
2. Downstream check derivations (`buildPackage`, `cargoClippy`, `cargoNextest`, `cargoDoc`, etc.) accept `inherit cargoArtifacts;` alongside a filtered `src` (`cleanCargoSource` or `lib.fileset.toSource`).

Inspection of `lib/mkDummySrc.nix` (L99–154, L200–336, L369–376), `lib/findCargoFiles.nix` (L18–53), `lib/cleanCargoToml.nix` (L9–35), `lib/default.nix` (L112–116), `lib/filters/cargoTomlConservative.nix` (L21–112), and `lib/buildDepsOnly.nix` (L37–90) establishes the exact inputs copied into `dummySrc`:

1. **Verbatim files (two-pass `lib.cleanSourceWith`):** Root `Cargo.lock` (or an explicit `cargoLock` argument) and every `.cargo/config.toml` and `.cargo/config` anywhere under `src`.
2. **Eval-time laundered `Cargo.toml` files:** Every `Cargo.toml` under `src` is parsed via `builtins.fromTOML`, filtered by `cleanCargoToml` (defaulting to `filters.cargoTomlConservative`), stripped of string context via `builtins.unsafeDiscardStringContext`, and rewritten with `writeTOML`. For package manifests (`cleanedCargoToml ? package`), `package.build` is overwritten to a store-path `dummyBuild.rs` so Cargo caches `build-dependencies` without timestamp-collision issues against the real `build.rs`.
3. **Synthetic `.rs` stubs:** Generated for `src/lib.rs`, `src/main.rs`, auto-discovered `src/bin/*`, and manifest-declared `[[bin]]`, `[[bench]]`, `[[example]]`, and `[[test]]` targets. Real `.rs` and `build.rs` files are not copied unless injected via `extraDummyScript` or `dummyBuildrs`.

Consequently, a shared workspace `cargoArtifacts` (`buildDepsOnly`) derivation has the following exact invalidation boundary:

- **Always invalidates `dummySrc` / `cargoArtifacts`:**
  - Any byte change to `Cargo.lock`, `.cargo/config.toml`, or `.cargo/config`.
  - Any change to retained `Cargo.toml` fields in **any** workspace member under `cargoTomlConservative`: `[dependencies]`, `[dev-dependencies]`, `[build-dependencies]`, `[target.*]`, `[features]`, `[patch]`, `[profile]`, `[workspace.{members, default-members, exclude, dependencies, package, resolver}]`, `package.{name, version, edition, resolver, workspace}` (note that `buildDepsOnly.nix` L61–62 also derives `pname`/`version` from root `Cargo.toml` unless overridden), and target structural fields (`name`, `path`, `crate-type`, `edition`, `harness`, `proc-macro`).
  - Adding, removing, or renaming `src/lib.rs`, `src/main.rs`, or entries under `src/bin/` in any crate (`mkDummySrc.nix` L231–265 calls `builtins.readDir` on `src/` and `src/bin/` at eval time).
  - Adding or removing any `Cargo.toml` or `.cargo/config(.toml)` anywhere in the workspace tree.
- **Does NOT invalidate `dummySrc` / `cargoArtifacts`:**
  - Editing contents of existing `.rs` source files or existing `build.rs` files.
  - Comments or formatting changes in `Cargo.toml`, or edits to fields stripped by `cargoTomlConservative`: `[badges]`, `[lints]`, `[workspace.lints]`, `[workspace.metadata]`, `package.{authors, description, documentation, homepage, repository, readme, license, license-file, keywords, categories, publish, exclude, include, metadata, build, links, rust-version, default-run, auto*}`, and per-target `{test, doctest, bench, doc, plugin, required-features}`.

#### 2.2 Multi-Toolchain Matrices (`fenix` and `oxalica/rust-overlay`)

Basis: documentation

Both `nix-community/fenix` (`ea745d6a7730c73bb5e0c028818240234e7bda05`) and `oxalica/rust-overlay` (`a5c999945da3991d7aa3cc2a6075cfd22bd387e9`) supply pure, hash-pinned Rust toolchains (stable, MSRV, beta, nightly, cross targets, and components such as `miri`, `clippy`, and `rust-src`) that compose with `(crane.mkLib pkgs).overrideToolchain`.

- `oxalica/rust-overlay` pre-fetches component hashes in-tree for pure evaluation without network access, retains all stable releases back to `1.29.0`, retains nightly/beta manifests only back to `{current_year - 1}-01-01` (older nightlies require pinning historical snapshot tags), and supports reading `rust-toolchain.toml` via `fromRustupToolchainFile`.
- `nix-community/fenix` provides Cachix-backed `minimal`/`default`/`complete`/nightly toolchains and `combine` for assembling multi-target cross-compilation toolchains.

### 3. Nix Cross-OS Sandbox Parity (Linux, macOS, Windows)

Basis: source + documentation

Enforced source-closure confinement in `NixOS/nix` (`2.36.0`, commit `3705f35ddcdca8d777c1d75b939eb6a3a4ac9ebb`) differs materially across operating systems:

| Platform | Official Support | Compiled-In `sandbox` Default | Isolation Mechanism and Parity Gaps |
| :--- | :--- | :--- | :--- |
| **Linux** (`i686`, `x86_64`, `aarch64`) | Supported (`supported-platforms.md:5`) | `smEnabled` (`true`) (`local-settings.hh:356-360`) | Full kernel isolation: `CLONE_NEWPID \| CLONE_NEWNS \| CLONE_NEWIPC \| CLONE_NEWUTS` (plus `CLONE_NEWNET` for non-FODs, `CLONE_NEWUSER`, optional `CLONE_NEWCGROUP`), private `/proc`, `/dev`, `/dev/shm`, `/dev/pts`, chroot/mount remapping, seccomp `filter-syscalls = true`, and `allow-new-privileges = false` (`linux-derivation-builder.cc:596-600, 913-919`; `local-settings.hh:364-376, 571-598`). |
| **macOS / Darwin** (`x86_64`, `aarch64`) | Supported (`supported-platforms.md:7`) | `smDisabled` (`false`) (`local-settings.hh:358-360, 386`) — **not** `relaxed` by default in upstream Nix | When disabled (`false`), applies only `sandbox-minimal.sb` (`(allow default)` + `(deny file-write-setugid)`). When explicitly set to `true` or `relaxed`, invokes Apple's private/undocumented `sandbox_init_with_parameters()` (`<sandbox.h>`, `darwin-derivation-builder.cc:15-16, 230-235`; not the `sandbox-exec` CLI) with an SBPL `(version 1)` `(deny default)` profile (`sandbox-defaults.sb` + allowlisted store paths). **Gaps vs. Linux:** no mount, PID, IPC, UTS, or network namespaces; no path remapping (`target=source` and diverted stores throw, `darwin-derivation-builder.cc:133-137`, `unix-derivation-builder.cc:1088-1093`); ~10k–12k store-path Seatbelt profile ceiling despite 32-bucket prefixing (`darwin-derivation-builder.cc:122-156`); `sandbox-defaults.sb` exposes host `/System/Library/CoreServices/SystemVersion*.plist`, `/usr/share/{zoneinfo,locale}`, `/private/var/select/sh`, `sysctl-read`, SysV/POSIX IPC, and `opendirectoryd`; `additionalSandboxProfile` requires `sandbox = relaxed` (which also exempts `__noChroot = true` and FODs, `unix-derivation-builder.cc:1071-1083`). |
| **Windows** | Unsupported natively (`supported-platforms.md:1-7` lists only Linux and macOS; practical use requires WSL2) | `smDisabled` (`false`) (`local-settings.hh:358-360`) | Experimental `WindowsDerivationBuilderImpl` (`windows-derivation-builder.cc:71-85, 210-216, 309-320`) has **zero sandboxing**: no filesystem, chroot, or network isolation; no build user (runs as caller); no builtin builders; no recursive Nix; no CA or fixed-output derivations (input-addressed only); inherits host `SystemRoot`, `SystemDrive`, `windir`, `COMSPEC`, `PATHEXT`, and `PATH` (commented in source as *"Impure: a derivation sees whatever else is on the builder's `PATH`"*). |

### 4. Non-Nix Architectural Alternatives

#### 4.1 Bazel (`rules_rust`) and Buck2 (`reindeer`)

Basis: documentation + derived

Both Bazel (`bazelbuild/rules_rust` `0.75.0`) and Buck2 (`facebookincubator/reindeer`) enforce hermetic per-action sandboxes and content-addressed remote action caches (REAPI v2) with **early cutoff**: if a crate's `.rmeta` interface output is unchanged after a private implementation edit, downstream dependents skip recompilation and test re-execution.

For Rust libraries that remain published via Cargo/crates.io, four recurring friction points offset those gains:

1. **Dual build-graph maintenance:** Teams must keep `Cargo.toml`/`Cargo.lock` alongside generated `BUILD.bazel` (`crate_universe`) or `BUCK` (`reindeer`) graphs. `reindeer` flattens Cargo's dynamic resolution into static Buck targets, generally requires vendored/pinned crate sources, and needs manual "fixup" overlays for non-standard `build.rs` or `-sys` crates.
2. **Proc-macro and `no_std`/`std` splits:** Proc-macros run on the host (`exec` configuration) while target libraries may be `no_std` or cross-compiled; host/target feature unification in `crate_universe`/`rules_rust` has recurring edge cases, and `rust-analyzer` (`gen_rust_project`) needs extra wiring to locate Bazel-built proc-macro `.so`/`.dylib` artifacts.
3. **`trybuild` UI tests:** `trybuild` spawns `cargo`/`rustc` subprocesses against temporary manifests and compares `.stderr` snapshots; inside Bazel's strict sandbox, missing `CARGO`/`CARGO_MANIFEST_DIR`/toolchain paths and path-prefix differences break tests unless explicitly plumbed as `data` deps and environment variables.
4. **Miri / Kani / nightly verification:** `rules_rust` lacks native first-class `miri_test` support on standard `rust_test` targets; running Miri or Kani requires manual nightly toolchain wiring and struggles with `-sys`/FFI crates in the `crate_universe` graph.

#### 4.2 Lightweight Sandbox + Signed CAS (`bubblewrap` and BuildKit + OCI)

Basis: execution + derived

A custom CI runner can enforce per-check repository source closures without adopting Nix or rewriting `Cargo.toml` by combining Linux mount namespaces (`containers/bubblewrap` `v0.12.0` — mounting an empty `--tmpfs /work` and `--ro-bind`ing only allowlisted paths) or `moby/buildkit` (`v0.35.1`) per-check `COPY` stages with a content-addressed cache key `H(check_spec, merkle(filtered_source_tree), pinned_oci_digest)`.

In `support/probe3_bwrap_closure.sh` (`bubblewrap 0.12.0`, `support/probe3_output.txt`), running a check under `bwrap --unshare-all --tmpfs /work --ro-bind <repo>/crates/core /work/crates/core`:

- Reading declared `/work/crates/core/lib.rs` succeeded.
- Reading undeclared `/work/README.md` and `/work/crates/leaf/lib.rs` failed with `No such file or directory` (`exit=1`).
- Mutating read-only `/work/crates/core/lib.rs` failed with `Read-only file system` (`exit=1`).

Compared to Nix, this design has four structural gaps (`derived`):

1. **Host/runtime leakage:** `bwrap --ro-bind /usr /usr` inherits host dynamic libraries unless paired with a pinned rootfs/OCI image; even with `image@sha256:...`, host kernel version, CPU flags (`-C target-cpu=native`), wall-clock time, and `/proc`/`/sys` can leak unless explicitly scrubbed.
2. **Coarse toolchain invalidation:** Keying on a monolithic OCI digest invalidates every check when any unrelated tool in the base image changes, whereas Nix tracks per-check input closures.
3. **No native derivation DAG or early cutoff:** A flat `H(spec, files, image)` check skipper rebuilds from scratch on a miss unless layered with `sccache`, `rust-cache`, or BuildKit cache mounts — and BuildKit cache mounts are mutable and outside the cryptographic cache key, reintroducing impurity risk if misused.
4. **DIY trust and attestation:** Nix binary caches provide built-in Ed25519 `.narinfo` signatures and closure invariants; a custom CAS must implement its own signing, read/write credential separation (preventing untrusted PR forks from poisoning trusted keys), and garbage collection.

#### 4.3 Non-Sandboxed Affected-Selection Failure Modes and Complementary Cargo Caches

Basis: documentation + source

**Why non-sandboxed affected-test selection is unsound for Rust:** Heuristic skipping using `git diff` + `cargo metadata` (or task-graph hashers with manually maintained `inputs` globs) fails silently when a check reads undeclared inputs:

1. **`build.rs` arbitrary reads:** Build scripts can read arbitrary repo files or environment variables without emitting `cargo::rerun-if-changed=<path>`.
2. **Compile-time file inclusion:** `include_bytes!("../testdata/foo.bin")` and `include_str!("../../README.md")` can reach outside a crate's `Cargo.toml` directory; `cargo metadata` does not parse Rust ASTs or macro expansions.
3. **Proc-macro side-channel reads:** Proc macros execute arbitrary Rust code at compile time and can call `std::fs::read` or `std::env::var`; `rustc --emit=dep-info` does **not** record `std::env::var` or untracked file reads inside proc macros, and unlisted sibling files (e.g., `foo/mod.rs`) can fail to invalidate cached results (`mozilla/sccache` `docs/Rust.md`).
4. **Non-Rust test fixtures and golden files:** Integration tests, `trybuild` `.stderr` snapshots, shell scripts, and schemas read via `CARGO_MANIFEST_DIR` are invisible to `cargo metadata`.
5. **`Cargo.lock` and workspace feature unification:** Editing a feature flag or dependency in crate B can alter the unified feature set of a shared dependency D used by crate A (`guppy-rs/guppy` `tools/cargo-hakari/README.md`), changing crate A's compiled behavior without modifying any file under crate A.

**Complementary caches on dirty core-file misses:** Whole-check source-closure skipping yields **0% savings** when a core file shared by all downstream checks changes. In that regime, compilation caches and archive splits remain essential:

- **`mozilla/sccache` (`v0.19.0`, `docs/Rust.md`):** Wraps `rustc` (`RUSTC_WRAPPER=sccache`) to cache per-crate `.rlib`/`.rmeta` artifacts keyed by `rustc --emit=dep-info`, flags, and environment. Documented caveats: cannot cache crates that invoke the system linker (`bin`, `dylib`, `cdylib`, `proc-macro`); rejects `CARGO_INCREMENTAL=1` unless `SCCACHE_ALLOW_INCREMENTAL=1|cache`; requires `SCCACHE_BASEDIRS` (and `SCCACHE_BASEDIRS_VERBATIM_ENV_DEPS`) to avoid absolute-path misses across ephemeral CI checkouts; does not detect changes to native libraries linked by a proc-macro.
- **`Swatinem/rust-cache` (`v2.9.3`, `README.md`):** Caches `~/.cargo` and dependency artifacts in `target/` keyed on `rustc` version, `Cargo.toml`/`Cargo.lock`, `rust-toolchain*`, `.cargo/config.toml`, and env-var prefixes (`CARGO`, `CC`, `CFLAGS`, `CXX`, `CMAKE`, `RUST`), while purging workspace crate objects by default to bound cache size.
- **`cargo-hakari` (`guppy-rs/guppy`, `tools/cargo-hakari/README.md`):** Generates a `workspace-hack` crate that unifies dependency features across workspace members, preventing Cargo from recompiling shared dependencies multiple times with different feature sets across separate check invocations.
- **`cargo-nextest` archives (`nextest-rs/nextest` `0.9.152`):** `cargo nextest archive --archive-file nextest-archive.tar.zst` bundles compiled test binaries, `OUT_DIR`, and metadata once so sharded CI runners (`--partition count:i/N` or hashed) can execute tests without recompiling or requiring `cargo`.

### 5. Architectural Comparison Matrix

Basis: derived (synthesized from Sections 1–4)

| Dimension | Nix (`lib.fileset` + `crane` + `nix-eval-jobs` + Binary Cache) | Bazel (`rules_rust`) / Buck2 (`reindeer`) | Lightweight Sandbox + Signed CAS (`bwrap` / BuildKit + OCI) | Cargo / `sccache` / `rust-cache` / Affected-Selection (`git diff` + `cargo metadata`) |
| :--- | :--- | :--- | :--- | :--- |
| **Source-Closure Enforcement** | **Strong on Linux** (kernel namespaces + seccomp); **opt-in / weaker on macOS** (Seatbelt); **none on native Windows** | **Strong** (kernel/symlink action sandbox exposes only declared `srcs`/`data`) | **Strong for repo files on Linux** (mount-ns / `COPY` fails undeclared reads with `ENOENT`) | **None (advisory):** undeclared reads (`build.rs`, `include_str!`, proc-macros, fixtures) silently pass and poison skip decisions |
| **Toolchain & Dep Pinning Granularity** | **Per-check fine-grained:** exact `rustc`/MSRV/nightly/cross derivations (`fenix`/`rust-overlay`) | **Per-target fine-grained:** registered toolchains + `crate_universe`/`reindeer` targets | **Coarse (container image):** monolithic OCI digest busts all checks on base-image bumps unless split per tool | **Coarse / ambient:** runner OS + `rustup` + `Cargo.lock`; runner image drift not hermetically enforced |
| **Pre-Run Skip / Cache Probe Cost** | **Low (with `--lazy-trees`):** `nix eval` / `nix-eval-jobs` + `HEAD <hash>.narinfo` or `nix path-info --store` (breaks for floating `ca-derivations` unless probing `.doi`) | **Low–Moderate:** build graph analysis + REAPI `GetActionResult` digest lookup | **Very Low:** local Merkle hash of allowlisted files + OCI digest -> single CAS `HEAD` | **Very Low:** `git diff` + `cargo metadata` or task-hash lookup (fast, but unsound) |
| **Early Cutoff & Core-File Miss Recovery** | **Coarse (`buildDepsOnly`):** `crane` caches third-party deps (`cargoArtifacts`), no per-crate `.rmeta` early cutoff inside workspace | **Best-in-class:** per-crate compilation actions + `.rmeta` early cutoff + remote execution | **None built-in:** whole-check miss rebuilds from scratch unless layered with `sccache`/`rust-cache`/BuildKit cache mounts | **Good for compilation, none for skip:** `sccache` + `rust-cache` + `cargo-hakari` + `cargo-nextest` archives speed up dirty builds, though `sccache` skips linker crates |
| **Cargo Ecosystem Compatibility (`trybuild`, Miri, Kani, proc-macros)** | **High:** runs real `cargo` inside derivations once dependencies are vendored | **Low–Moderate:** dual `Cargo.toml` + `BUILD`/`BUCK` maintenance; high friction for `trybuild`, Miri, Kani, and `no_std` proc-macros | **High:** runs real `cargo` inside `bwrap`/OCI container | **Native:** 100% standard Cargo workflows |
| **Cache Trust & Poisoning Model** | **Built-in:** Ed25519 `.narinfo` signatures + closure invariant; PR forks need read-only credentials | **Built-in (REAPI):** remote cache ACLs separate read-only PRs from trusted writers | **DIY:** must implement signing, read/write isolation, and GC around S3/GCS/OCI registry | **Platform-managed (e.g., GHA cache):** branch-scoped; vulnerable to key collisions or non-hermetic contamination |

## Boundaries

- **`not examined` — End-to-end `ca-derivations` `.doi` realization cache hits:** Pre-build placeholder generation was observed locally (`support/probe2_output.txt`) and `BinaryCacheStore::queryRealisationUncached` was verified in `NixOS/nix` source, but end-to-end `nix copy` and `.doi` realization cache hits across two stores were not executed.
- **`not examined` — Live `nix-eval-jobs` execution:** `nix-eval-jobs` (`v2.35.4`) behavior (`--workers`, `--max-memory-size`, `--check-cache-status`, `CacheStatusResolver`) was verified from upstream source and documentation, not executed on a live host.
- **`not examined` — Shared vs. per-check `crane` `buildDepsOnly` cost trade-off:** The exact invalidation rules of `mkDummySrc` / `cargoTomlConservative` are established from `crane` `v0.24.0` source, but empirical wall-clock and cache-hit ratios comparing one shared workspace `cargoArtifacts` against per-check `buildDepsOnly` derivations on a large multi-crate Rust repository were not measured.
- **`not examined` — CI-platform PR-fork cache-write isolation:** Separating read-only untrusted PR evaluation from trusted-writer cache population (e.g., GitHub Actions `pull_request` vs. `pull_request_target` / merge queue with Attic, Cachix, S3, or custom CAS) is an architectural requirement noted in comparison, not empirically probed here.
- **`known not to apply` — `.narinfo` pre-build probing on floating `ca-derivations`:** Pre-build `outPath` probing via `<32-char-hash>.narinfo` or `nix path-info <outPath>` does not apply when `__contentAddressed = true` because `outPath` is a 52-character placeholder until realization.
- **`known not to apply` — Soundness of non-sandboxed affected-test selection for Rust:** `git diff` + `cargo metadata` or manual-glob task hashers do not guarantee sound check skipping in Rust workspaces because `build.rs`, `include_bytes!`/`include_str!`, proc-macro filesystem/env reads, runtime fixtures, and workspace feature unification bypass static manifest graphs.
- **`known not to apply` — Whole-check skipping on dirty core-file edits:** Enforced source-closure skipping provides 0% skip savings when a core file included in every downstream check's closure is edited; compilation caches (`sccache`, `rust-cache`, `cargo-hakari`) and test-archive splitting (`cargo-nextest`) remain necessary for that regime.
- **`unsupported` — Native Windows Nix sandboxing:** `NixOS/nix` `2.36.0` officially supports only Linux and macOS; `WindowsDerivationBuilderImpl` provides zero filesystem/network/env isolation and inherits host `PATH`.
- **`unsupported` — `bubblewrap` on macOS or Windows:** `bubblewrap` relies on Linux kernel namespaces (`clone(CLONE_NEWNS)`) and is Linux-only.
- **`unsupported` — Git `reftable` format in Nix `libgit2` fetcher (Determinate Nix `3.17.0` / Nix `2.33.3`):** Flake evaluation aborts on `extensions.refstorage = reftable` unless the repository uses `--ref-format=files`.
- **`unsupported` — `sccache` caching of linker-invoking Rust crates:** `mozilla/sccache` `v0.19.0` does not cache `bin`, `dylib`, `cdylib`, or `proc-macro` crates, and rejects `CARGO_INCREMENTAL=1` unless `SCCACHE_ALLOW_INCREMENTAL=1|cache` is set.

## Evidence

### Local Execution Evidence (2026-11-21, `x86_64-linux`)

- **Runtime environment:** `x86_64-linux`, Determinate Nix `3.17.0` (upstream Nix `2.33.3`), local `nixpkgs` store path `/nix/store/wjfxdzblindbl9sp2hbwhi4iyh5jh348-source`, `bubblewrap 0.12.0`.
- **`support/probe1_nix_source_filtering.sh` and `support/probe1_output.txt`:** Demonstrates `lib.fileset.toSource` vs. `self` invalidation across `README.md`, `crates/leaf/src/lib.rs`, and `crates/core/src/lib.rs` edits; confirms `builtins.toFile` rejection of derivation string context without `builtins.unsafeDiscardStringContext`; documents `toJSON` `outPath` coercion workaround (`drv_path`/`out_path`).
- **`support/probe2_nix_lazy_trees_and_cache.sh` and `support/probe2_output.txt`:** Demonstrates `--lazy-trees` avoiding store copy of 2 MiB `unrelated-large.bin` (`NONE`) vs. `--no-lazy-trees` copying it to `/nix/store/7z8zwi5sghy9rcbhrymcbf1dczisgwf2-source/unrelated-large.bin`; records exact `h0f60ka9axqjz52ymp0vkiag7w0yq8vm.narinfo` contents; confirms `nix path-info --store file://.../cache --json <unbuilt-outPath>` exits `0` with `{"<outPath>":null}` and does not realize the derivation; records pre-build `ca-derivations` placeholder `/1q37br5pbz5sa9wy23mb8g7wwv84ajv1qriqwwj3zkhqwc4kim7i`.
- **`support/probe3_bwrap_closure.sh` and `support/probe3_output.txt`:** Demonstrates `bubblewrap 0.12.0` (`--unshare-all --tmpfs /work --ro-bind <repo>/crates/core /work/crates/core`) allowing declared reads, blocking undeclared reads with `ENOENT` (`exit=1`), and blocking writes with `EROFS` (`exit=1`).

### Upstream Source and Documentation Evidence (2026-11-21)

- **`NixOS/nix` (`3705f35ddcdca8d777c1d75b939eb6a3a4ac9ebb`, `2.36.0`):**
  - `src/libstore/binary-cache-store.cc`: L128, L347–348 (`<hashPart>.narinfo` layout and closure invariant); L646–649 (`BinaryCacheStore::queryRealisationUncached`, `realisations/<drv-modulo-hash>/<outputName>.doi`).
  - `src/libstore/include/nix/store/local-settings.hh`: L354–388 (`smEnabled` on Linux vs. `smDisabled` on macOS/Windows), L452–488, L571–598 (`filter-syscalls`, `allow-new-privileges`).
  - `src/libstore/unix/build/unix-derivation-builder.cc`: L1054–1101 (`relaxed` exemptions, diverted-store/remapping checks).
  - `src/libstore/linux/build/linux-derivation-builder.cc`: L596–600, L913–919 (Linux namespace flags and isolation).
  - `src/libstore/darwin/build/darwin-derivation-builder.cc`: L14–16, L58–237 (`sandbox_init_with_parameters()`, ~10k–12k 32-bucket store-path ceiling, path-remapping rejection).
  - `src/libstore/darwin/build/sandbox-defaults.sb` (L1–117) and `src/libstore/darwin/build/sandbox-minimal.sb` (L1–9).
  - `src/libstore/windows/build/windows-derivation-builder.cc`: L71–85, L127–142, L210–216, L304–320 (no sandboxing, inherited `PATH`).
  - `doc/manual/source/installation/supported-platforms.md`: L1–7 (Linux and macOS only).
- **`DeterminateSystems/nix-src` (`a21b800b3c1640f2350cc311fee1a2f64576e33a`, `v3.24.3`):** Lazy-trees documentation and configuration.
- **`nix-community/nix-eval-jobs` (`9f1553afabd95f9f59951f5c946e86005af7196a`, `v2.35.4`):** `README.md` and `src/cache-status-resolver.cc` (`--workers`, `--max-memory-size`, `--check-cache-status`, `CacheStatusResolver`).
- **`ipetkov/crane` (`95e62def851e9d650f0eab63cb4f59a3306e20bd`, `v0.24.0`):** `lib/mkDummySrc.nix` (L99–154, L200–336, L369–376), `lib/findCargoFiles.nix` (L18–53), `lib/cleanCargoToml.nix` (L9–35), `lib/default.nix` (L112–116), `lib/filters/cargoTomlConservative.nix` (L21–112), `lib/buildDepsOnly.nix` (L37–90), `lib/cleanCargoSource.nix`.
- **`nix-community/fenix` (`ea745d6a7730c73bb5e0c028818240234e7bda05`):** `README.md`.
- **`oxalica/rust-overlay` (`a5c999945da3991d7aa3cc2a6075cfd22bd387e9`):** `README.md`.
- **`bazelbuild/rules_rust` (`5d99ff2e58d1a0c9387fc4945029df11144bc8a3`, `0.75.0`):** `crate_universe` and architecture documentation.
- **`facebookincubator/reindeer` (`5981c7a3faacee2efc15584a94c0caa851c6517b`):** `README.md` and `docs/MANUAL.md`.
- **`mozilla/sccache` (`1616af1ba4881ad17d1619884042febaa5189055`, `v0.19.0`):** `docs/Rust.md`.
- **`Swatinem/rust-cache` (`eedcf2fb1c22f010a0eb66b92f378c110977f266`, `v2.9.3`):** `README.md`.
- **`guppy-rs/guppy` (`0cbe52c4cbf4ac55bc2fa9ba7f8f5d14288fe478`):** `tools/cargo-hakari/README.md`.
- **`nextest-rs/nextest` (`bb7472661992548512163aa563bee0948db47a4f`, `cargo-nextest-0.9.152`):** Archive and partitioning documentation (`cargo nextest archive`, `--partition`).

## Revalidation

1. **Nix source filtering, string context, lazy trees, `.narinfo`, and `ca-derivations`:**
   - Rerun `support/probe1_nix_source_filtering.sh` and `support/probe2_nix_lazy_trees_and_cache.sh` on the target Nix version (overriding `NIXPKGS_SRC` and `BUSYBOX` environment variables if the host store uses different paths). Confirm: (a) `check-core-fileset` stays unchanged across `README.md` and `crates/leaf` edits, (b) `--lazy-trees` does not copy `unrelated-large.bin` to `/nix/store`, (c) `nix path-info --store ... --json <missing>` still exits `0` with `null` (and check whether `--json-format` became mandatory, as warned in `support/probe2_output.txt`), and (d) whether `ca-derivations` still emits a placeholder `outPath`.
   - To check `reftable` support in a newer Nix release, replace `git init --ref-format=files` with `git init --ref-format=reftable` in Probe 1 and test `nix eval`.
2. **`crane` `mkDummySrc` invalidation rules:**
   - Diff `lib/mkDummySrc.nix`, `lib/filters/cargoTomlConservative.nix`, `lib/findCargoFiles.nix`, and `lib/buildDepsOnly.nix` against `ipetkov/crane@95e62def851e9d650f0eab63cb4f59a3306e20bd`. Any change to the retained TOML key list or `builtins.readDir` target discovery directly alters what edits bust `cargoArtifacts`.
3. **Nix cross-OS sandbox parity:**
   - Diff `src/libstore/include/nix/store/local-settings.hh` (`sandbox` default per platform), `src/libstore/darwin/build/darwin-derivation-builder.cc`, `src/libstore/darwin/build/sandbox-defaults.sb`, `src/libstore/windows/build/windows-derivation-builder.cc`, and `doc/manual/source/installation/supported-platforms.md` against `NixOS/nix@3705f35ddcdca8d777c1d75b939eb6a3a4ac9ebb`.
4. **`bubblewrap` confinement:**
   - Rerun `support/probe3_bwrap_closure.sh` on the target Linux kernel/CI runner (notably checking whether unprivileged user namespaces are allowed under the runner's AppArmor/sysctl policy).
5. **`sccache` and `nix-eval-jobs` contracts:**
   - Diff `mozilla/sccache` `docs/Rust.md` against `1616af1ba4881ad17d1619884042febaa5189055` for linker-crate caching or incremental-compilation changes, and diff `nix-community/nix-eval-jobs` `src/cache-status-resolver.cc` against `9f1553afabd95f9f59951f5c946e86005af7196a` for `cacheStatus` schema changes.
