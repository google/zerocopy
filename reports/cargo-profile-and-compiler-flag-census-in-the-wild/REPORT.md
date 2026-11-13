# Cargo Profile Configurations, Compiler Flags, and Release Pipelines in the Wild

## Summary

Defining the compilation configurations that a verified `rustc` mode must
support requires distinguishing three layers: Cargo's built-in profile defaults
and implicit flag resolutions, `[profile.*]` customizations across library
crates versus application workspaces, and environment-level `RUSTFLAGS` / PGO /
BOLT pipelines used by major binaries, operating-system kernels, and Linux
distributions:

1. **Cargo 1.99.1 built-in defaults and deferred resolutions:** In Cargo `1.99.1`
   (`5f94df4789f005f9a352888e8355ffc645b7ed0e`, `src/workspace/profiles.rs`),
   `dev` defaults to `opt-level = 0`, `debug = 2` (`Full`),
   `debug-assertions = true`, `overflow-checks = true`, `incremental = true`,
   and `codegen-units = 256`, while `release` defaults to `opt-level = 3`,
   `debug = 0` (`None`), `debug-assertions = false`, `overflow-checks = false`,
   `incremental = false`, and `codegen-units = 16`. Both profiles default to
   `lto = false` (`Lto::Bool(false)`) and `panic = "unwind"`. Crucially, Cargo
   applies three non-obvious implicit rules:
   - When `lto = false`, Cargo passes `-C embed-bitcode=no` and omits `-C lto`,
     which causes `rustc` at `opt-level >= 1` and `codegen-units > 1` to execute
     **crate-local ThinLTO (`Lto::ThinLocal`)** across the crate's codegen
     units; only explicit `lto = "off"` (`-C lto=off`) disables crate-local
     ThinLTO.
   - `strip` defaults to `Strip::Deferred(StripInner::None)`: whenever no unit
     in the build graph requests debuginfo (the default in `--release`), Cargo
     automatically promotes `strip` to **`-C strip=debuginfo`** to strip
     pre-existing DWARF/PDB debug sections inherited from `libstd` and `libcore`
     `.rlib` archives.
   - Procedural macros, `build.rs` scripts, and their host-only dependencies
     force `opt-level = 0`, `PanicSetting::AlwaysUnwind` (`panic = "unwind"`),
     and `DebugInfo::Deferred` (weakened to `debug = 0` unless shared with a
     target dependency).
2. **Sharp divergence between published library crates and application workspaces:**
   Because Cargo ignores `[profile.*]` tables in non-root dependency manifests,
   only **11 of the top 100 crates by recent downloads** (`11.0%`, `10.1%` of
   download volume) and **200 of 3,680 unique crates** (`5.43%`) in the local
   crates.io cache define any `[profile.*]` table in their original
   `Cargo.toml.orig`. By contrast, **18 of 18 major Rust application and system
   workspaces** (`100%`) customize `[profile.release]` or define custom named
   profiles (`dist`, `profiling`, `release-lto`, `minimal-size`, `production`).
   Across customizing crates.io packages (`N = 152` with `[profile.release]`),
   the dominant overrides are `lto = true` / `"fat"` (`63.8%`) or `"thin"`
   (`15.8%`), `codegen-units = 1` (`48.0%`), `opt-level = 3` (`39.5%`) or
   `"s"`/`"z"` (`11.2%`), `debug = true`/`1`/`2` (`23.0%`), `panic = "abort"`
   (`16.4%`), and `strip = true`/`"symbols"` (`13.8%`).
3. **Production release workflows, Linux distributions, kernel builds, and PGO/BOLT:**
   Among the 18 major application repositories examined, **13 (`72.2%`)** enable
   LTO (`8` `thin`, `5` `fat`/`true`), **12 (`66.7%`)** set `codegen-units = 1`,
   **7 (`38.9%`)** set `panic = "abort"` in `release` or `dist` profiles, and
   **4 (`22.2%`: `rustc`, `ruff`, `uv`, and `uutils/coreutils`)** run multi-step
   **Profile-Guided Optimization (`-Cprofile-generate` / `-Cprofile-use`)** in
   their official release workflows. Official `rustc 1.99.1` Linux distributions
   (`src/tools/opt-dist`) further apply **LLVM BOLT** (`llvm-bolt
   -reorder-blocks=ext-tsp -reorder-functions=cdsort -split-functions
   -split-strategy=cdsplit -split-all-cold -icf=all`). Distribution packaging
   (Arch Linux `makepkg` `rust.conf`, Fedora `rust-srpm-macros`, Debian
   `dh-cargo`) and `denoland/deno` inject `-C force-frame-pointers=yes` and
   `-C debuginfo=2 -C strip=none`, while the Linux kernel (`rust/Makefile` and
   `Makefile`) compiles Rust directly without Cargo under `-Copt-level=2
   -Cpanic=abort -Cembed-bitcode=n -Clto=n -Cforce-unwind-tables=n
   -Ccodegen-units=1 -Csymbol-mangling-version=v0 -Crelocation-model=static
   -Zfunction-sections=n`.

## Applicability

These findings apply to **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`) and **Cargo 1.99.1**
(`rust-lang/cargo` `5f94df4789f005f9a352888e8355ffc645b7ed0e`) across the
eight Tier 1 targets (`x86_64-unknown-linux-gnu`, `x86_64-pc-windows-msvc`,
`x86_64-pc-windows-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`,
`aarch64-pc-windows-msvc`, `i686-unknown-linux-gnu`, and
`i686-pc-windows-msvc`):

- **Exact observation:** Built-in profile defaults and target-spec defaults were
  extracted from `rust-lang/cargo` (`src/workspace/profiles.rs`) and verified by
  running `cargo +1.99.1-x86_64-unknown-linux-gnu build --lib -v` and
  `rustc +1.99.1 -Z unstable-options --print target-spec-json` across all eight
  Tier 1 targets. Ecosystem profile statistics were collected across the pinned
  Top-100 crates by recent downloads (`8,422,968,730` 90-day downloads; see
  `rustc-experimental-corpora-and-harness-conventions`), `3,680` unique crates
  in the local crates.io source cache, `18` pinned GitHub application workspaces,
  the Linux kernel (`torvalds/linux` `7e1392a42ea288d70a266f6553fe06f57f8647ea`),
  and Arch Linux `devtools` (`c677b681beb02427762e49deef31f635edc2834f`).
- **Design relevance:** Weighting compiler configurations by real-world use
  determines which flag combinations a verified `rustc` backend must prove and
  support in its initial release versus later extensions.

## Findings

### 1. Cargo 1.99.1 built-in profiles and target-specific `rustc` defaults

Basis: source + execution

In `rust-lang/cargo` (`5f94df4789f005f9a352888e8355ffc645b7ed0e`,
`src/workspace/profiles.rs:157-188` and `650-750`), Cargo defines two root
profiles (`dev` and `release`) and four predefined derived profiles (`test`,
`doc`, and `debug` inheriting from `dev`; `bench` inheriting from `release`).
Table 1 summarizes the resolved settings and empirical `rustc` flags emitted by
`cargo +1.99.1 build -v`.

| Profile | `opt-level` | `lto` | `codegen-units` | `debug` (`debuginfo`) | `strip` | `debug-assertions` | `overflow-checks` | `panic` | `incremental` | Emitted `rustc` Codegen Flags (`x86_64-unknown-linux-gnu`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `dev` | `"0"` | `false` (`ThinLocal` off at `-O0`) | `256` (rustc default when `incremental=true`) | `2` (`Full`) | `Deferred(None)` $ightarrow$ `none` | `true` | `true` | `"unwind"` | `true` (`false` if `CI=1`) | `-C embed-bitcode=no -C debuginfo=2 -C incremental=<dir>` |
| `release` | `"3"` | `false` (`ThinLocal` across 16 CGUs) | `16` (rustc default when `incremental=false`) | `0` (`None`) | `Deferred(None)` $ightarrow$ `debuginfo` | `false` | `false` | `"unwind"` | `false` | `-C opt-level=3 -C embed-bitcode=no -C strip=debuginfo` |
| `test` | `"0"` | `false` | `256` | `2` (`Full`) | `none` | `true` | `true` | Forced `"unwind"` (`AlwaysUnwind`) | `true` | `--test -C embed-bitcode=no -C debuginfo=2 -C incremental=<dir>` |
| `bench` | `"3"` | `false` | `16` | `0` (`None`) | `debuginfo` | `false` | `false` | Forced `"unwind"` (`AlwaysUnwind`) | `false` | `--test -C opt-level=3 -C embed-bitcode=no -C strip=debuginfo` |
| Host `build.rs` / `proc-macro` | `"0"` (overridden in `get_profile`, line 471) | `false` | `None` (`rustc` default) | `Deferred` (weakened to `0` if unshared) | `none` / `debuginfo` | Inherits root | Inherits root | Forced `"unwind"` (`AlwaysUnwind`) | Inherits root | `-C embed-bitcode=no` (omits `-C opt-level=3` even under `--release`) |

Four implementation invariants in `src/workspace/profiles.rs` and `rustc`'s
target specifications govern how these defaults translate into backend work:

1. **`lto = false` vs. `lto = "off"` (`src/workspace/profiles.rs:864-872`):**
   Cargo distinguishes `Lto::Bool(false)` (the default) from `Lto::Off`
   (`lto = "off"`). Under `Lto::Bool(false)`, Cargo passes `-C embed-bitcode=no`
   (since no cross-crate LTO requires LLVM bitcode inside `.rlib` archives) and
   omits `-C lto`. Inside `rustc` (`compiler/rustc_session/src/config.rs`), an
   unspecified `-C lto` with `opt-level != 0` and `codegen-units > 1` activates
   `Lto::ThinLocal` (intra-crate ThinLTO across the crate's 16 codegen units).
   Passing `lto = "off"` in `Cargo.toml` emits `-C lto=off`, disabling even
   intra-crate `ThinLocal` LTO.
2. **Automatic `-C strip=debuginfo` in release builds
   (`src/workspace/profiles.rs:932-962`):** Because official `rust-std` `.rlib`
   archives ship with embedded DWARF/CodeView debug sections for the standard
   library, Cargo initializes `strip` to `Strip::Deferred(StripInner::None)`.
   When no unit in the compilation graph has `debuginfo.is_turned_on()`, Cargo
   calls `strip_debuginfo()` to emit `-C strip=debuginfo`. A verified `rustc`
   driver must therefore accept `-C strip=debuginfo` (and `-C strip=symbols` /
   `-C strip=none`) as part of standard `--release` invocations.
3. **Automatic CI incremental disablement (`src/workspace/profiles.rs:76-82`):**
   When `CARGO_INCREMENTAL` and `build.incremental` are unset, Cargo checks
   `cargo_util::is_ci()` (detecting `CI`, `GITHUB_ACTIONS`, `BUILD_ID`, etc.)
   and defaults `incremental` to `false` in CI environments.
4. **Target-specific baseline CPU features, frame pointers, and `split-debuginfo`:**
   Querying `rustc +1.99.1 -Z unstable-options --print target-spec-json` across
   all eight Tier 1 targets shows that several codegen properties vary by target
   triple even before user flags are applied (Table 2).

| Tier 1 Target | Default `-C target-cpu` | Default Target Features | Default `frame-pointer` | Default `split-debuginfo` | Supported `split-debuginfo` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `x86-64` (SSE2) |*(none beyond `x86-64`)* | `may-omit` | `off` | `packed`, `unpacked`, `off` |
| `x86_64-pc-windows-msvc` | `x86-64` | `+cmpxchg16b,+sse3,+lahfsahf` | `may-omit` | `packed` (`.pdb`) | `packed`, `unpacked`, `off` |
| `x86_64-pc-windows-gnu` | `x86-64` | `+cmpxchg16b,+sse3,+lahfsahf` | `may-omit` | `off` | `off` |
| `aarch64-unknown-linux-gnu` | `generic` (`v8a`) | `+v8a,+outline-atomics` | `non-leaf` | `off` | `packed`, `unpacked`, `off` |
| `aarch64-apple-darwin` | `apple-m1` |*(Apple M1 baseline: Neon, LSE, DotProd, FP16, AES, SHA2, CRC)* | `non-leaf` | `packed` (`.dSYM`) | `packed`, `unpacked`, `off` |
| `aarch64-pc-windows-msvc` | `generic` (`v8a`) | `+v8a,+neon` | `non-leaf` | `packed` (`.pdb`) | `packed`, `unpacked`, `off` |
| `i686-unknown-linux-gnu` | `pentium4` (SSE2) |*(none beyond `pentium4`)* | `may-omit` | `off` | `packed`, `unpacked`, `off` |
| `i686-pc-windows-msvc` | `pentium4` (SSE2) |*(none beyond `pentium4`)* | `may-omit` | `packed` (`.pdb`) | `packed`, `unpacked`, `off` |

### 2. Crates.io `[profile.*]` census: top-100 download corpus and 3,680 unique packages

Basis: source + execution

Because Cargo ignores `[profile.*]` tables in non-root dependency manifests and
`cargo package` strips workspace-only tables when generating normalized
`Cargo.toml` files inside `.crate` tarballs, inspecting `.crate` archives
requires reading `Cargo.toml.orig` (the un-normalized manifest preserved inside
each archive).

Across the **Top-100 crates by recent downloads** (`8.42B` recent / `52.25B`
all-time downloads), only **11 crates (`11.0%` unweighted, `10.1%` of recent
downloads)** define any `[profile.*]` section in `Cargo.toml.orig`:
- **Benchmark/test debuginfo and optimization (`6` crates):** `itertools`,
  `indexmap`, `base64`, `memchr`, `regex`, and `aho-corasick` set
  `[profile.bench] debug = true` and/or `[profile.test] opt-level = 3` so
  profiling tools (`perf`, `flamegraph`) can symbolicate benchmarks and
  compute-heavy tests run quickly.
- **Release LTO / single-CGU / `panic = "abort"` (`5` crates):** `clap` sets
  `[profile.release] lto = true, codegen-units = 1, panic = "abort"` and
  `[profile.dev] panic = "abort"`; `cc` sets `[profile.release] opt-level = 3,
  lto = true`; `zerocopy` sets `[profile.release] lto = "fat",
  codegen-units = 1, opt-level = 3`; `rand_chacha` and `ppv-lite86` set
  `[profile.release] debug = true`.

Across all **3,680 unique crates** in the local crates.io cache
(`index.crates.io-1949cf8c6b5b557f`), **200 crates (`5.43%`)** define one or
more `[profile.*]` sections (`152` `release`, `94` `bench`, `42` `dev`, `38`
`test`, and `15` custom profiles such as `release-lto`, `fuzz`, and `dist`).
Table 3 shows the distribution of explicit settings within those customizing
crates.

| Profile Table | Setting Key | Value Distribution Across Customizing Crates (`3,680` Unique Crates Scanned) | Primary Purpose |
| :--- | :--- | :--- | :--- |
| `[profile.release]` (`152` crates) | `lto` (`121` crates) | `true`: `88` (`57.9%`), `"thin"`: `24` (`15.8%`), `"fat"`: `9` (`5.9%`) | Whole-program inlining and dead-code elimination |
| `[profile.release]` (`152` crates) | `codegen-units` (`75` crates) | `1`: `73` (`48.0%`), `16`: `2` (`1.3%`) | Maximize LLVM intra-crate optimization across single module |
| `[profile.release]` (`152` crates) | `opt-level` (`78` crates) | `3`: `60` (`39.5%`), `"s"`: `10` (`6.6%`), `"z"`: `7` (`4.6%`), `2`: `1` (`0.7%`) | Peak throughput (`3`) or binary size minimization (`s`/`z`) |
| `[profile.release]` (`152` crates) | `debug` (`38` crates) | `true`: `29` (`19.1%`), `1`: `4` (`2.6%`), `2`: `2` (`1.3%`), `false`/`0`: `3` (`2.0%`) | Retain DWARF symbols for production profiling / crash backtraces |
| `[profile.release]` (`152` crates) | `panic` (`25` crates) | `"abort"`: `25` (`16.4%`) | Eliminate landing pads and `.eh_frame` unwind tables |
| `[profile.release]` (`152` crates) | `strip` (`21` crates) | `true`: `12` (`7.9%`), `"symbols"`: `8` (`5.3%`), `"debuginfo"`: `1` (`0.7%`) | Strip symbol tables from final release binaries |
| `[profile.release]` (`152` crates) | `overflow-checks` (`8` crates) | `true`: `7` (`4.6%`), `false`: `1` (`0.7%`) | Harden arithmetic against wrapping in security-sensitive release builds |
| `[profile.release]` (`152` crates) | `incremental` (`7` crates) | `false`: `6` (`3.9%`), `true`: `1` (`0.7%`) | Deterministic non-incremental release codegen |
| `[profile.bench]` (`94` crates) | `debug` (`67` crates), `lto` (`22`), `codegen-units` (`19`), `opt-level` (`19`) | `debug = true`/`1`/`2` (`66`), `lto = true`/`"thin"` (`22`), `codegen-units = 1` (`19`), `opt-level = 3` (`19`) | Symbolicated Criterion/libtest benchmarks at peak optimization |
| `[profile.dev]` (`42` crates) | `opt-level` (`21` crates), `panic` (`9`), `debug` (`9`), `package_overrides` (`7`) | `opt-level = 2`/`3`/`1` (`17`), `panic = "abort"` (`9`), `debug = 0`/`1`/`false` (`7`) | Speed up slow debug builds (`opt-level`) and reduce link time/RAM (`debug=0/1`) |
| `[profile.test]` (`38` crates) | `opt-level` (`26` crates), `debug` (`9`) | `opt-level = 3`/`2`/`1` (`26`), `debug = true`/`1`/`0` (`9`) | Accelerate compute-intensive test suites (crypto, compression, regex) |

### 3. Major Rust applications, workspaces, and CI/release workflows

Basis: source

Unlike library crates, application and workspace root repositories directly
control binary compilation. Table 4 records the exact `[profile.*]` and CI/release
workflow configurations across 18 major Rust workspaces at pinned Git commits,
together with `rust-lang/rust` (`1.99.1`) itself.

| Repository & Pinned Commit | `[profile.release]` Configuration | Custom Profiles (`[profile.<name>]`) | CI / Release Workflow `RUSTFLAGS` & PGO/BOLT Usage |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` (`58cf8f9c35b3`, `library/Cargo.toml` & `Cargo.toml`) | `library`: `lto = "off"`, `codegen-units = 1` (`compiler_builtins`: `opt-level = 3`, `codegen-units = 10000`); `compiler`: `opt-level = 3`, `debug = 0`, `codegen-units = 256` (`opt-dist` overrides to `codegen-units = 1`, `lto = "thin"`) | `dev` sets `debug = 0`, `opt-level = 1` (`library`: `opt-level = 2`) | `src/tools/opt-dist`: multi-stage **LLVM PGO + `rustc` PGO** (`-Cprofile-generate` / `-Cprofile-use`) + **LLVM BOLT** (`llvm-bolt -reorder-blocks=ext-tsp -reorder-functions=cdsort -split-functions -split-strategy=cdsplit -split-all-cold -icf=all`) |
| `BurntSushi/ripgrep` (`4649aa970061`) | `debug = 1` | `deb`: `inherits = "release"`, `debug = false` | `release.yml`: builds Debian package with `--profile deb`; strips release binaries |
| `sharkdp/fd` (`b19136871310`) | `lto = true`, `codegen-units = 1`, `strip = true` |*(none)* | Uses `jemallocator` on Linux/macOS; full Fat LTO + `codegen-units = 1` |
| `astral-sh/ruff` (`cf41c5e87612`) | `lto = "fat"`, `codegen-units = 1`, `strip = "symbols"` | `minimal` (`lto = "off"`, `opt-level = "s"`), `profiling` (`debug = "full"`, `strip = false`), `ci` (`lto = "thin"`, `codegen-units = 16`, `strip = false`) | `build-binaries.yml`: **PGO (`-Cprofile-generate` / `-Cprofile-use=ruff.profdata`)**, `-C linker=rust-lld -C link-arg=--icf=safe`, `-C target-feature=+crt-static`; `ci.yaml`: `CARGO_PROFILE_DEV_DEBUG=line-tables-only` |
| `astral-sh/uv` (`d5c3f1744174`) | `lto = "fat"`, `codegen-units = 1`, `strip = "symbols"` | `minimal` (`lto = "off"`), `minimal-size` (`opt-level = "z"`, `lto = "fat"`, `codegen-units = 1`, `strip = "symbols"`), `profiling` (`debug = "full"`), `no-debug` | `build-release-binaries.yml`: **PGO (`-Cprofile-use=uv.profdata`)** on Linux/macOS/Windows MSVC, `-C link-arg=-fuse-ld=lld -C link-arg=-Wl,--icf=all`, `-C target-feature=+crt-static` |
| `helix-editor/helix` (`a714a818a3a4`) |*(inherits default release)* | `opt`: `inherits = "release"`, `lto = "thin"`, `codegen-units = 1` | `release.yml`: builds official binaries with `--profile opt` |
| `alacritty/alacritty` (`aa5d942f46c4`) | `lto = true`, `codegen-units = 1`, `panic = "abort"`, `debug = 1`, `incremental = false` |*(none)* | Full Fat LTO + `panic = "abort"` + line-level debuginfo (`debug = 1`) |
| `bytecodealliance/wasmtime` (`68f6475eac03`) |*(workspace default; sets per-package overrides for `cranelift-codegen`)* | `fast-build` (`lto = false`, `codegen-units = 256`, `opt-level = "s"`) | `main.yml`: tests both `unwind` and `RUSTFLAGS="-Cpanic=abort"`; sets `CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=false` |
| `denoland/deno` (`e7b39ebd55c8`) | `codegen-units = 1`, `incremental = true`, `lto = true`, `opt-level = "z"` (with `opt-level = 3` package overrides for hot crates `deno_core`, `v8`, `serde_v8`) | `bench`: `codegen-units = 1`, `lto = true`, `opt-level = 2` | `ci.generated.yml`: `RUSTFLAGS="-C force-frame-pointers=yes -C force-unwind-tables=no -C link-arg=-Wl,--no-eh-frame-hdr"`, `CARGO_PROFILE_DEV_DEBUG=0` |
| `pola-rs/polars` (`437948302e11`) | `lto = "fat"`, `codegen-units = 1` | `opt-dev` (`opt-level = 1`), `debug-release` (`debug = true`), `nodebug-release` (`lto = "thin"`, `codegen-units = 16`, `debug = false`) | `benchmark.yml`: `RUSTFLAGS="-C target-cpu=native"`; `lint-rust.yml`: `RUSTFLAGS="-C debuginfo=0"` |
| `tikv/tikv` (`33aa721d0182`) | `lto = "thin"`, `opt-level = 3`, `debug = 1`, `codegen-units = 1` (`debug-assertions = false`) | `dev`: `opt-level = 0`, `debug = 1`, `codegen-units = 4`, `incremental = true` | Retains `debug = 1` in production for stack-trace symbolication with `lto = "thin"` |
| `vectordotdev/vector` (`fda52a69b3da`) | `opt-level = 3`, `lto = false`, `codegen-units = 1`, `debug = false`, `strip = "debuginfo"` | `release-lto`: `inherits = "release"`, `lto = "fat"`, `codegen-units = 1` | Separates fast CI release builds (`lto = false`) from packaged release builds (`--profile release-lto`) |
| `typst/typst` (`84cca406aafe`) | `lto = true`, `codegen-units = 1`, `panic = "abort"`, `strip = true` |*(none)* | Full Fat LTO + `codegen-units = 1` + `panic = "abort"` + `strip = true` |
| `nushell/nushell` (`a93aaef9f5b9`) | `opt-level = "s"`, `strip = "debuginfo"`, `lto = "thin"` | `ci` (`inherits = "dev"`, `opt-level = 0`, `debug = 0`), `profiling` (`debug = true`, `strip = false`) | Optimizes release binary size (`opt-level = "s"`) with `lto = "thin"` to keep multi-command shell binary compact |
| `uutils/coreutils` (`12e107fc042f`) | `lto = true`, `panic = "abort"`, `codegen-units = 1` | `release-fast` (`lto = "thin"`, `panic = "abort"`, `strip = true`), `release-small` (`opt-level = "z"`, `lto = true`, `panic = "abort"`, `codegen-units = 1`, `strip = true`), `ci` | `CICD.yml`: **PGO (`-Cprofile-use=target/coreutils-pgo/...`)** and `--profile=release-small` for single-binary multicall coreutils |
| `firecracker-microvm/firecracker` (`bd40216958ea`) | `lto = true`, `codegen-units = 1`, `panic = "abort"`, `strip = "none"` | `dev` (`panic = "abort"`), `ci` (`panic = "unwind"`, `incremental = false`) | Enforces `panic = "abort"`, `lto = true`, `codegen-units = 1` for minimal attack surface in microVM monitor |
| `fish-shell/fish-shell` (`4da2a2080191`) | `lto = true`, `overflow-checks = true` | `release-with-debug`: `inherits = "release"`, `debug = true` | Explicitly enables `overflow-checks = true` in production `[profile.release]` alongside Fat LTO |
| `zed-industries/zed` (`aff99ecc3249`) | `lto = "thin"`, `codegen-units = 1`, `debug = "limited"` (`1`), with `[profile.release.package.zed] codegen-units = 16` | `dev` (`debug = "limited"`, `split-debuginfo = "unpacked"`, `opt-level = 3` on 19 hot/macro deps, `codegen-units = 1` on 34 workspace crates), `release-fast` (`lto = false`, `codegen-units = 16`) | Uses `[profile.dev.package.*]` extensively so proc-macros (`syn`, `quote`) and heavy libraries (`wasmtime`, `tree-sitter`, `resvg`, `taffy`) run at `-O3` even in debug builds |
| `servo/servo` (`1107afe32b59`) |*(uses custom profiles inheriting from `release`)* | `production` (`opt-level = "s"`, `lto = true`, `codegen-units = 1`), `production-stripped` (`strip = true`), `checked-release` (`overflow-checks = true`, `debug-assertions = true`), `profiling` (`lto = "thin"`, `codegen-units = 1`, `debug = true`) | `linux-common.yml`: `-C link-arg=-fuse-ld=lld`; `[profile.dev.package]` compiles `sha1`, `sha2`, `crypto-bigint` at `opt-level = 3` |

### 4. OS kernels, Linux distributions, and `rustc`'s PGO + BOLT pipeline

Basis: source

Three non-Cargo or wrapper-driven build environments impose distinct compiler
flag requirements that do not appear in `Cargo.toml` files:

1. **Linux kernel (`torvalds/linux` `7e1392a42ea288d70a266f6553fe06f57f8647ea`,
   `Makefile:619-625`, `938-941`, and `rust/Makefile:226-260`):** The kernel
   invokes `rustc` directly from Kbuild without Cargo, passing:
   ```makefile
   KBUILD_RUSTFLAGS := $(rust_common_flags)                        -Cpanic=abort -Cembed-bitcode=n -Clto=n                        -Cforce-unwind-tables=n -Ccodegen-units=1                        -Csymbol-mangling-version=v0                        -Crelocation-model=static                        -Zfunction-sections=n                        -Wclippy::float_arithmetic
   ```
   along with `-Copt-level=2` (under `CONFIG_CC_OPTIMIZE_FOR_PERFORMANCE`) or
   `-Copt-level=s` (under `CONFIG_CC_OPTIMIZE_FOR_SIZE`), and compiles `core`
   from source with `--cfg no_fp_fmt_parse --cfg no_io_statics`.
2. **Linux distribution packaging defaults (`archlinux/devtools`
   `c677b681beb02427762e49deef31f635edc2834f`, `config/makepkg/conf.d/rust.conf:14-18`):**
   Distribution build systems override upstream project flags via environment
   variables so system-wide profiling (`perf`), debuginfod symbol servers, and
   unwinding work uniformly:
   - **Arch Linux (`makepkg`):** Sets `RUSTFLAGS="-C force-frame-pointers=yes
     -C link-arg=-Wl,--icf=safe"` and `DEBUG_RUSTFLAGS="-C debuginfo=2
     -C strip=none"` with `OPTIONS=(strip docs !libtool !staticlibs emptydirs
     zipman purge debug lto)` in `x86_64.conf:98`.
   - **Fedora (`rust-srpm-macros`) and Debian (`dh-cargo`):** Pass `-C opt-level=3
     -C debuginfo=2 -C codegen-units=1 -C strip=none` (and `-C force-frame-pointers=yes`
     on Fedora), relying on `rpmbuild`/`dh_strip` after compilation to split
     DWARF sections into `-debuginfo` / `-dbgsym` packages.
3. **Official `rustc 1.99.1` PGO + BOLT distribution pipeline (`rust-lang/rust`
   `58cf8f9c35b355199727627d07ae34a4e2846d67`,
   `src/ci/docker/host-x86_64/dist-x86_64-linux/dist.sh:1-14` and
   `src/tools/opt-dist/src/{main.rs,bolt.rs,training.rs}`):**
   - **Step 1 (LLVM PGO):** Builds an instrumented LLVM (`-DLLVM_BUILD_INSTRUMENTED=IR`),
     trains it by compiling `rustc-perf` crate workloads, and merges `.profraw`
     files via `llvm-profdata`.
   - **Step 2 (`rustc` PGO + ThinLTO + `codegen-units = 1`):** Builds an
     instrumented stage-2 `rustc` (`--rust-profile-generate`), runs `rustc-perf`
     benchmarks across `check`, `debug`, and `opt` profiles, and rebuilds
     `rustc` with `--rust-profile-use`, `rust.lto = "thin"`, and
     `rust.codegen-units = 1`.
   - **Step 3 (LLVM BOLT post-link binary optimization, `bolt.rs:58-128`):**
     Instruments both `libLLVM.so` and `librustc_driver.so` with `llvm-bolt
     -instrument`, collects basic-block edge profiles (`prof.fdata`), and
     rewrites the ELF binaries in place with:
     ```text
     llvm-bolt <binary> -data <profile> -o <out>        -reorder-blocks=ext-tsp -reorder-functions=cdsort        -split-functions -split-strategy=cdsplit        -split-all-cold -jump-tables=move -icf=all        -update-debug-sections -dyno-stats
     ```
     (falling back to `-split-strategy=profile2` on `aarch64` due to an upstream
     `llvm-bolt` `cdsplit` limitation; `bolt.rs:64-66`).

### 5. Prioritized configuration set for a verified `rustc` mode

Basis: derived

Combining Cargo's built-in profile semantics with the crates.io, application
workspace, kernel, and distribution censuses yields a three-tier configuration
roadmap for verified compilation (Table 5).

| Priority Tier | Configuration & Compiler Flag Set | Ecosystem Coverage & Rationale |
| :--- | :--- | :--- |
| **Tier 0 — Mandatory Baseline** | `opt-level` $\in \{0, 2, 3, 	ext{"s"}, 	ext{"z"}\}$; `panic` $\in \{	ext{"unwind"}, 	ext{"abort"}\}$; `codegen-units` $\in \{1, 16, 256\}$; `lto` $\in \{	ext{"off"}, 	ext{false (ThinLocal)}\}$; `overflow-checks` $\in \{	ext{true}, 	ext{false}\}$; `debug-assertions` $\in \{	ext{true}, 	ext{false}\}$; `debuginfo` $\in \{0, 1, 2\}$; `strip` $\in \{	ext{"none"}, 	ext{"debuginfo"}, 	ext{"symbols"}\}$; `frame-pointer` $\in \{	ext{"may-omit"}, 	ext{"non-leaf"}, 	ext{"always"}\}$ | Covers `100%` of standard `cargo build` (`dev`), `cargo build --release` (`release`), `cargo test`, Linux kernel `-Copt-level=2 -Cpanic=abort -Ccodegen-units=1 -Clto=n`, and Arch/Fedora/Debian distro packaging builds (`-C force-frame-pointers=yes -C debuginfo=2 -C strip=none`). |
| **Tier 1 — High-Value Whole-Program Release** | Cross-crate `lto = "thin"` and `lto = "fat"` (`true`); per-package `[profile.<name>.package.<dep>]` mixed `opt-level` (`0` + `3`) linking; `-C target-cpu=native` / explicit `-C target-feature=+crt-static,+avx2,+neon`; `-C symbol-mangling-version=v0`; `-C relocation-model=static,pic,pie`; `split-debuginfo` $\in \{	ext{"off"}, 	ext{"packed"}, 	ext{"unpacked"}\}$ | Covers `72.2%` (`13/18`) of major Rust application release builds (`ripgrep`, `fd`, `ruff`, `uv`, `helix`, `alacritty`, `deno`, `polars`, `tikv`, `vector`, `typst`, `nushell`, `coreutils`, `firecracker`, `zed`, `servo`). |
| **Tier 2 — Profile-Guided & Post-Link Pipelines** | `-C profile-generate` / `-C profile-use=<path>.profdata` (LLVM IR PGO); post-link `llvm-bolt` binary layout optimization; unstable `panic = "immediate-abort"`; `-Z function-sections=n` | Used by `4/18` (`22.2%`) of top performance-critical binary releases (`rustc`, `ruff`, `uv`, `uutils/coreutils`); note that PGO and BOLT alter basic-block layout, inlining thresholds, and cold-code splitting without changing source-level semantics, meaning translation validation or backend lowering proofs must either verify post-PGO IR/ASM per compilation or disable PGO/BOLT in verified mode. |

## Boundaries

- **Not examined:** Proprietary internal enterprise monorepos (which often use
  Bazel `rules_rust` or Buck2 rather than Cargo profiles) were not directly
  sampled; however, their underlying `rustc` flags (`-C opt-level`,
  `-C codegen-units=1`, `-C panic=abort`, `-C force-frame-pointers=yes`) map
  onto the same `rustc` codegen option space documented in Section 4.
- **Known not to apply:** `[profile.*]` tables inside non-root crates.io library
  packages do not take effect when those libraries are compiled as dependencies
  of a downstream workspace (`src/workspace/profiles.rs:83-122`); therefore, the
  `5.43%` profile customization rate across crates.io packages must not be
  interpreted as the rate at which end-user binaries are compiled with custom
  profiles.

## Evidence

- **Cargo 1.99.1 profile resolution source:** `rust-lang/cargo` commit
  `5f94df4789f005f9a352888e8355ffc645b7ed0e`, `src/workspace/profiles.rs` lines
  `74-188` (`Profiles::new`, `predefined_profiles`, CI incremental detection),
  `450-606` (`ProfileMaker::get_profile`, host `opt-level = "0"` override,
  `merge_profile`), `650-750` (`Profile::default`, `default_dev`,
  `default_release`), and `864-962` (`Lto`, `PanicStrategy`, `Strip::Deferred`
  and `strip_debuginfo`).
- **Rust 1.99.1 self-build, PGO, and BOLT source:** `rust-lang/rust` commit
  `58cf8f9c35b355199727627d07ae34a4e2846d67`, `Cargo.toml`,
  `library/Cargo.toml`, `src/ci/docker/host-x86_64/dist-x86_64-linux/dist.sh`,
  and `src/tools/opt-dist/src/{main.rs,bolt.rs,training.rs}`.
- **Linux kernel and Arch Linux packaging sources:** `torvalds/linux` commit
  `7e1392a42ea288d70a266f6553fe06f57f8647ea` (`Makefile:619-625`, `938-941`;
  `rust/Makefile:203-268`) and `archlinux/devtools` commit
  `c677b681beb02427762e49deef31f635edc2834f`
  (`config/makepkg/conf.d/rust.conf:14-18`, `config/makepkg/x86_64.conf:39-98`).
- **Preserved support datasets:**
  - `support/profile_census_tables.json` — full JSON dataset containing the
    empirical `rustc` CLI invocations across all 8 Tier 1 targets, target-spec
    defaults, Top-100 and 3,680-crate `[profile.*]` frequency tables, and the
    18 major project profile and GitHub Actions workflow extractions.
  - `support/profile_census_summary.csv` — flat CSV frequency table of
    `[profile.release]` settings across the 3,680-crate registry sample and 18
    major application repositories.

## Revalidation

To revalidate Cargo's built-in profile flag emission and target-spec defaults
on a newer `rustc` / `cargo` toolchain, run:

```bash
cargo +1.99.1-x86_64-unknown-linux-gnu build --lib -v --release
rustc +1.99.1-x86_64-unknown-linux-gnu -Z unstable-options --print target-spec-json --target x86_64-unknown-linux-gnu
```

and compare against `support/profile_census_tables.json` and `src/workspace/profiles.rs`
in the corresponding `rust-lang/cargo` revision.
