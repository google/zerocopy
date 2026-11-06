# Charon Driver, Toolchain Contract, CLI Invocation Modes, Entry Selection, Opacity, and Cargo Extraction

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`, the Charon commit pinned by `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` / release `nightly-2026.06.03`), Charon splits compilation orchestration and compiler-internal MIR extraction across two binaries: the outer `charon` wrapper (`charon/src/bin/charon/main.rs`) and its sibling `charon-driver` (`charon/src/bin/charon-driver/main.rs`). Because `charon-driver` enables `#![feature(rustc_private)]`, imports internal compiler crates (`rustc_driver`, `rustc_middle`, `rustc_hir`, `rustc_interface`, `rustc_mir_build`, `rustc_session`, `rustc_span`, `rustc_target`), and dynamically links `librustc_driver`, it is coupled to an exact Rust nightly toolchain (`nightly`, `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). The outer `charon` binary embeds `charon/rust-toolchain` at compile time via `include_str!` (`charon/src/bin/charon/toolchain.rs`) and routes compiler invocations through either `rustup run nightly <program>` or—when `CHARON_TOOLCHAIN_IS_IN_PATH` is set—directly through `PATH` without performing a runtime compiler-version equality check. Current Anneal (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`) satisfies that trusted-`PATH` contract by packaging Rust `nightly` in `anneal/flake.nix` and configuring `Toolchain::command(Tool::Charon)` (`anneal/src/setup.rs`) with `CHARON_TOOLCHAIN_IS_IN_PATH=1`, the managed `rust/bin` directory on `PATH`, and `LD_LIBRARY_PATH` / `DYLD_LIBRARY_PATH` pointing to the managed Rust libraries before invoking `aeneas/bin/charon`. By contrast, Charon's own `nightly-2026.06.03` release tag resolves to `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (15 commits later), whose `charon/rust-toolchain` selects `nightly`.

The outer `charon` CLI exposes two compiler-facing translation subcommands (`charon cargo` and `charon rustc`), a test harness subcommand (`charon ui_test` / `ui-test`), and three utility subcommands (`charon toolchain-path`, `charon pretty-print`, and `charon version`). `charon cargo` delegates unit-graph construction and dependency compilation to `cargo build`, installing `charon-driver` as `RUSTC_WRAPPER`, setting `CHARON_USING_CARGO=1`, clearing `CARGO_PRIMARY_PACKAGE` from the outer environment, reading `[package.metadata.charon]` from `./Cargo.toml`, and passing serialized `CliOpts` JSON in `CHARON_ARGS`. `charon rustc` bypasses Cargo and invokes `charon-driver` directly with user-supplied `rustc` arguments. Both modes inject `--target <rustc-host>` when no `--target` is present so `charon-driver` can distinguish target-side units (which have `--target`) from host-side build scripts and procedural macros (which lack `--target`), translating only invocations that are both target-side and primary (`CARGO_PRIMARY_PACKAGE` present in Cargo mode) while compiling all other wrapped invocations normally via `RunCompilerNormallyCallbacks`.

Within a selected target crate, Charon does not import Cargo dependencies wholesale or dump every AST node. Instead, `translate_crate::translate` seeds a demand-driven work queue (`items_to_translate` deduplicated by `processed`) from configured entry-point selectors (`--start-from`, `--start-from-if-exists`, `--start-from-attribute`, `--start-from-pub`, or the default strict `crate` root) and recursively registers declarations reached through semantic references, governed by the four-level `ItemOpacity` lattice (`Transparent < Foreign < Opaque < Invisible`). After transformation passes, `reorder_decls::compute_declarations_graph` recomputes reachability from translated `ItemMeta` entries matching `StartFrom::matches` and orders declarations by strongly connected components. Charon's `--targets` flag runs one concurrent translation thread per target triple into isolated temporary files (`<tempdir>/target_<i>.<ext>`) and merges the resulting `CrateData` values via `multi_target::merge` (`CrateMerger` and `ItemDeduplicator`), whereas a single `charon cargo` invocation whose Cargo build graph produces multiple target-side primary `rustc` processes shares one `CHARON_ARGS` output policy without per-unit staging or locking. Finally, all `TranslateCtx` and Hax `State<'tcx>` memoization caches live only for a single `rustc_driver::run_compiler` session; Charon `0.1.210` provides translation-scope pruning (`--start-from` and opacity) and within-run caching, not cross-run incremental LLBC state maintenance or delta serialization.

## Applicability

The findings in this report apply to the following pinned repository revisions recorded in `REPORT.json`:

- **Primary Charon subject (`AeneasVerif/charon`)**:
  - `a535e914f74db4fd9e6be7048f4233270d8945c0` (version `0.1.210`), pinned by `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`) in both `charon-pin` and `flake.lock`, and bundled into Aeneas release archives as `aeneas/bin/charon` and `aeneas/bin/charon-driver`.
- **Comparative Charon revisions (`AeneasVerif/charon`)**:
  - `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (tag `nightly-2026.06.03`, version `0.1.210`), 15 commits ahead of `a535e914f74db4fd9e6be7048f4233270d8945c0`, whose `charon/rust-toolchain` pins `nightly` rather than `nightly`.
  - `67da6d3b8f31dfb0d003aee1596040f9efd7d27f` (later `main` snapshot), referenced solely as a non-authoritative boundary showing that later Charon adds a fresh `RUSTC_WORKSPACE_WRAPPER` fingerprint in `charon/src/bin/charon/main.rs` (`a5aa2c459ccde69502093dcf6988f2a5d314c7d3`) to force Cargo to rerun Charon.
- **Paired Rust compiler (`rust-lang/rust`)**:
  - `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly`), selected by `charon/rust-toolchain` at `a535e914f74db4fd9e6be7048f4233270d8945c0`.
- **Downstream Aeneas and Anneal integration subjects**:
  - `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`), for the boundary between Charon `ItemOpacity` and Aeneas external-model registration.
  - `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix` and `anneal/src/setup.rs`), for Anneal's managed `nightly` toolchain packaging and `CHARON_TOOLCHAIN_IS_IN_PATH=1` invocation contract.

No fresh Charon, Cargo, `rustc`, `rustup`, Nix, or Aeneas execution was performed for this synthesis; checked-in `.out` test goldens in `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` are preserved upstream execution artifacts from that exact revision.

## Findings

### 1. Toolchain Contract, Embedded `rust-toolchain`, and Runtime Provisioning

#### 1.1 Exact Nightly Coupling and Compile-Time Toolchain Embedding

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, `charon/rust-toolchain` (blob `3c98116ae62afb83263fa1654037badaf569e1c1`, pointed to by the repository-root `rust-toolchain` blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`) specifies:

- `channel = "nightly"` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`);
- `components = ["rustc-dev", "llvm-tools-preview", "rust-src", "miri"]`;
- `targets`: seven explicit target triples across Linux, macOS, Windows, and bare-metal targets.

In `charon/src/bin/charon/toolchain.rs` (blob `b35d1d0236cd7e1c5f68ad5b80b3371b82f2e784`), the outer `charon` binary embeds that crate-root `charon/rust-toolchain` file at compile time as `static PINNED_TOOLCHAIN: &str` via `include_str!` (traversing three parent directories from `charon/src/bin/charon/toolchain.rs` to `charon/rust-toolchain`).

`get_pinned_toolchain` parses `PINNED_TOOLCHAIN` at runtime rather than reading an on-disk `rust-toolchain` file next to the executable. Although `docs/usage.md` (blob `8731e44a3caa5ca3fc54c001ce2579b1a3ad4bde`) still mentions the stale filename `rust-toolchain.template`, the `include_str!` path in `toolchain.rs` is the authoritative compiler pin.

The coupling to `nightly` is architectural:

- `charon/src/bin/charon-driver/main.rs` (blob `ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`) enables `#![feature(rustc_private)]` and imports internal compiler crates (`rustc_driver`, `rustc_middle`, `rustc_hir`, `rustc_interface`, `rustc_mir_build`, `rustc_session`, `rustc_span`, `rustc_target`).
- `charon/Cargo.toml` (blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`) documents that `charon-driver` dynamically links `librustc_driver` and other `rustc` shared libraries and instructs callers not to invoke `charon-driver` directly.
- By contrast, the library target `charon_lib` enables its `rustc` feature by default (which pulls in rustc-facing trait elaboration), but `charon/Cargo.toml` documents that `charon-lib` can be compiled with `--no-default-features` on a stable Rust toolchain by consumers that only deserialize or manipulate exported ULLBC/LLBC (`CrateData`).

Basis: `source` (`charon/rust-toolchain`, `rust-toolchain`, `charon/src/bin/charon/toolchain.rs`, `charon/src/bin/charon-driver/main.rs`, `charon/Cargo.toml`) and `documentation` (`docs/usage.md`, `README.md` blob `6470a71c857dcb64be248cdb5dfe67576d914c99`).

#### 1.2 `rustup` Provisioning Path vs. `CHARON_TOOLCHAIN_IS_IN_PATH` Trusted-Environment Path

`toolchain.rs` implements two distinct execution paths inside `in_toolchain(program)`:

| Provisioning Mode | Trigger Condition | Command Construction & Environment | Validation & Limitations |
| --- | --- | --- | --- |
| Ordinary `rustup` mode | `CHARON_TOOLCHAIN_IS_IN_PATH` unset | Runs `rustup run nightly <program>` (plus `RUSTUP_WINDOWS_PATH_ADD_BIN=1` on Windows, citing Charon issue `#588` and `rustup` issue `#3825` so the `rustc` driver DLL directory is on `PATH`). | `Toolchain::is_installed` runs `rustup run <channel> rustc --version`. If that fails, `Toolchain::install` runs `rustup install <channel>` and `rustup component add --toolchain <channel> <component>` for each component. However: (1) `is_installed` has an explicit `FIXME: check if the right components are installed`—if the channel exists without `rustc-dev`, `is_installed` returns `true`; (2) `Toolchain` deserializes only `channel` and `components`, ignoring `targets`, so `rustup target add` is never run; (3) `Toolchain::install` checks only spawn/wait errors on `rustup` subcommands, not `ExitStatus::success()`. |
| Nix / trusted-`PATH` mode | `CHARON_TOOLCHAIN_IS_IN_PATH` set | Runs `Command::new(program)` directly from `PATH` without invoking `rustup`. In Charon's `flake.nix` (blob `844a2ca996e86acb053bbecd52ff251134341da8`) and `nix/charon.nix`, `rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain` honors the full `rust-toolchain` file (including `targets`), sets `CHARON_TOOLCHAIN_IS_IN_PATH=1`, prepends toolchain binaries to `PATH`, sets library search paths, and adds an rpath on macOS. | Performs **no runtime version comparison** between the `rustc` on `PATH` and `PINNED_TOOLCHAIN`. `get_rustc_version` in `charon/src/bin/charon/main.rs` runs the driver command only to extract the host triple (panicking with `"failed to determine underlying rustc version of Charon"` on failure) without checking the compiler commit or release string against `nightly`. |

At `a535e914f74db4fd9e6be7048f4233270d8945c0`, the CLI provides `charon toolchain-path` (tested in `charon/tests/cli.rs`), which executes `rustc --print=sysroot` via `in_toolchain` and prints the effective sysroot, but there is no `toolchain-version` subcommand at this pin. Historical issue `AeneasVerif/charon#588` ("dynamic librustc_driver path is not set by charon") corroborates why invoking `charon-driver` outside the wrapper environment fails to locate `librustc_driver`.

#### 1.3 Anneal's Trusted-`PATH` Wiring and the Same-Date `nightly-2026.06.03` Tag Split

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

1. `anneal/flake.nix` sets `rustDate = "2026-05-31"`, builds a managed Rust sysroot from that exact nightly, and bundles it alongside the Aeneas `nightly-2026.06.03` release archive (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, which supplies `aeneas/bin/charon` and `aeneas/bin/charon-driver` built from `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`).
2. `Toolchain::command(Tool::Charon)` in `anneal/src/setup.rs` invokes `aeneas/bin/charon`, clears the inherited environment, sets `CHARON_TOOLCHAIN_IS_IN_PATH=1`, prepends the managed `rust/bin` directory to `PATH` (retaining host tools such as the linker after it), and sets `LD_LIBRARY_PATH` or `DYLD_LIBRARY_PATH` to the managed Rust library directory.
3. By contrast, Charon's own `nightly-2026.06.03` Git tag resolves to `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (15 commits after `a535e914f74db4fd9e6be7048f4233270d8945c0`), where `charon/rust-toolchain` pins `nightly` instead of `nightly`. Because live Anneal source does not call the `charon_lib` crate locked to `0c91ca1a...` in `anneal/Cargo.lock`, Anneal's runtime compiler requirement is governed by Aeneas's `charon-pin` (`a535e914...` -> `nightly`), not by the same-date Charon tag.

Basis: `source` (`charon/src/bin/charon/toolchain.rs`, `charon/src/bin/charon/main.rs`, `charon/src/bin/charon/cli.rs`, `flake.nix`, `anneal/flake.nix`, `anneal/src/setup.rs`, `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1/charon/rust-toolchain`) and `derived` alignment conclusion.

---

### 2. CLI Invocation Modes, Argument Channels, Wrapper Classification, and Output Serialization

#### 2.1 Public Subcommands and Compiler Orchestration (`charon cargo` vs. `charon rustc`)

`charon/src/bin/charon/cli.rs` (blob `3580a74c6079079510aba318949810bc1a95a15f`) and `charon/src/bin/charon/main.rs` (blob `b4460ce4cd3baa32308718e79b6e194860b042a6`) define six top-level subcommands:

- `charon cargo`: delegates unit-graph construction and `rustc` command-line synthesis to `cargo build` (`translate_with_cargo`).
- `charon rustc`: bypasses Cargo and invokes `charon-driver` directly (`translate_without_cargo`).
- `charon ui_test` / `ui-test`: test-harness command that constructs a `charon rustc`-style invocation from source-file directives.
- `charon pretty-print FILE --format ...`: deserializes an existing `.llbc` / `.ullbc` / `.postcard` file (`charon/src/export.rs` blob `d5428958eb870f9f8531a8d193385c6be782338a`) and pretty-prints `CrateData` without launching Cargo or `rustc` (enforcing exact `CharonVersion` equality).
- `charon toolchain-path`: prints the `rustc --print=sysroot` path selected by `in_toolchain`.
- `charon version`: prints `0.1.210`.

| Dimension | `charon cargo [CHARON_OPTS] -- [CARGO_ARGS]` | `charon rustc [CHARON_OPTS] -- [RUSTC_ARGS]` |
| --- | --- | --- |
| Outer orchestrator (`main.rs`) | `translate_with_cargo` | `translate_without_cargo` |
| `./Cargo.toml` `[package.metadata.charon]` (`toml_config.rs` blob `7bf93adcd601d300180b89315190591643de5e8e`) | Read and merged into `CliOpts` before validation (`rustc.flags`, inclusion/opacity/start roots; CLI scalar options take precedence over metadata). | **Not read**; `[package.metadata.charon]` in `./Cargo.toml` is ignored. |
| Trailing arguments after `--` | Appended to the `cargo build` command line (e.g., `--features`, `--package`, `--bin`, `--lib`). | Appended directly to `CliOpts.rustc_args`. |
| `--rustc-arg <FLAG>` (`CliOpts.rustc_args` in `options.rs` blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`) | Serialized into `CHARON_ARGS` and appended by `charon-driver` to selected target-unit `rustc` invocations. | Serialized into `CHARON_ARGS` (alongside trailing args) and appended by `charon-driver` to the `rustc` invocation. |
| Explicit `--target` injection | If no `--target` is present in Cargo args, queries pinned `rustc` host triple and appends `--target <rustc-host>` to `cargo build`. | If no `--target` is present in `rustc` args, queries pinned `rustc` host triple and appends `--target <rustc-host>` to the driver invocation. |
| Process launch & environment | Launches pinned `cargo build` with `RUSTC_WRAPPER=<sibling charon-driver>`, `CHARON_USING_CARGO=1`, `CARGO_PRIMARY_PACKAGE` removed from outer env, and `CHARON_ARGS=<JSON CliOpts>`. | Launches `<sibling charon-driver>` (with `rustc` inserted as argv[1] per wrapper convention) and `CHARON_ARGS=<JSON CliOpts>`. |

#### 2.2 `charon-driver` Wrapped-Unit Classification and `CHARON_ARGS` Protocol

When Cargo invokes `RUSTC_WRAPPER` (`charon/src/bin/charon-driver/driver.rs` blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`), `charon-driver` classifies each compiler process using two conditions:

1. **Workspace dependency vs. primary package**: When `CHARON_USING_CARGO` is set in the environment, the absence of `CARGO_PRIMARY_PACKAGE` marks the invocation as a non-primary dependency build.
2. **Target-side vs. host-side compilation**: The presence of a `--target` flag in the `rustc` arguments marks the invocation as target-side; host-side build scripts (`build.rs`) and procedural-macro crates compiled for the host lack `--target` (which is why outer `charon` always forces `--target <rustc-host>` on native builds).

Only an invocation that is **both non-dependency (`CARGO_PRIMARY_PACKAGE` present, or `CHARON_USING_CARGO` absent) and target-side (`--target` present)** runs Charon's `CharonCallbacks` translation. All other wrapped `rustc` invocations run `RunCompilerNormallyCallbacks` (with `always_encode_mir = true` so compiled dependencies emit MIR into `.rmeta`). For a selected translation unit, `charon-driver` requires `CHARON_ARGS` (emitting an error instructing the user not to call `charon-driver` directly if `CHARON_ARGS` is missing), deserializes `CliOpts`, applies any `--preset`, configures error policy, appends `CliOpts.rustc_args`, and runs `rustc_driver::run_compiler`. The outer `charon` process propagates the child `ExitStatus` numeric exit code (`main.rs`).

#### 2.3 Output File Naming, Formats (`json`, `postcard`, `all`), and Partial Serialization (`has_errors`)

In `charon/src/options.rs` (`CliOpts::targets`) and `charon/src/export.rs` (`CrateData::serialize_to_file`):

- **Default naming (when `--dest-file` is omitted)**: Starts from `<dest_dir>/<crate_name>` (where `dest_dir` defaults to `.`) and appends the representation and encoding extension:
  - LLBC JSON (default): `<dest_dir>/<crate_name>.llbc`
  - ULLBC JSON (`--ullbc`): `<dest_dir>/<crate_name>.ullbc`
  - LLBC Postcard (`--format postcard`): `<dest_dir>/<crate_name>.llbc.postcard`
  - ULLBC Postcard (`--ullbc --format postcard`): `<dest_dir>/<crate_name>.ullbc.postcard`
- **Explicit `--dest-file PATH`**:
  - With a single format (default JSON or explicit `--format json` / `--format postcard`), writes to `PATH` verbatim without appending an extension.
  - With `--format all`, treats `PATH` (or `<dest_dir>/<crate_name>` if `--dest-file` is omitted) as a path base and appends both JSON and Postcard extensions.
- **`--no-serialize`**: Produces an empty output-target list and is rejected at option validation if combined with `--format`.
- **Directory creation and `has_errors`**: `serialize_to_file` creates parent directories if needed, creates/truncates the output file, writes the serialized `CrateData`, and canonicalizes the path for logging. If translation continued after errors, `CrateData.has_errors` is `true` and Charon's log message labels the serialized file as partial.

Basis: `source` (`charon/src/bin/charon/cli.rs`, `charon/src/bin/charon/main.rs`, `charon/src/bin/charon-driver/driver.rs`, `charon/src/options.rs`, `charon/src/bin/charon/toml_config.rs`, `charon/src/export.rs`) and `documentation` (`docs/usage.md`).

---

### 3. Dependency Extraction, MIR Availability, and Whole-Crate Source Coverage

#### 3.1 Semantic Reference Closure and Cargo Source-Kind Invariance

In `charon/src/bin/charon-driver/translate/translate_crate.rs` (blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`) and `translate_items.rs` (blob `7964644be017856c6d165545a67bd6ef06e0c85c`):

- **Default structural root (`crate`)**: When no `--start-from*` flag is passed, `TranslateOptions::new` inserts `StartFrom::Pattern { pattern: "crate", strict: true }`. Because `crate` defaults to `ItemOpacity::Transparent`, `enqueue_module_item` and `register_module` structurally traverse the current crate's transparent module hierarchy and inherent `impl` blocks—even for local functions never called at runtime—and also walk nested HIR items inside transparent item bodies (`charon/tests/ui/filtering/inner-items.rs` blob `bc5779ce4a02f3b53c381178e869e2a7584e4a12`, `.out` blob `1f17ef7a5a962eaccbdf7b5f4acc28cc5ea15dfb`).
- **Demand-driven foreign inclusion (`register_and_enqueue`)**: Cargo dependencies (`--extern` crates) are **not** traversed from their crate roots by default (`charon/tests/cargo/dependencies/src/main.rs` blob `ab7719b680082503d0bc6df9079fe71cff9f6461`, `Cargo.toml` blob `4fc7413db8afca5528ce3a2b53d6e0b54758d505`). Instead, when translating a reached item's signature, body, type, trait clause, `impl` relationship, constant, global, associated item, vtable, or drop glue encounters a nonlocal `DefId`, `register_and_enqueue` assigns a Charon item ID and pushes its `TransItemSource` onto `items_to_translate`. Unused dependency crates and unreferenced items in used dependency crates never enter the queue unless explicitly selected via `--start-from`.
- **Invariance across Cargo dependency source kinds**: In `charon/src/bin/charon-driver/translate/translate_meta.rs` (blob `187a703dff83687f369f1903c6646aabdff259d3`) and `charon/src/ast/meta.rs` (blob `7a80a92ea1b3f3eaff1758554001e32019473237`), `ItemMeta.is_local` is a boolean derived solely from `rustc` crate locality (`DefId::is_local()`). Although file metadata normalizes paths under the Rust sysroot and Cargo home and records the crate name, Charon's reachability and opacity logic has no branch on whether an external crate originated from `crates.io`, a `[dependencies]` `path`, a `git` repository, or the sysroot.

#### 3.2 `always_encode_mir` vs. Prebuilt Standard-Library MIR Availability

In `charon/src/bin/charon-driver/driver.rs` (`3f90a7a3...`) and `charon/src/bin/charon-driver/translate/get_mir.rs` (blob `a1cd9ba131a1362dda55e85c25f29f4a9e28df69`):

- Even if `--include` or `--extract-opaque-bodies` requests `ItemOpacity::Transparent` for a foreign function, Charon can translate its body only if `rustc` exposes MIR for that `DefId` (`get_mir.rs` returns `None` when nonlocal MIR is absent).
- For workspace and external dependencies compiled by Cargo under `charon-driver`, the driver sets `-Zalways-encode-mir` (`always_encode_mir = true`), so their compiled metadata retains optimized MIR for ordinary nonlocal functions (and CTFE MIR for constants, statics, and `const fn`).
- However, `get_mir.rs` explicitly notes that `always_encode_mir` does not apply retroactively to the prebuilt Rust standard library (`core`, `alloc`, `std`): standard-library MIR is available only where prebuilt `.rmeta` already encodes it (such as generic, inlineable, or `const` items), not for arbitrary non-generic standard-library functions.

#### 3.3 Preprocessing, Macro/Build-Script Boundaries, and MIR Reachability

Because `CharonCallbacks` runs in `after_expansion` and extracts promoted MIR by default:

- **`#[cfg(...)]`-excluded code**: Stripped by `rustc` before `after_expansion`; default whole-crate coverage covers only the active target/feature/`cfg` configuration.
- **Procedural macros and `build.rs`**: A proc-macro crate and a `build.rs` script are host-side compilation units compiled normally by `RunCompilerNormallyCallbacks`; their host implementation code is not part of the target crate's LLBC. Conversely, target-crate Rust syntax produced by procedural-macro expansion or included from `OUT_DIR` (e.g., via `include!`) is parsed into the target crate before `after_expansion` and is covered identically to handwritten target Rust. Non-Rust build-script outputs (native archives, linker flags, environment variables) never become MIR.
- **Intra-function MIR block reachability**: Both `rustc` (before promoted MIR) and Charon (traversing from `START_BLOCK` and pruning dead blocks during transformations) drop disconnected basic blocks, so an item's presence in LLBC does not mean unreachable syntactic branches survived into its body.

Basis: `source` (`translate_crate.rs`, `translate_items.rs`, `get_mir.rs`, `driver.rs`, `resolve_path.rs` blob `b091bf23f897cee6b84e0136b41426a7de9d91f2`, `translate_meta.rs`, `ast/meta.rs`, `options.rs`), `documentation` (`docs/what_charon_translates.md` blob `780949ef1304a89e34c87b04958d65dbc3bf0810`), and `execution` (checked-in fixtures `charon/tests/cargo/dependencies/` and `charon/tests/ui/filtering/inner-items.rs`).

---

### 4. Entry-Point Selection (`--start-from*`), Pattern Resolution, and Two-Stage Reachability

#### 4.1 Entry-Point Selector Variants and Semantics

`charon/src/options.rs` (`f08f8bae...`), `charon/src/bin/charon-driver/translate/translate_crate.rs` (`53536c6d...`), and `charon/tests/help-output.txt` (blob `dd724b5aa48efaee9a36fb29159a9956d31e4a9b`) define four CLI start-selection mechanisms, all of which populate `TranslateOptions.start_from: Vec<StartFrom>` (multiple selectors form a single union before queue exploration):

| CLI Flag | `StartFrom` Variant | Resolution & Error Semantics | Module & Visibility Handling |
| --- | --- | --- | --- |
| *(none supplied)* | `StartFrom::Pattern { pattern: "crate", strict: true }` | Resolves local crate root module (`crate`). | `crate` is `Transparent` by default, so module traversal enqueues all top-level items and transparent submodules. |
| `--start-from <PAT>[,<PAT>...]` (repeatable & comma-delimited) | `StartFrom::Pattern { pattern, strict: true }` | Parsed via `NamePattern::parse` (`name_matcher/parser.rs` blob `fc5f292ba4f7038190c168070f5a3bf40d1f9014`) and resolved via `def_path_def_ids` (`resolve_path.rs`). Parse errors or empty resolution at a path prefix abort translation before the main work queue runs (`start_from_errors.rs` blob `aecac45c05b58c3b521a19e0eaa2938a848c9779`, `.out` blob `86ed12614ddb23d6eaba12266dd71154b1d1cb31`). | Transparent module roots enqueue their direct contents; non-module roots enqueue only themselves and their semantic dependency closure (`start_from.rs` blob `7b1d8b98c4918c6b091c448caac660cf7ccfb6ca`, `.out` blob `d643755caf24befb41d0357ee1001b3f683505dd`; `comma-delimited-start-from.rs` blob `ae96633334ef5c48ada639ede7b548022964c4cb`, `.out` blob `899c645976adc5176126d402bd7b37372959df18`). |
| `--start-from-if-exists <PAT>` | `StartFrom::Pattern { pattern, strict: false }` | Uses `NamePattern::parse` (so malformed syntax like `std::iter:once` is still an option parse error), but suppresses missing-match resolution errors (`start-from-if-exists.rs` blob `d55041495823aa2b11f028cdd65cbb9059ecb295`, `.out` blob `a2b4de68cea3772348b2fb7e0758d1dd80aa8449`). | Same closure rules as `--start-from` for matched roots; carries a fail-open risk if used without checking which roots matched. |
| `--start-from-attribute[=<ATTR>]` (default `verify::start_from`) | `StartFrom::Attribute(attr)` | Scans `tcx.hir_crate_items(()).definitions()` and enqueues local definitions bearing `<ATTR>`. | **Explicitly skips modules**: annotating `#[verify::start_from]` on a module does nothing (`start_from_attribute.rs` blob `41000f22198cbd4086d4eb2614f354fa5197d81e`, `translate_meta.rs`). |
| `--start-from-pub` | `StartFrom::Pub` | Scans `tcx.hir_crate_items(()).definitions()` and enqueues local non-module definitions where `tcx`/hax visibility is `Some(true)` (`start_from_pub.rs` blob `7e22da0375df43d7a5871fb52223321320e3f4a2`, `.out` blob `85327d35d3bf512af881574ba52369148aa11bb8`). | **Skips modules** and tests item-level `pub` syntax rather than effective crate-level exported reachability (a `pub` item inside a private, non-reexported module is still selected). Upstream issue `AeneasVerif/charon#1270` documents a `0.1.210` case where `--start-from-pub` emitted a larger LLBC than default whole-crate extraction. |

#### 4.2 `resolve_path` Supported Forms, Rejection Boundaries, and High-Cardinality Constraints

In `charon/src/bin/charon-driver/translate/resolve_path.rs` (`b091bf23...`), `def_path_def_ids` resolves `NamePattern` roots against `rustc` crate and item tables:

- **Accepted pattern forms** (`start_from.rs` / `start_from.out` and `inner-items.rs`):
  - Local modules and items via `crate::...` or `<local_crate_name>::...` (`crate::module1`, `test_crate::module2`);
  - External/stdlib functions and trait or inherent methods (`std::iter::once`, `std::clone::Clone::clone_from`, `std::slice::Iter::as_slice`, `u32::wrapping_add`);
  - Glob path segments (`crate::*::do_translate_glob`, `crate::_::bar` reaching nested functions, closures, and functions inside anonymous consts);
  - Top-level trait-impl patterns with a named ADT self type or wildcard `_` self type (e.g., `{impl Trait for MyStruct}::method` or `{impl Trait for _}`).
- **Rejected pattern forms** (`start_from_errors.rs` / `start_from_errors.out`):
  - Malformed paths (`std::iter:once`);
  - Unrooted local paths (`module2` fails and suggests `crate::module2`);
  - Inherent impl patterns (`{impl Type}` fails with ``--start-from` does not support inherent impls`);
  - Trait-impl patterns with non-named self types (such as slices/references/tuples unless `_` is used);
  - Trait-impl patterns with trait generic arguments;
  - Impl patterns occurring anywhere after the first path element (`crate::module::{impl ...}`);
  - Missing methods beneath a resolved impl;
  - Associated type roots (`AssocTy` resolves in `resolve_path` but fails registration because `AssocTy` is not a valid translation root).
- **Scaling and CLI-length constraints**: `resolve_path.rs` explicitly comments that `def_path_def_ids` is *"expensive and should be used sparingly"*, and `translate_crate.rs` invokes it separately for each `StartFrom::Pattern`. Moreover, `CliOpts` at `0.1.210` has no `--start-from-file` or response-file option (documented as a limitation in upstream feature request `AeneasVerif/charon#1020`).

#### 4.3 Late Post-Transformation Reachability Filtering (`reorder_decls.rs`)

Charon computes reachability a second time in `charon/src/transform/add_missing_info/reorder_decls.rs` (blob `256a7143194c31b22fb2809637d3991253f5d3ae`):

1. After MIR extraction and AST transformation passes (which can eliminate dead branches or render previously queued items unreachable), `compute_declarations_graph` seeds a fresh dependency graph using `StartFrom::matches(&item_meta)` (matching `NamePattern`, `item_meta` unknown attributes for `StartFrom::Attribute`, or `item_meta.attr_info.public` for `StartFrom::Pub`).
2. It traverses outgoing references in the transformed AST—treating `TraitDecl` specially by visiting generics, parent clauses, associated types/vtables, and method/const signatures without automatically traversing default method/const bodies merely because they belong to the trait declaration.
3. Inaccessible items are dropped, and final `ordered_decls` groups are emitted in topological SCC order.

Basis: `source` (`options.rs`, `translate_crate.rs`, `resolve_path.rs`, `translate_meta.rs`, `reorder_decls.rs`, `name_matcher/mod.rs` blob `17d2683ee660595a75a56104c61d3ab162f54a6c`, `name_matcher/parser.rs`), `documentation` (`docs/what_charon_translates.md`, `charon/tests/help-output.txt`), and `execution` (checked-in `.out` goldens in `charon/tests/ui/filtering/`).

---

### 5. Item Opacity (`ItemOpacity`), Precedence Rules, and Downstream Aeneas Model Separation

#### 5.1 The Four-Level `ItemOpacity` Lattice and Precedence Rules

`charon/src/ast/meta.rs` (`7a80a92e...`) and `charon/src/options.rs` (`f08f8bae...`) define `ItemOpacity` with derived ordering:

$$\texttt{Transparent} < \texttt{Foreign} < \texttt{Opaque} < \texttt{Invisible}$$

1. **Base name-pattern table (`TranslateOptions::new`)**:
   - Without `--extract-opaque-bodies`: initializes `_ -> Foreign` and `crate -> Transparent`.
   - With `--extract-opaque-bodies`: initializes `_ -> Transparent` and `crate -> Transparent`.
   - Appends `--include <PAT>` as `Transparent`, `--opaque <PAT>` as `Opaque`, and `--exclude <PAT>` (plus hidden marker-trait/allocator patterns) as `Invisible`.
2. **CLI pattern specificity and tie-breaking (`Pattern::compare` and `opacity_for_name`)**:
   - CLI patterns are prefix matchers (`NamePattern::matches_with_generics`): `--opaque crate::module` matches both `crate::module` and every descendant `crate::module::*` unless overridden by a longer pattern (such as `--include crate::module::_`).
   - Longer patterns outrank shorter patterns; at equal length, a concrete final path element outranks a glob (`_`/`*`); at equal specificity, `opacity_for_name` takes the maximum (`ItemOpacity::max`), erring toward greater opacity (`charon/tests/ui/filtering/opacity.rs` blob `2088ea043c3750201a3146aca9ed13e932a989b8`, `.out` blob `5429afa54236e0fc0d82e7aaaf348b5d6442b4f0`).
3. **Source attributes and `extern` items (`translate_item_meta` in `translate_meta.rs`)**:
   - Source annotations `#[charon::opaque]`, `#[aeneas::opaque]`, and `#[verify::opaque]` apply **only to the annotated item itself** (not prefix-inherited by children) and combine via `ItemOpacity::Opaque.max(name_opacity)`. Source `exclude` attributes combine via `ItemOpacity::Invisible.max(name_opacity)`. Consequently, `--include` or `--extract-opaque-bodies` **cannot** override a source `#[charon::opaque]` attribute.
   - Declarations inside Rust `extern { ... }` blocks (`is_extern_item(def)`) are unconditionally combined with `ItemOpacity::Opaque.max(name_opacity)` because they have no Rust MIR body to extract.

#### 5.2 Per-Construct Semantics Across `Transparent`, `Foreign`, `Opaque`, and `Invisible`

| Construct | `Transparent` | `Foreign` (default for external crates) | `Opaque` (`--opaque` or `#[charon::opaque]`) | `Invisible` (`--exclude`) |
| --- | --- | --- | --- | --- |
| Free functions & globals/consts | Translates signature and MIR body / initializer (`Body`). | Retains declaration and signature; body is omitted (`Body::Opaque`). | Retains declaration and signature (`fn f() = <opaque>`); body/initializer expression is omitted (`opacity.out`, `opaque_attribute.out` blob `9d25497b70aad9abb11206a8f1fa850a9497a430`). | Omitted completely before Hax definition lookup (unless an excluded trait identity must be referenced indirectly by an included impl). |
| Structs, enums, and unions (ADTs) | Translates all fields and variants. | **Translates public enums and structs whose fields are all public structurally**; hides types with private fields. | Emits `TypeDeclKind::Opaque` (`opaque type`); hides all fields and variants (`match_on_opaque_enum.rs` blob `2f38d8122c95c09bedfe8ca35f968212988456ec`, `.out` blob `33aef9c93a2462abc44966534a9dc36d97b57a7b` fails translation when matching on an opaque enum's discriminant). | Omitted completely. |
| Modules | Enqueues all direct items (`register_module`). | Does not traverse module contents; referenced items inside are queued individually. | Stops module traversal (`register_module` skips items). However, under source `#[charon::opaque]` on a module, a child function called from outside is still reached and translated with its own `Transparent` body (`opaque_attribute.rs` / `.out`), whereas CLI `--opaque crate::module` also prefix-matches children unless `--include crate::module::_` is passed. | Stops module traversal and excludes prefix-matched children under CLI `--exclude`. |
| Inherent `impl` blocks & methods | Enqueues methods when impl is transparent. | Methods reached by reference are body-opaque. | `PatElem::Impl` in `name_matcher/mod.rs` returns `false` for inherent `ImplElem::Ty`, so inherent impl blocks cannot be matched via `{impl Type}` CLI syntax; methods must be matched via wildcard paths such as `crate::module::_::method`. Annotating `#[charon::opaque]` on an impl block affects only the impl container, not each method's own opacity. | Same method-level matching requirement. |
| Trait declarations & trait `impl`s | Translates trait/impl structure and marks provided methods used. | Retains trait/impl structure; method bodies follow demand/opacity rules. | Preserves `TraitDecl` / `TraitImpl` structure (`opaque-trait.rs` blob `f2ed077aee2ec1ba55654728c5f205773de723b2`, `.out` blob `d6649d54d89eb6f59c2f81008e3f8627763d84fd`). CLI `{impl Trait for Type}` matches the rightmost trait impl in a path and acts as a prefix for its associated methods (`issue-114-opaque-bodies.rs` blob `6c6c094220e37b17a5a60d13307816757e6441a1`, `.out` blob `89ea5450be1172432a167391c5cdf7a03a99f6e0` makes `drop_in_place` under `{impl core::marker::Destruct for alloc::vec::Vec}` opaque). Individual trait methods can also carry `#[charon::opaque]` (`get_bool` in `opaque_attribute.out`). | Cannot filter a trait impl block itself directly without its associated items (`help-output.txt`). |

#### 5.3 Independence of Charon Opacity and Downstream Aeneas External Models

Marking an item `--opaque` or `#[charon::opaque]` in Charon removes its body or fields from LLBC (`Body::Opaque` / `TypeDeclKind::Opaque`), truncating dependency discovery through that body, **without** attaching any replacement specification or mathematical model. When Aeneas (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`) consumes the resulting LLBC, it independently matches Rust item names against its own builtin and external-model tables (`ExtractBuiltinLean.ml`). If an opaque declaration matches a registered Aeneas model, Aeneas redirects calls to that hand-written Lean definition; if no model is registered, Aeneas emits an external `axiom` declaration or `External.lean` template obligation. Consequently, Charon opacity (`--opaque`) and Aeneas model substitution are separate mechanisms with distinct trust obligations.

Basis: `source` (`ast/meta.rs`, `options.rs`, `translate_meta.rs`, `translate_items.rs`, `name_matcher/mod.rs`), `documentation` (`docs/what_charon_translates.md`), `execution` (checked-in fixtures `opacity.out`, `opaque_attribute.out`, `opaque-trait.out`, `match_on_opaque_enum.out`, `issue-114-opaque-bodies.out`), and `derived` pipeline boundary.

---

### 6. Multi-Target (`--targets`) Semantic Merge vs. Multi-Primary Cargo Output Collisions

#### 6.1 Explicit `--targets` Concurrent Fan-Out and Temporary File Isolation

When `CliOpts.targets` (`--targets=t1,t2,...`) is nonempty (`charon/src/bin/charon/main.rs` blob `b4460ce4...`), `translate_multi_target` creates one temporary directory for the invocation and spawns one scoped thread per target triple `i`:

- Each thread clones `CliOpts` and overrides staging fields:
  - Clears `targets` and `preset` (already applied by the outer command);
  - Sets `print_ullbc = false`, `print_llbc = false`, and `no_serialize = false`;
  - Sets `dest_file = Some(<tempdir>/target_<i>.<ext>)`, choosing `.llbc`/`.ullbc` JSON when outer format is default, `json`, or `all`, and `.postcard` only when outer format is explicitly `postcard`;
  - Forces `unbind_item_vars = false` (so item/variable IDs remain manipulable during merge) and `translate_all_methods = true` (so all targets start with comparable trait method sets before post-merge cleanup);
  - Appends `--target <triple>` to the child `cargo build` or `rustc` arguments.
- If any target child process exits nonzero or fails deserialization, `translate_multi_target` fails closed without producing a merged output.
- Each per-target `CrateData` must contain exactly one target-information entry, and `CrateMerger` sets the merged `has_errors` flag to the logical OR ($\bigvee_i \text{has\_errors}_i$) across all targets.

#### 6.2 `CrateMerger` and `ItemDeduplicator` Semantics (`charon/src/export/multi_target.rs`)

In `charon/src/export/multi_target.rs` (blob `a5e3516521e1c107db5800fd7e806b20c2c7e6df`), Charon merges the per-target `CrateData` structures in four stages:

1. **Initial target-qualified union (`CrateMerger`)**:
   - Uses the first target's `crate_name` as the merged `crate_name` (without asserting later targets share that crate name).
   - Deduplicates `File` entries strictly by `FileName` (`file_name_to_id` reuses an existing `FileId` whenever a later target registers the same `FileName`, without comparing file contents).
   - Remaps all declaration IDs and appends `PathElem::Target(target)` to every item's `Name`.
2. **Fixpoint grouping (`ItemDeduplicator`)**:
   - Strips the trailing `PathElem::Target(target)` to form a base `(Name, ItemId variant)` key, normalizing impl references through the current candidate remap to a fixpoint.
   - If a **single target** produces two items with the same normalized base key, `ItemDeduplicator` clears that group so ambiguous same-target collisions are never merged across targets.
3. **Normalization and `decide_merge` outcomes**:
   - `normalize_item` strips target suffixes, source spans, `item_meta.source_text`, selected `rustc_*` attributes, and type `layout` records before comparing items for equality:

| Multi-Target Group Shape | `decide_merge` Action | Merged LLBC Representation | Preserved Upstream Fixture (`charon/tests/`) |
| --- | --- | --- | --- |
| Identical normalized items across all targets where present (including a **1-element group** present on only one target, e.g., `#[cfg(target_arch = "aarch64")]`) | Deduplicate to canonical item | Strips `PathElem::Target` suffix, remaps all references to the canonical declaration ID, and drops duplicate copies. Note: a target-only item loses its target suffix and appears unsuffixed, so absence of a target suffix does **not** prove presence on all targets. | `ui/multi-target/multi-targets.rs` (`742988f7a12636bcf6e6eabd511ee7fa5e2dc60b`) & `.out` (`8fb3fa5bbffa38e6b2a7831c0feaee9d72de6d58`); `ui/multi-target/issue-1157-single-target-suffix.rs` (`35d99861e9856a5a3732e14903cba9b301aa6140`) & `.out` (`33dcc8854100ca9d2b2b6026f730ac17c90fbcd3`) |
| `TypeDecl` items equal after clearing `layout`, but with target-specific sizes/alignments (e.g., conditional `#[repr(align(...))]`) | Deduplicate type + merge layouts | Emits a single unsuffixed `TypeDecl` that accumulates the per-target layout records from every merged target copy. | `ui/multi-target/issue-1186-conditional-repr.rs` (`2f9c733ae9e02634613f72c06e99f2eee17f9433`) & `.out` (`998307cbf9f049cbe545c67855037da3b69684bb`) |
| `FunDecl` items with identical normalized name, generics, and signature, but differing bodies across targets | Create `TargetDispatch` façade | Retains target-suffixed `FunDecl`s marked `ItemSource::TargetDependent`, creates a synthetic unsuffixed `FunDecl` whose body is `Body::TargetDispatch` mapping each target triple to its target-specific `FunDeclId`, and remaps callers to the façade. | `ui/multi-target/multi-targets.out` (`8fb3fa5b...`); `ui/multi-target/issue-1158-partial-dedup.rs` (`3a0fdb6b60de08bd459bde6365da277c4a6ff123`) & `.out` (`423c51a2b61926f7961c2fb6284aa16968c837b9`); `cargo/multi-targets/src/lib.rs` (`f70ad5be41543da6343cb08756faadef1a43b0a5`) & `.out` (`ef98e938d5d6614f3e4ce62dee5593b554d7473f`) |
| Non-function items that differ after normalization, or `FunDecl` items whose signatures/generics differ across targets | `Skip` | Leaves each target-qualified declaration separate in the merged crate without synthesizing a union type or dispatcher. | `ui/multi-target/multi-targets.out` (`8fb3fa5b...`) |

4. **Post-merge cleanup**: Removes unused trait methods (reversing the staging `translate_all_methods = true` override) and runs `unbind_item_vars` if originally requested, then serializes the merged crate using the outer `--dest-file` / `--format` options.

#### 6.3 Multi-Primary Cargo Unit Write-Collision Hazard

In contrast to explicit `--targets` fan-out, a single `charon cargo` invocation exports one `CHARON_ARGS` value to `cargo build`, and `charon-driver` (`driver.rs` blob `3f90a7a3...`) translates **every** wrapped `rustc` process that has both `CARGO_PRIMARY_PACKAGE` and `--target`:

- When a single Cargo build graph compiles more than one target-side primary unit (for example, `--lib` plus a `--bin` sharing the same crate name, or multiple workspace primary packages when `--dest-file` is set), every selected `charon-driver` process inherits the same `CliOpts` output configuration.
- With an explicit `--dest-file`, all selected primary `charon-driver` processes write to that exact path. Without `--dest-file`, any two selected primary units that share a `rustc` crate name derive the same `<dest_dir>/<crate_name>.llbc` path.
- Even inside one target thread of `charon cargo --targets=...`, the thread assigns a single `target_<i>.llbc` path to its child `cargo build`, so multiple primary units inside that Cargo build still collide on `target_<i>.llbc` before `multi_target::merge` runs.
- Because `CrateData::serialize_to_file` (`export.rs`) opens and truncates the destination path directly without file locking, per-unit suffixes, or multi-unit aggregation, callers must ensure each `charon cargo` invocation selects at most one target-side primary unit (or distinct crate names without `--dest-file`).

Basis: `source` (`charon/src/bin/charon/main.rs`, `charon/src/export/multi_target.rs`, `charon/src/bin/charon-driver/driver.rs`, `charon/src/options.rs`, `charon/src/export.rs`), `execution` (preserved `.out` goldens in `charon/tests/ui/multi-target/` and `charon/tests/cargo/multi-targets.out`), and `derived` multi-primary write-collision analysis.

---

### 7. Within-Run Caching vs. Absence of Cross-Run Incremental LLBC State

As inventoried in [support/charon-incremental-capabilities-0-1-210/incremental-capabilities-matrix.json](support/charon-incremental-capabilities-0-1-210/incremental-capabilities-matrix.json) and [support/charon-incremental-capabilities-0-1-210/source-map.json](support/charon-incremental-capabilities-0-1-210/source-map.json), Charon `0.1.210` (`a535e914f74db4fd9e6be7048f4233270d8945c0`) separates within-run memoization from cross-run incrementality across six architectural layers:

| Layer / Mechanism | Pinned Source Location (`a535e914f74db4fd9e6be7048f4233270d8945c0`) | Lifetime & Scope | Incremental Capability vs. Limitation |
| --- | --- | --- | --- |
| 1. Compiler session & callback (`run_rustc_driver`, `CharonCallbacks`) | `charon/src/bin/charon-driver/driver.rs` (`3f90a7a31857aed462694066e5ffaa6e28b9dcfa`); `charon/src/bin/charon-driver/main.rs` (`ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`) | One `rustc_driver::run_compiler` call per selected crate; returns `Compilation::Stop` after `after_expansion` and exits after serialization. | `TyCtxt<'tcx>` is dropped before `translate_crate::translate` returns `TransformCtx`; no persistent compiler server or reusable `TyCtxt` survives across runs. |
| 2. Charon translation context (`TranslateCtx`) | `charon/src/bin/charon-driver/translate/translate_ctx.rs` (`e7e10ceb5c6d8ee1834ad2d11d021c92b1f5f6ec`); `translate_crate.rs` (`53536c6df6e241c9655840f6b1f8a4aca2113f90`) | Created fresh at the start of `translate_crate::translate`. | Memoizes `id_map`, `reverse_id_map`, `items_to_translate`, `processed` set, cached names/meta, `method_status`, and `file_to_id` **within one run**. Never deserializes or updates a prior `TranslatedCrate` or preserves numeric `ItemId`s as stable cross-edit patch keys. |
| 3. Hax translation caches (`hax::State`, `GlobalCache<'tcx>`, `ItemCache<'tcx>`) | `charon/src/bin/charon-driver/hax/state.rs` (`63fc236effb5b581582a8bf10f3c5934d857d6eb`); `TranslateCtx::hax_def_for_item` | Parameterized by `'tcx` and constructed via `State::new(...)` once per `translate_crate::translate` call. | Caches translated full definitions, types, item references, and trait proofs during a single `TyCtxt` session; dropped before returning `TransformCtx`. |
| 4. Root-driven graph pruning (`--start-from*`, `ItemOpacity`) | `charon/src/options.rs` (`f08f8bae08d7fb5f38773c0be038d925fe80cb4c`); `translate_crate.rs` | Per-invocation work-queue seed. | Prunes the subgraph of items translated during a fresh extraction; does **not** compute which roots were invalidated by an edit or merge newly translated items into an older `.llbc` file. |
| 5. Cargo & `rustc` build/query reuse (`charon cargo`) | `charon/src/bin/charon/main.rs` (`b4460ce4cd3baa32308718e79b6e194860b042a6`) | Delegated to `cargo build` and `rustc`. | Cargo can reuse compiled dependency artifacts, but `0.1.210` defines no Charon-level freshness fingerprint (whereas later `AeneasVerif/charon@67da6d3b8f31dfb0d003aee1596040f9efd7d27f` `charon/src/bin/charon/main.rs` blob `a5aa2c459ccde69502093dcf6988f2a5d314c7d3` explicitly adds a random `RUSTC_WORKSPACE_WRAPPER` fingerprint to force Cargo to rerun Charon every time). |
| 6. Output serialization (`CrateData::serialize_to_file`) | `charon/src/export.rs` (`d5428958eb870f9f8531a8d193385c6be782338a`) | Whole-file write per invocation. | Emits complete JSON or Postcard `CrateData` and requires exact `CharonVersion` equality on read; provides no base-snapshot hash, item delta record, tombstone list, or incremental patch protocol. |

Basis: `source` (`driver.rs`, `charon-driver/main.rs`, `translate_ctx.rs`, `translate_crate.rs`, `hax/state.rs`, `options.rs`, `export.rs`, `charon/main.rs`, `rust-toolchain` blob `4e348edab20d6bd5b195e758afe20f9d8258a3e1`, and later comparison `AeneasVerif/charon@67da6d3b8f31dfb0d003aee1596040f9efd7d27f/charon/src/bin/charon/main.rs` blob `a5aa2c459ccde69502093dcf6988f2a5d314c7d3`) and `derived` incremental architecture requirements preserved in [support/charon-incremental-capabilities-0-1-210/incremental-capabilities-matrix.json](support/charon-incremental-capabilities-0-1-210/incremental-capabilities-matrix.json).

## Boundaries

- **Not examined (no fresh execution)**: No fresh `charon`, `charon-driver`, `cargo`, `rustc`, `rustup`, Nix, or Aeneas processes were executed for this report. Checked-in `.out` files under `charon/tests/` are preserved upstream execution artifacts from `a535e914f74db4fd9e6be7048f4233270d8945c0`, not fresh reruns on this machine.
- **Unknown empirical quantities**:
  - Wall-clock throughput, memory growth, and OS argv-length failure points when passing hundreds or thousands of `--start-from` roots (`resolve_path.rs` notes `def_path_def_ids` is expensive, and `AeneasVerif/charon#1020` requests file-based root input).
  - Exact runtime failure symptoms (dynamic-linker error vs. startup panic vs. mid-translation crash) when `CHARON_TOOLCHAIN_IS_IN_PATH=1` is paired with a mismatched `rustc` nightly at `0.1.210`.
  - Concrete filesystem winner ordering or byte interleaving when a single `charon cargo` invocation spawns multiple target-side primary `rustc` units that write to the same `.llbc` destination path.
  - Warm vs. cold Cargo/rustc query-cache latency and exact conditions under which Cargo skips or reruns `charon-driver` at `0.1.210`.
- **Known not to apply**:
  - Charon's own `nightly-2026.06.03` tag (`0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, pinning `nightly`) does not govern the Charon binary bundled in Aeneas `nightly-2026.06.03` (`a535e914f74db4fd9e6be7048f4233270d8945c0`, pinning `nightly`).
  - Absence of a `PathElem::Target` suffix in a `multi_target::merge` output does not mean the item existed on all requested targets (1-element target-specific groups are deduplicated to unsuffixed items).
  - Marking an item `--opaque` or `#[charon::opaque]` in Charon does not supply a Lean/Aeneas model or prove that an Aeneas model is faithful to the omitted Rust body.
  - `[package.metadata.charon]` in `./Cargo.toml` is not read by `charon rustc`.
  - `Toolchain::install` in `toolchain.rs` does not install the `targets` array from `charon/rust-toolchain` and does not verify `rustc-dev` presence when `rustc --version` already succeeds.
- **Unsupported at `a535e914f74db4fd9e6be7048f4233270d8945c0`**:
  - Inherent impl patterns (`{impl Type}`) in `--start-from` or CLI name matching;
  - Trait-impl `--start-from` patterns with non-named self types (other than `_`), trait generic arguments, or `::{impl ...}` after the first path element;
  - Associated type (`AssocTy`) roots in `--start-from`;
  - Module roots in `--start-from-attribute` (`#[verify::start_from]` on a `mod` is ignored) and `--start-from-pub`;
  - Cross-run incremental LLBC state updates or delta serialization.

## Evidence

All primary Charon source and preserved test artifacts were inspected at `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`):

- **CLI, toolchain wrapper, and multi-target orchestration**:
  - `charon/rust-toolchain` (`3c98116ae62afb83263fa1654037badaf569e1c1`) and root `rust-toolchain` (`4e348edab20d6bd5b195e758afe20f9d8258a3e1`): `nightly` channel, components, and target list.
  - `charon/src/bin/charon/toolchain.rs` (`b35d1d0236cd7e1c5f68ad5b80b3371b82f2e784`): `PINNED_TOOLCHAIN` `include_str!`, `Toolchain::is_installed` (`FIXME`), `Toolchain::install` (omitting `targets` and exit-status checks), `in_toolchain`, `CHARON_TOOLCHAIN_IS_IN_PATH`, `RUSTUP_WINDOWS_PATH_ADD_BIN=1`, `driver_cmd`, and sysroot lookup.
  - `charon/src/bin/charon/cli.rs` (`3580a74c6079079510aba318949810bc1a95a15f`): top-level subcommands and trailing argument vectors.
  - `charon/src/bin/charon/main.rs` (`b4460ce4cd3baa32308718e79b6e194860b042a6`): `translate_with_cargo`, `translate_without_cargo`, `CHARON_ARGS`, `CHARON_USING_CARGO`, `CARGO_PRIMARY_PACKAGE` removal, `--target <rustc-host>` injection, `translate_multi_target` thread fan-out and temporary file staging, and exit-status propagation.
  - `charon/src/bin/charon/toml_config.rs` (`7bf93adcd601d300180b89315190591643de5e8e`): `[package.metadata.charon]` reader in Cargo mode.
  - `charon/src/options.rs` (`f08f8bae08d7fb5f38773c0be038d925fe80cb4c`): `CliOpts`, `TranslateOptions::new`, `StartFrom`, `opacity_for_name`, `--extract-opaque-bodies`, `--targets`, and output extension rules.
  - `charon/src/export.rs` (`d5428958eb870f9f8531a8d193385c6be782338a`) and `charon/src/export/multi_target.rs` (`a5e3516521e1c107db5800fd7e806b20c2c7e6df`): `CrateData::serialize_to_file`, exact-version check, `has_errors`, `CrateMerger`, `ItemDeduplicator`, `normalize_item`, `decide_merge`, and `TargetDispatch`.
  - `charon/Cargo.toml` (`8c9936202e7bdbdaaefbc19305363da1ab6c0084`), `flake.nix` (`844a2ca996e86acb053bbecd52ff251134341da8`), `docs/usage.md` (`8731e44a3caa5ca3fc54c001ce2579b1a3ad4bde`), `docs/what_charon_translates.md` (`780949ef1304a89e34c87b04958d65dbc3bf0810`), `README.md` (`6470a71c857dcb64be248cdb5dfe67576d914c99`), and `charon/tests/help-output.txt` (`dd724b5aa48efaee9a36fb29159a9956d31e4a9b`).
- **Driver, Hax state, reachability, name matcher, and opacity**:
  - `charon/src/bin/charon-driver/main.rs` (`ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`) and `charon/src/bin/charon-driver/driver.rs` (`3f90a7a31857aed462694066e5ffaa6e28b9dcfa`): `rustc_private` crate imports, `CharonCallbacks`, `RunCompilerNormallyCallbacks`, `always_encode_mir`, and target-side primary-unit classification.
  - `charon/src/bin/charon-driver/translate/translate_ctx.rs` (`e7e10ceb5c6d8ee1834ad2d11d021c92b1f5f6ec`), `translate_crate.rs` (`53536c6df6e241c9655840f6b1f8a4aca2113f90`), `translate_items.rs` (`7964644be017856c6d165545a67bd6ef06e0c85c`), `translate_meta.rs` (`187a703dff83687f369f1903c6646aabdff259d3`), `get_mir.rs` (`a1cd9ba131a1362dda55e85c25f29f4a9e28df69`), and `resolve_path.rs` (`b091bf23f897cee6b84e0136b41426a7de9d91f2`).
  - `charon/src/bin/charon-driver/hax/state.rs` (`63fc236effb5b581582a8bf10f3c5934d857d6eb`), `charon/src/ast/meta.rs` (`7a80a92ea1b3f3eaff1758554001e32019473237`), `charon/src/name_matcher/mod.rs` (`17d2683ee660595a75a56104c61d3ab162f54a6c`), `charon/src/name_matcher/parser.rs` (`fc5f292ba4f7038190c168070f5a3bf40d1f9014`), and `charon/src/transform/add_missing_info/reorder_decls.rs` (`256a7143194c31b22fb2809637d3991253f5d3ae`).
- **Preserved upstream test fixtures (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`)**:
  - Filtering, start-from, and opacity: `start_from.rs` (`7b1d8b98c4918c6b091c448caac660cf7ccfb6ca`) / `.out` (`d643755caf24befb41d0357ee1001b3f683505dd`), `start_from_errors.rs` (`aecac45c05b58c3b521a19e0eaa2938a848c9779`) / `.out` (`86ed12614ddb23d6eaba12266dd71154b1d1cb31`), `start-from-if-exists.rs` (`d55041495823aa2b11f028cdd65cbb9059ecb295`) / `.out` (`a2b4de68cea3772348b2fb7e0758d1dd80aa8449`), `start_from_pub.rs` (`7e22da0375df43d7a5871fb52223321320e3f4a2`) / `.out` (`85327d35d3bf512af881574ba52369148aa11bb8`), `start_from_attribute.rs` (`41000f22198cbd4086d4eb2614f354fa5197d81e`), `comma-delimited-start-from.rs` (`ae96633334ef5c48ada639ede7b548022964c4cb`) / `.out` (`899c645976adc5176126d402bd7b37372959df18`), `inner-items.rs` (`bc5779ce4a02f3b53c381178e869e2a7584e4a12`) / `.out` (`1f17ef7a5a962eaccbdf7b5f4acc28cc5ea15dfb`), `opacity.rs` (`2088ea043c3750201a3146aca9ed13e932a989b8`) / `.out` (`5429afa54236e0fc0d82e7aaaf348b5d6442b4f0`), `opaque_attribute.rs` (`d69ad26b35289697732534343604e4712abdacf4`) / `.out` (`9d25497b70aad9abb11206a8f1fa850a9497a430`), `opaque-trait.rs` (`f2ed077aee2ec1ba55654728c5f205773de723b2`) / `.out` (`d6649d54d89eb6f59c2f81008e3f8627763d84fd`), `match_on_opaque_enum.rs` (`2f38d8122c95c09bedfe8ca35f968212988456ec`) / `.out` (`33aef9c93a2462abc44966534a9dc36d97b57a7b`), and `issue-114-opaque-bodies.rs` (`6c6c094220e37b17a5a60d13307816757e6441a1`) / `.out` (`89ea5450be1172432a167391c5cdf7a03a99f6e0`).
  - Dependencies and multi-target: `charon/tests/cargo/dependencies/src/main.rs` (`ab7719b680082503d0bc6df9079fe71cff9f6461`) & `Cargo.toml` (`4fc7413db8afca5528ce3a2b53d6e0b54758d505`), `multi-targets.rs` (`742988f7a12636bcf6e6eabd511ee7fa5e2dc60b`) / `.out` (`8fb3fa5bbffa38e6b2a7831c0feaee9d72de6d58`), `issue-1157-single-target-suffix.rs` (`35d99861e9856a5a3732e14903cba9b301aa6140`) / `.out` (`33dcc8854100ca9d2b2b6026f730ac17c90fbcd3`), `issue-1158-partial-dedup.rs` (`3a0fdb6b60de08bd459bde6365da277c4a6ff123`) / `.out` (`423c51a2b61926f7961c2fb6284aa16968c837b9`), `issue-1186-conditional-repr.rs` (`2f9c733ae9e02634613f72c06e99f2eee17f9433`) / `.out` (`998307cbf9f049cbe545c67855037da3b69684bb`), and `charon/tests/cargo/multi-targets/src/lib.rs` (`f70ad5be41543da6343cb08756faadef1a43b0a5`) / `multi-targets.out` (`ef98e938d5d6614f3e4ce62dee5593b554d7473f`).
- **Staged support artifacts**:
  - [support/charon-incremental-capabilities-0-1-210/incremental-capabilities-matrix.json](support/charon-incremental-capabilities-0-1-210/incremental-capabilities-matrix.json)
  - [support/charon-incremental-capabilities-0-1-210/source-map.json](support/charon-incremental-capabilities-0-1-210/source-map.json)

## Revalidation

When upgrading or re-evaluating Charon for Anneal:

1. **Toolchain & wrapper diff (`toolchain.rs`, `charon/rust-toolchain`, `Cargo.toml`)**:
   - Resolve Aeneas's `charon-pin` to the exact Charon commit first (never infer from a same-date tag). Read `charon/rust-toolchain` and `include_str!` in `toolchain.rs`, check whether `Toolchain` now deserializes/installs `targets` or verifies `rustc-dev`, check `in_toolchain` and `CHARON_TOOLCHAIN_IS_IN_PATH` for version validation, and confirm `anneal/flake.nix` (`rustDate`) and `anneal/src/setup.rs` (`Tool::Charon`) supply the matching `rustc` nightly and library paths.
2. **CLI routing, wrapper classification, and multi-primary Cargo behavior (`cli.rs`, `main.rs`, `driver.rs`, `options.rs`, `toml_config.rs`, `export.rs`)**:
   - Diff subcommands, `--rustc-arg` vs. trailing `--` routing, `[package.metadata.charon]` merging, explicit `--target <rustc-host>` injection, `CARGO_PRIMARY_PACKAGE` + `--target` selection in `driver.rs`, and output extension rules.
   - Verify whether `charon cargo` still shares one `CHARON_ARGS` destination across multiple primary Cargo units or adds per-unit output staging/locking.
3. **Dependency coverage, `--start-from*`, and `ItemOpacity` (`translate_crate.rs`, `translate_items.rs`, `get_mir.rs`, `resolve_path.rs`, `name_matcher/`, `reorder_decls.rs`)**:
   - Diff `StartFrom` variants, `def_path_def_ids` restrictions (inherent impls, trait-impl position/generics/self-type rules, `AssocTy`), `ItemOpacity` precedence (`Pattern::compare`, `#[charon::opaque]` vs. CLI prefix matching, `is_extern_item`), `-Zalways-encode-mir` vs. prebuilt stdlib MIR availability, and post-pass reachability pruning in `reorder_decls.rs`.
   - On an execution-capable machine, run the filtering UI suite plus a scaling probe (1 to 2,000 `--start-from` roots via repeated and comma-delimited flags) and a multi-dependency Cargo workspace (registry, path, Git, unused crate, partially referenced crate, public vs. private-field foreign ADTs, `build.rs` `include!`, proc-macro output, and `cfg`-disabled code).
4. **Multi-target merge (`export/multi_target.rs`) and incremental state (`translate_ctx.rs`, `hax/state.rs`)**:
   - Check `translate_multi_target` temporary file staging, `CrateMerger` file-ID deduplication, `ItemDeduplicator` normalization, 1-element target-only suffix removal, `TargetDispatch` synthesis, and layout accumulation.
   - Check whether `TranslateCtx`/`hax::State` remain single-session or gain persistent snapshot/delta protocols, and whether `charon cargo` sets `RUSTC_WORKSPACE_WRAPPER` fingerprints that alter Cargo rebuild behavior.
