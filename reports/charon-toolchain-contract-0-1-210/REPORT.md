# Charon toolchain contract at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), the rustc-facing Charon executable is deliberately coupled to one Rust nightly: `nightly-2026-05-31`. The repository records that channel in `charon/rust-toolchain`, and the `charon` wrapper embeds the complete file into its binary with `include_str!`. Normal non-Nix execution therefore does not ask the user's default `rustc` which version to use: it runs Cargo, rustc queries, and `charon-driver` through `rustup run nightly-2026-05-31 ...`.

The coupling is architectural, not merely a tested-version recommendation. `charon-driver` uses `#![feature(rustc_private)]`, imports many `rustc_*` crates directly, and dynamically links rustc libraries. The package manifest explicitly says the driver should not be invoked directly; callers should use `charon` so it can arrange the correct toolchain and runtime paths.

There are two materially different provisioning paths. The ordinary rustup path parses the embedded toolchain file, checks whether `rustup run <channel> rustc --version` succeeds, and attempts to install the channel and listed components when it does not. The Nix path sets `CHARON_TOOLCHAIN_IS_IN_PATH`, which tells Charon to skip rustup and run the requested program directly from `PATH`. That environment variable is therefore a trust assertion: the pinned source performs no runtime comparison between the `PATH` compiler and the embedded channel before using it.

The runtime rustup installer is also narrower than the checked-in toolchain file. `rust-toolchain` lists a channel, four components, and seven targets, but Charon's deserialized `Toolchain` struct contains only `channel` and `components`. Serde ignores the `targets` key, and `Toolchain::install` installs the channel plus components but never adds the listed targets. By contrast, the Nix flake constructs its Rust toolchain from the whole `rust-toolchain` file. The target list therefore participates in repository/Nix provisioning but is not enforced by Charon's own runtime installer.

Mismatch handling is mostly preventative rather than diagnostic. On the normal rustup path, the wrapper selects the named nightly, so an unrelated default toolchain is normally bypassed. If `CHARON_TOOLCHAIN_IS_IN_PATH` is set incorrectly, if required rustc-private libraries/components are absent, or if `charon-driver` is launched outside the wrapper environment, the pinned source does not contain a general version-compatibility check that turns this into a clean “wrong rustc revision” error. Failures can instead appear as process-launch, dynamic-linking, rustc-driver, or compiler-internal failures. No fresh mismatch experiment was performed, so this report does not claim one stable error message.

The non-rustc-facing `charon_lib` boundary is different. The Cargo feature `rustc` is default, but the manifest documents that `charon-lib` can be compiled with `--no-default-features` on stable Rust. Consumers that only deserialize/manipulate Charon's exported representation are therefore not subject to the same rustc-private toolchain requirement merely because the driver is.

## Applicability

This report applies to:

- repository: `AeneasVerif/charon`;
- revision: `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- package version: `0.1.210`;
- embedded Rust channel: `nightly-2026-05-31`.

It covers the top-level `charon` wrapper, sibling `charon-driver`, repository `rust-toolchain`, and the Nix flake's toolchain selection.

“Toolchain match” here means that the rustc-private driver is executed in the Rust environment Charon expects. This is stronger than matching only the human-readable release string: a rustc-private client is source/ABI-coupled to compiler internals, so the safest identity is the exact pinned channel/revision supplied by the repository.

The report does not infer continuity to neighboring Charon or Rust nightlies. It also does not claim that every Charon library consumer must use the pinned nightly; the `charon_lib` no-rustc feature boundary is explicitly separate.

## Findings

### The authoritative Charon pin is `nightly-2026-05-31`

`charon/rust-toolchain` contains:

- channel `nightly-2026-05-31`;
- components `rustc-dev`, `llvm-tools-preview`, `rust-src`, and `miri`;
- explicit target triples for several Linux, macOS, Windows, and bare-metal targets.

For the rustc-facing driver, the channel is the primary compiler identity exposed by the repository at this revision.

Basis: repository configuration **source**.

### The wrapper embeds the pin into the built executable

`toolchain.rs` defines:

`static PINNED_TOOLCHAIN: &str = include_str!("../../../rust-toolchain");`

`get_pinned_toolchain` parses that embedded text at runtime. The wrapper is therefore not consulting a mutable `rust-toolchain` file beside the installed executable when deciding which rustup channel to use.

This matters for provenance. The behavior of a built Charon wrapper is tied to the toolchain text compiled into that binary, even if another checkout later changes its `rust-toolchain` file.

Basis: Charon **source**.

### The driver requires rustc-private compiler internals

`charon-driver/main.rs` enables `rustc_private` and imports a large set of internal compiler crates, including `rustc_driver`, `rustc_middle`, `rustc_hir`, `rustc_interface`, `rustc_mir_build`, `rustc_session`, `rustc_span`, and `rustc_target`.

The package manifest says the resulting driver dynamically links rustc dylibs, including `librustc_driver`, and instructs users not to call the driver directly.

That establishes the reason for exact coupling: Charon is compiled against and executes inside rustc implementation interfaces rather than a stable public compiler API.

Basis: Charon **source** + package **documentation**.

### Ordinary execution selects the pinned channel independently of the user's rustup default

Outside the Nix override, `in_toolchain(program)` constructs:

`rustup run <pinned-channel> <program>`

The same helper is used for Cargo and for the driver environment. `driver_cmd` additionally points at the sibling `charon-driver`.

As a result, a machine whose rustup default is another stable or nightly channel does not normally cause Charon to use that default. The wrapper names the pinned channel explicitly.

This is a source-level selection rule. It does not establish that all system-level conflicts are impossible; executable lookup and environment configuration can still fail.

Basis: Charon **source**.

### Charon can auto-install the channel and listed components

Before using rustup, `Toolchain::is_installed` runs the pinned `rustc --version` under `rustup run`. If that command does not return success, `Toolchain::install` runs:

- `rustup install <channel>`;
- `rustup component add --toolchain <channel> <component>` for every listed component.

The intended ordinary path can therefore provision a missing toolchain without requiring the caller to install the nightly manually.

Basis: Charon **source**.

### The installed-state check does not verify components

The source contains an explicit FIXME in `Toolchain::is_installed`: “check if the right components are installed.”

The function currently asks only whether pinned `rustc --version` succeeds. If the channel exists but, for example, `rustc-dev` is missing, this check returns true and Charon does not enter its component-install loop.

Missing-component failure is consequently deferred to later use rather than diagnosed by the initial installed-state predicate.

Basis: Charon **source**.

### Runtime auto-install ignores the `targets` array

The checked-in `rust-toolchain` contains a `targets` array, but the deserialized Rust `Toolchain` type has only two fields:

- `channel`;
- `components`.

Serde's default behavior permits unrecognized fields, so the target list is not retained in that runtime struct. `Toolchain::install` likewise has no target-install loop.

Thus Charon's own rustup auto-provisioning does **not** implement the full declarative toolchain file. A target named in `rust-toolchain` is not thereby guaranteed to be installed by Charon's runtime helper.

Basis: Charon configuration + **source** comparison.

### The Nix path consumes the repository toolchain through a different mechanism

`flake.nix` builds:

`rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain`

and passes that toolchain through the Charon package build and development environments.

The default development shell sets `CHARON_TOOLCHAIN_IS_IN_PATH = 1` and obtains the toolchain through package inputs. The intended Nix realization therefore derives the `PATH` toolchain from the same repository file before telling the wrapper not to use rustup.

This is a separate realization of the same source pin; it does not make the environment-variable override self-validating.

Basis: Charon Nix **source**.

### `CHARON_TOOLCHAIN_IS_IN_PATH` disables runtime toolchain selection and verification

When `CHARON_TOOLCHAIN_IS_IN_PATH` is present, `in_toolchain` uses `Command::new(program)` directly instead of `rustup run <channel> program`.

The source comment says the variable is set by the Nix development/build environments, where the toolchain and dynamic linkage should already be correct. Charon itself does not compare `rustc -vV`, a commit hash, or a release string to the embedded channel before trusting this path.

Therefore the variable is an authority boundary:

- in the intended Nix environment, upstream construction supplies the matching toolchain;
- if another caller sets the variable while placing a different rustc environment on `PATH`, Charon does not detect that mismatch before launching the program.

Basis: Charon **source** + **derived** trust-boundary interpretation.

### Direct `charon-driver` invocation bypasses the supported setup boundary

The manifest says `charon-driver` should not be invoked directly. `driver_cmd` deliberately wraps it through `in_toolchain` to obtain the correct library paths and inserts `rustc` as the first argument because the driver expects Cargo's wrapper calling convention.

Historical upstream issue #588 records a concrete older-revision failure in which directly launching `charon-driver` could not locate its `librustc_driver` shared library until the appropriate toolchain library path was supplied. That historical observation is consistent with the current package comment and wrapper design, but it is not fresh execution evidence for this exact revision.

The durable rule is to treat `charon`, not `charon-driver`, as the supported executable boundary.

Basis: pinned Charon **source** + older preserved issue **execution evidence**, scoped historically.

### Charon does not expose a general “wrong rustc revision” gate before driver startup

At the pinned source, the normal path avoids mismatch by selecting the named rustup channel. The Nix override trusts `PATH`. There is no source check that obtains the active compiler commit and compares it with an embedded expected commit before invoking the driver.

`get_rustc_version` does query version metadata by running the driver command, but it uses the result primarily to obtain the host triple for target selection. Failure to obtain the metadata is converted into a panic with “failed to determine underlying rustc version of Charon”; the returned metadata is not compared against a separate expected version.

Consequently, mismatch diagnostics are incidental to the failing layer rather than one stable compatibility protocol.

Basis: Charon **source**.

### Toolchain installation failures are not all checked immediately

`Toolchain::install` obtains `ExitStatus` values from `rustup install` and `rustup component add`, but the pinned function does not test `status.success()` before continuing; it only propagates errors that prevent spawning/waiting for the command.

A rustup subcommand can therefore fail with a nonzero status without `Toolchain::install` itself returning an error. The subsequent Cargo/driver launch may then fail for the underlying missing channel/component.

This is an error-reporting limitation, not evidence that Charon can operate correctly without the required toolchain.

Basis: Charon **source**.

### Windows has an explicit rustup path workaround

When constructing `rustup run`, Charon sets `RUSTUP_WINDOWS_PATH_ADD_BIN=1` on Windows. The source cites Charon issue #588 and rustup issue #3825 as context and says this adds the rust driver DLL location to `PATH`.

This is further evidence that dynamic runtime linkage is part of the toolchain contract, not just selection of a `rustc` executable.

Basis: Charon **source**.

### The repository's usage documentation states that Charon builds the target with its nightly

`docs/usage.md` says Charon is compiled with nightly because implementing a rustc driver requires it and that Charon will build the analyzed crate with Rust nightly. The document points users to the pinned toolchain configuration for the specific version.

The exact filename mentioned in that prose has drifted (`rust-toolchain.template` versus the checked-in `charon/rust-toolchain` used by the source at this pin), so the executable source/configuration is stronger evidence for exact discovery than that filename reference.

Basis: upstream **documentation** + pinned repository **source**.

### `charon_lib` without rustc integration has a different toolchain requirement

The package's default `rustc` feature pulls in rustc-facing integration. The manifest explicitly says callers can pass `--no-default-features` to compile `charon-lib` on a stable toolchain.

This separates two compatibility questions:

- building/running `charon-driver` requires the pinned rustc-private environment;
- using the pure exported `charon_lib` API without the `rustc` feature need not inherit that exact nightly solely because of the driver.

Serialized-format version compatibility remains a separate report subject.

Basis: Charon package **source/documentation**.

## Boundaries

- No fresh `rustup`, Cargo, rustc, Charon, Nix, dynamic-linker, or cross-toolchain execution was performed.
- The report establishes source-defined selection and trust behavior. It does not enumerate the exact diagnostics produced by every missing-channel, missing-component, wrong-dylib, or wrong-rustc scenario.
- The source's `nightly-2026-05-31` channel is treated as the required compiler selection for this Charon revision. This report does not independently recover the exact rustc Git commit behind that channel from a fresh `rustc -vV` execution.
- The Nix flake is examined as source. No Nix derivation was instantiated on this surface.
- The runtime `Toolchain` struct ignores the toolchain file's `targets`; this report does not establish which targets happen to be preinstalled by rustup or the host environment.
- The historical dynamic-linker issue cited above applies to an older Charon revision and is used only as corroborating provenance for the wrapper boundary, not as an exact execution result for 0.1.210.
- System `PATH`, Cargo configuration, wrappers such as `sccache`, and platform dynamic-loader behavior can introduce additional failures not exhaustively analyzed here.
- This report does not characterize LLBC serialization compatibility between Charon versions.
- It does not prescribe how Anneal should package, install, or expose Charon; it preserves the upstream contract a packaging design must satisfy.

## Evidence

**Charon source:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

- `charon/rust-toolchain`, blob `3c98116ae62afb83263fa1654037badaf569e1c1`: channel, components, and target list.
- `charon/src/bin/charon/toolchain.rs`, blob `b35d1d0236cd7e1c5f68ad5b80b3371b82f2e784`: embedded toolchain text, rustup installed check, auto-install, `CHARON_TOOLCHAIN_IS_IN_PATH`, driver launch, sysroot discovery, Windows DLL-path workaround.
- `charon/src/bin/charon/main.rs`, blob `b4460ce4cd3baa32308718e79b6e194860b042a6`: Cargo/direct-rustc use of the toolchain wrapper, rustup requirement, version-metadata query and host-target selection.
- `charon/src/bin/charon-driver/main.rs`, blob `ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`: `rustc_private` driver executable and internal compiler crate imports.
- `charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`: driver dynamic-linking contract, supported wrapper boundary, default `rustc` feature, stable-compatible no-rustc library build.
- `flake.nix`, blob `844a2ca996e86acb053bbecd52ff251134341da8`: Nix toolchain derivation from `rust-toolchain`, package wiring, and `CHARON_TOOLCHAIN_IS_IN_PATH`.
- `docs/usage.md`, blob `8731e44a3caa5ca3fc54c001ce2579b1a3ad4bde`: documented nightly requirement and user-facing invocation model.
- `README.md`, blob `6470a71c857dcb64be248cdb5dfe67576d914c99`: rustup/Nix installation guidance.

**Historical upstream issue evidence:**

- `AeneasVerif/charon#588`, “dynamic librustc_driver path is not set by charon”: older-revision direct-driver dynamic-linking failure and manual library-path workaround. This is historical execution evidence, not execution at the pinned revision.

No evidence in this report is fresh **execution**.

## Revalidation

For another Charon revision, the cheapest source check is:

1. Read the revision's `charon/rust-toolchain`.
2. Check whether `toolchain.rs` still embeds that file and whether `Toolchain` now models channel, components, and targets.
3. Check `in_toolchain` for rustup versus environment-override behavior and any new version validation.
4. Check `Cargo.toml`/driver source for the rustc-private boundary.
5. Check the Nix flake or release packaging for how it establishes the toolchain before setting any “toolchain already present” override.
6. Diff error handling around rustup install/component/target commands.

On an execution-capable surface, use two controlled environments for the exact revision.

**Rustup path:**
- start with the pinned channel absent;
- run a trivial `charon rustc` input;
- preserve rustup commands/output;
- confirm the selected `rustc -vV` commit and required driver components;
- repeat with the channel installed but `rustc-dev` removed to observe the missing-component path.

**Override path:**
- construct one environment with the intended toolchain on `PATH` and `CHARON_TOOLCHAIN_IS_IN_PATH=1`;
- construct a control with a deliberately neighboring nightly on `PATH`;
- run the same trivial translation;
- preserve process exit, dynamic-link errors/panics, and `rustc -vV`.

Also test a target listed in `rust-toolchain` after allowing Charon's runtime auto-installer to provision a fresh rustup home. That specifically discriminates whether target installation behavior has changed.

These probes establish concrete mismatch diagnostics and provisioning behavior for that revision. They do not justify using a mismatched toolchain in production or establish semantic equivalence between neighboring rustc revisions.
