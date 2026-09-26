# Charon CLI invocation modes at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), the two compiler-facing public modes share one rustc-driver implementation but delegate different parts of compilation setup.

`charon cargo` delegates build-unit selection and each rustc command line to Cargo. Charon launches the pinned Cargo as `cargo build`, installs the sibling `charon-driver` as `RUSTC_WRAPPER`, transports Charon's own options through `CHARON_ARGS`, and marks the wrapper path with `CHARON_USING_CARGO`. Cargo then invokes the driver for both dependency/host work and selected target work. The driver compiles non-selected units normally and translates selected target-side primary-package units.

`charon rustc` bypasses Cargo. Charon launches the same `charon-driver` directly under the pinned toolchain and appends the user's rustc arguments. The caller therefore owns the rustc build context that Cargo would otherwise construct: crate input, dependency `--extern` arguments when needed, crate type/name, cfgs, and other compilation arguments. This changes orchestration, not the rustc callback/extraction architecture.

The command line has three distinct argument channels. Charon options populate `CliOpts`; `--rustc-arg` adds an extra rustc flag to the serialized Charon options and is appended by the driver; and arguments after the subcommand's trailing `--` are passed to the underlying tool—Cargo build arguments in `cargo` mode and rustc arguments in `rustc` mode. Only `cargo` mode also reads `[package.metadata.charon]` from `./Cargo.toml`.

Both compiler-facing modes force an explicit `--target` equal to the pinned compiler's host target when the caller supplied none. This is not merely an output-target default: Charon's driver uses presence of `--target` to distinguish target-side compilation from host-side build scripts and procedural macros.

Serialization is controlled independently of invocation mode. By default Charon writes JSON LLBC in the current directory using the translated crate name. `--ullbc` changes the representation/extension; `--format postcard` changes encoding; `--format all` writes both JSON and Postcard; `--dest-file` overrides the normal output path; and `--no-serialize` suppresses files. `pretty-print`, `toolchain-path`, and `version` are utility modes rather than Rust translation modes.

No fresh Charon, Cargo, or rustc execution was performed. This report establishes the exact source-defined command routing, option transport, and output path rules. It does not claim that every possible Cargo/rustc argument combination has been empirically exercised.

## Applicability

This report applies to:

- repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- package version `0.1.210`;
- the public `charon` binary, its sibling `charon-driver`, and the option/output machinery at that revision.

The companion `charon-toolchain-contract-0-1-210` publication intent covers how the required Rust toolchain is selected and provisioned. The existing architecture note under `charon-ullbc-llbc-schema-nightly-2026-06-03` covers the rustc callback and extraction boundary. This report focuses on the public invocation surface and how it reaches those components.

"Forwarded arguments" below means arguments accepted after the subcommand's trailing separator. `CliOpts.rustc_args`, populated by one or more `--rustc-arg` options or package metadata, is a separate Charon-controlled channel even though those strings eventually also reach rustc.

Multi-target translation uses these same modes once per requested target and then merges the resulting translated crates. The mechanics of cross-target merging are a separate #3720 subject and are not characterized fully here.

## Findings

### The public CLI has explicit translation and utility subcommands

The pinned CLI defines these top-level commands:

- `charon cargo`;
- `charon rustc`;
- `charon ui_test` / `ui-test`;
- `charon toolchain-path`;
- `charon pretty-print`;
- `charon version`.

`cargo` and `rustc` are the ordinary translation entry points. `ui_test` is test infrastructure that constructs a `charon rustc`-style invocation from source-file directives. `pretty-print` reads an existing serialized crate. `toolchain-path` prints the sysroot selected by Charon's toolchain wrapper. `version` prints Charon's package version.

There is therefore no need to infer mode from an input filename or current directory: the public translation mode is explicit in the subcommand.

Basis: pinned Charon **source**, `charon/src/bin/charon/cli.rs` and `main.rs`.

### `charon cargo` delegates the actual build invocation to `cargo build`

In Cargo mode, the outer executable:

1. validates Charon's options;
2. chooses the pinned Cargo through the toolchain wrapper;
3. sets `RUSTC_WRAPPER` to the sibling `charon-driver`;
4. sets `CHARON_USING_CARGO=1`;
5. removes inherited `CARGO_PRIMARY_PACKAGE`;
6. serializes `CliOpts` into `CHARON_ARGS`;
7. invokes `cargo build`;
8. appends the user's forwarded Cargo arguments.

This means a command such as:

```text
charon cargo [CHARON_OPTIONS] -- [CARGO_BUILD_OPTIONS]
```

does not ask Charon to reconstruct dependency paths or Cargo's unit graph. Cargo selects packages/targets/features/profiles and constructs rustc command lines, including dependency artifacts and `--extern` arguments.

Basis: pinned Charon **source** + upstream Charon **documentation**.

### `charon rustc` bypasses Cargo but uses the same driver

For `charon rustc`, the outer executable appends the forwarded rustc argument vector to `CliOpts.rustc_args`, validates the result, creates the sibling driver command in the pinned toolchain environment, serializes the options into `CHARON_ARGS`, and launches the driver.

Cargo does not participate. Consequently Charon does not discover a Cargo unit graph, compile dependencies, or synthesize the caller's dependency `--extern` paths in this mode. A self-contained `.rs` file can need little more than rustc's ordinary input arguments; a crate with external build context requires the caller to supply that context.

Both modes ultimately execute the same `charon-driver` rustc callbacks for a selected translation unit. The distinction is who supplies the rustc invocation.

Basis: pinned Charon **source**.

### Forwarded arguments and Charon's `--rustc-arg` are different channels

The subcommand parsers mark their underlying-tool argument vectors as trailing arguments. In Cargo mode, the trailing vector is appended to `cargo build`. In direct-rustc mode, the trailing vector is appended to `CliOpts.rustc_args`.

`CliOpts` separately exposes repeatable `--rustc-arg` values. The driver deserializes `CliOpts` from `CHARON_ARGS` and appends every `rustc_args` element to the compiler argument vector it received.

The practical consequence is mode-dependent:

- in `charon rustc`, both `--rustc-arg` and trailing rustc arguments reach the selected rustc invocation;
- in `charon cargo`, trailing arguments configure Cargo, while `--rustc-arg` is transported through `CHARON_ARGS` and added by Charon's driver to selected translated rustc invocations.

These channels are not interchangeable. A Cargo feature flag belongs in the Cargo argument channel, while a Charon-added `-Z...` compiler flag belongs in the rustc argument channel.

Basis: pinned Charon **source**.

### Cargo package metadata is consulted only in Cargo mode

Before launching Cargo, `translate_with_cargo` reads `./Cargo.toml` and looks for `[package.metadata.charon]`. The pinned metadata adapter supports selected Charon settings such as inclusion/opacity/start roots and `rustc.flags`.

The metadata is merged into command-line `CliOpts`. Boolean/list fields are combined according to the adapter, while the source comments state that CLI values take precedence where a scalar choice cannot be merged.

The direct `translate_without_cargo` path does not call this metadata reader. A `charon rustc` invocation therefore does not acquire Charon settings merely because the current directory contains a Cargo manifest with `[package.metadata.charon]`.

Basis: pinned Charon **source**, `main.rs` and `toml_config.rs`.

### Charon forces an explicit target even for an ordinary native build

Both Cargo and direct-rustc modes inspect their respective underlying argument vectors for `--target`. If none is present, the outer executable queries the pinned rustc host triple and adds:

```text
--target <rustc-host>
```

For Cargo mode this argument is added to `cargo build`; for direct-rustc mode it is added to the driver/rustc command.

The driver relies on this invariant. Under Cargo, host-side units such as build scripts and proc macros do not receive the target argument, while target-side units do. The driver uses the presence of `--target` together with `CARGO_PRIMARY_PACKAGE` to decide whether an invocation is a selected crate to translate or a crate to compile normally.

Thus removal or rewriting of the explicit-target behavior can change which Cargo invocations Charon translates.

Basis: pinned Charon **source**.

### Cargo mode wraps every Cargo rustc invocation but translates only selected target units

`RUSTC_WRAPPER` causes `charon-driver` to be placed in front of Cargo's rustc processes. The driver classifies a wrapped invocation as a workspace dependency when `CHARON_USING_CARGO` is set but `CARGO_PRIMARY_PACKAGE` is absent. It separately treats an invocation as target-side when a `--target` argument exists.

Only an invocation that is both non-dependency and target-side is translated. Other wrapped invocations call rustc with `RunCompilerNormallyCallbacks`.

This explains an important distinction in the public CLI: `charon cargo` can cause Charon's driver executable to participate in many Cargo compilation processes without producing a Charon translation for every one of them.

Basis: pinned Charon **source**, `charon-driver/driver.rs`.

### `CHARON_ARGS` is the public-wrapper-to-driver option protocol

The outer executable serializes `CliOpts` as JSON in the `CHARON_ARGS` environment variable. A selected `charon-driver` invocation requires this variable, deserializes it, applies the requested preset, configures error policy, appends extra rustc flags, and then runs the compiler with Charon callbacks.

If a selected driver invocation lacks `CHARON_ARGS`, the driver emits an error telling the caller not to invoke `charon-driver` directly and to use `charon rustc` instead.

This environment variable is therefore an internal process boundary in the pinned CLI architecture. It is not a serialized LLBC interface and should not be treated as a stable public protocol across Charon releases without revalidation.

Basis: pinned Charon **source**.

### `--dest-file`, format, and representation determine concrete output names

`CliOpts::targets` defines output file selection.

With serialization enabled, the default format is JSON. If no destination file is supplied, Charon starts from `<dest_dir>/<crate_name>`; `dest_dir` defaults to the current directory. It then appends the representation/format extension:

- LLBC JSON: `.llbc`;
- ULLBC JSON: `.ullbc`;
- LLBC Postcard: `.llbc.postcard`;
- ULLBC Postcard: `.ullbc.postcard`.

For a single explicit format, `--dest-file PATH` uses `PATH` exactly rather than appending the normal extension.

For `--format all`, Charon treats `--dest-file`, if present, as a path base and appends both appropriate JSON and Postcard extensions. Without `--dest-file`, it appends those extensions to the ordinary crate-name path base.

`--no-serialize` returns an empty output-target list and is rejected when combined with `--format`, because encoding is irrelevant when no file will be written.

Basis: pinned Charon **source**, `options.rs` and `export.rs`.

### Serialization creates parent directories and can label output partial

For each selected output path, Charon creates the parent directory if necessary, creates/truncates the file, writes JSON or Postcard, then canonicalizes the resulting path for its status message.

`CrateData` carries `has_errors`. If translation was allowed to continue after errors, Charon can still serialize a partial crate and its status log identifies the generated file as partial.

Successful file creation is therefore not by itself a completeness certificate. A consumer must also account for Charon's error policy and `has_errors`.

Basis: pinned Charon **source**.

### Pretty-printing is a serialized-data operation, not a Rust translation

`charon pretty-print FILE --format ...` calls Charon's deserializer for the selected encoding and prints the translated crate. It does not launch Cargo or rustc.

At this revision the serialized `CharonVersion` deserializer requires exact equality with the consuming Charon library's version. A pretty-print failure caused by an incompatible version is therefore an LLBC compatibility issue, not a compiler-invocation issue.

Basis: pinned Charon **source**.

### Multi-target mode reuses the selected invocation mode once per target

When Charon's own `--targets` list is nonempty, both `cargo` and `rustc` dispatch through `translate_multi_target`. The outer executable runs one translation per requested target, using a temporary per-target destination file and then merging the resulting `CrateData` values before writing the final requested output.

For Cargo, each per-target invocation adds `--target <target>` to the forwarded Cargo arguments. For direct rustc, it adds that target to the rustc arguments.

The temporary-output mechanism means ordinary multi-target operation does not ask several parallel target translations to write the same user `--dest-file`. The semantics of how target-specific translated crates are reconciled during `multi_target::merge` remain a separate subject.

Basis: pinned Charon **source**.

### Exit status propagates from the underlying translation path

Ordinary Cargo and direct-rustc translation return the child process's `ExitStatus` to the public `main`, which exits with the same numeric code when the status is unsuccessful. Charon-specific driver failures are converted by `charon-driver` into its own exit code before reaching that outer propagation.

This establishes process-level failure propagation, not a complete semantic failure taxonomy. The existing support/failure report covers partial output and fail-open concerns in more detail.

Basis: pinned Charon **source**.

## Boundaries

- No fresh Charon, Cargo, rustc, wrapper, filesystem, or multi-target execution was performed.
- The report records the exact source-defined argument routing and environment setup; it does not enumerate every argument accepted by the pinned Cargo or rustc.
- It does not claim that Charon's CLI syntax is stable across adjacent releases.
- It does not characterize shell quoting, platform-specific command-line encoding, response files, or non-UTF-8 argument handling.
- It does not establish empirical behavior when external Cargo wrappers such as `sccache` are configured.
- It does not characterize every `[package.metadata.charon]` parse/error corner case.
- It does not characterize the semantics of `multi_target::merge`; only the outer per-target invocation/output staging is covered.
- It does not claim that direct rustc mode and Cargo mode produce equivalent LLBC for a project. Their compilation subjects and supplied arguments can differ.
- It does not claim that a serialized file without `has_errors` is semantically complete for all Rust behavior; that depends on the separate Charon coverage/support boundary.
- The report does not choose which Charon mode Anneal should use.

## Evidence

All Charon evidence is pinned to:

```text
AeneasVerif/charon
a535e914f74db4fd9e6be7048f4233270d8945c0
version 0.1.210
```

Primary **source**:

- `charon/src/bin/charon/cli.rs`, blob `3580a74c6079079510aba318949810bc1a95a15f`: subcommands and trailing underlying-tool arguments.
- `charon/src/bin/charon/main.rs`, blob `b4460ce4cd3baa32308718e79b6e194860b042a6`: Cargo/direct-rustc command construction, environment transport, target injection, multi-target dispatch, utility commands, exit propagation.
- `charon/src/bin/charon-driver/driver.rs`, blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`: wrapped-unit classification, `CHARON_ARGS` decoding, extra rustc arguments, selected versus normal compilation.
- `charon/src/options.rs`, blob `f08f8bae08d7fb5f38773c0be038d925fe80cb4c`: option channels, validation, output target derivation, format/representation extensions.
- `charon/src/bin/charon/toml_config.rs`, blob `7bf93adcd601d300180b89315190591643de5e8e`: `[package.metadata.charon]` reading and merge behavior.
- `charon/src/export.rs`, blob `d5428958eb870f9f8531a8d193385c6be782338a`: output creation/serialization, partial-output logging, exact-version deserialization.
- `docs/usage.md`, blob `8731e44a3caa5ca3fc54c001ce2579b1a3ad4bde`: upstream **documentation** for Cargo-style usage and package metadata.

No evidence in this report is fresh **execution**.

## Revalidation

For another Charon revision, first diff `cli.rs`, outer `main.rs`, `driver.rs`, `options.rs`, `toml_config.rs`, and `export.rs`. The discriminating source checks are:

1. which translation subcommands exist;
2. where trailing arguments are routed;
3. how `CliOpts` reaches the driver;
4. how Cargo wrapper invocations are classified;
5. whether native builds still get an explicit target;
6. whether Cargo metadata is still Cargo-mode-only;
7. output-path and multi-format derivation;
8. whether multi-target still stages each target into an isolated temporary file.

On an execution-capable surface, use a tiny workspace with one target dependency, one build script, and one proc macro. Record process argv and the relevant environment for:

```text
charon cargo --no-serialize -- <one cargo build selector>
charon rustc --no-serialize -- <self-contained input.rs>
```

Then test one `--rustc-arg`, one trailing underlying-tool argument, package metadata versus a conflicting CLI setting, an omitted versus explicit target, each serialization format/representation, `--dest-file`, and a two-target invocation.

Preserve the exact Charon/Cargo/rustc revisions, command lines, environment, output files, exit statuses, and hashes. This checks concrete routing and output behavior at that revision; it does not establish semantic equivalence between Cargo and direct-rustc translation.
