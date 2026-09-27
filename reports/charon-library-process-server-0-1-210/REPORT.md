# Charon’s library and process boundaries at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), Charon has two materially different integration surfaces:

- `charon_lib` is an in-process Rust library for LLBC/ULLBC data, transformations, formatting, options, and serialization/deserialization.
- Rust-source extraction is implemented in the `charon` and `charon-driver` executables. `charon` launches Cargo or `charon-driver`; `charon-driver` embeds rustc through callbacks, finishes one translation, serializes the result, and exits.

The pinned public `charon_lib` surface does not expose the rustc extraction driver as a library API. The pinned `charon` CLI also exposes no server or daemon subcommand and no request protocol. Thus a consumer can embed manipulation of an already-produced Charon AST, but the supported extraction path is batch/process-oriented.

This distinction matters for interactive tooling. Keeping a wrapper process alive would not, by itself, create persistent Charon compiler state: the current extraction path still starts Cargo/rustc work per translation request. A genuinely long-lived extraction service would need a new protocol plus either a refactoring of the binary-only rustc-driver machinery into an embeddable component or a server that owns and invokes that machinery. The pinned source does not define snapshot identity, cache invalidation, document versions, cancellation, or incremental request semantics for such a service.

This report does **not** conclude that repeated Charon invocations receive no benefit from Cargo or rustc caches. It characterizes the exposed integration and process boundaries, not performance or Charon’s separate incremental-capabilities question.

## Applicability

The findings apply to Charon 0.1.210 at commit `a535e914f74db4fd9e6be7048f4233270d8945c0`, the Charon revision pinned by Aeneas release `nightly-2026.06.03`.

“Library” means the public Rust crate named `charon_lib` in `charon/Cargo.toml` and exported from `charon/src/lib.rs`. “Extraction” means driving rustc over Rust source to construct Charon’s translated crate. “Server” means a long-lived request-serving interface whose process survives individual translations; it does not mean a caller-written wrapper that merely spawns the existing CLI once per request.

The report focuses on architecture exposed by the pinned source. It does not prescribe Anneal’s eventual Charon boundary. It also does not answer the separate #3720 subject “Charon incremental capabilities,” except where the absence of an exposed long-lived Charon state protocol is directly relevant.

## Findings

### `charon_lib` exposes the translated representation and post-extraction machinery

`charon/Cargo.toml` defines the library target as `charon_lib`. Its root publicly exposes AST modules, identifiers, errors, export/serialization, name matching, options, pretty-printing, and transformations. It also provides convenience functions for reading serialized LLBC into `TranslatedCrate`.

The manifest explicitly separates rustc-private support from the ordinary library use case: the default `rustc` feature is needed for `charon-driver`, while `charon-lib` can be compiled on stable with `--no-default-features`.

This makes `charon_lib` a useful embedded interface after extraction. A Rust consumer can keep a `TranslatedCrate` in memory, inspect or transform it, and avoid a second serialization boundary inside that consumer.

Basis: pinned **source** + upstream **documentation**.

### The rustc extraction driver is a binary target, not a public `charon_lib` module

The same manifest defines `charon-driver` as a separate binary and warns users not to invoke it directly. The library root does not export the driver module or `CharonCallbacks`; instead, its rustdoc comment points readers to the separately generated `charon_driver` documentation for those callbacks.

The extraction code lives under `charon/src/bin/charon-driver/`. `driver.rs` defines `run_rustc_driver` and `CharonCallbacks`; these are part of the binary crate’s source tree rather than modules declared by `charon/src/lib.rs`.

Accordingly, the pinned public library API does not provide a function such as “translate this Cargo project/Rust file with rustc and return `TranslatedCrate`.” Embedding LLBC manipulation and embedding Rust-source extraction are different integration problems at this revision.

Basis: pinned **source** + **derived** Rust target/module boundary.

### The supported Cargo path is an explicit subprocess pipeline

The `charon` executable describes and implements a Clippy-like wrapper topology. For `charon cargo`, it:

1. launches Cargo as a subprocess;
2. sets `RUSTC_WRAPPER` to `charon-driver`;
3. serializes Charon options into the `CHARON_ARGS` environment variable; and
4. waits for Cargo to exit.

Cargo then invokes `charon-driver` with rustc’s arguments for relevant crates. The driver decides whether an invocation is a selected target or a dependency/build-script/proc-macro compilation. Selected targets run rustc with Charon callbacks; other invocations compile normally.

For `charon rustc`, the wrapper bypasses Cargo but still launches `charon-driver` as a subprocess, passes options through `CHARON_ARGS`, and waits for it to exit.

The wrapper/driver boundary is therefore part of the pinned supported topology, not an incidental command example.

Basis: pinned **source**.

### One `charon-driver` process produces one finite translation result and exits

`charon-driver::run_charon` calls `driver::run_rustc_driver`. If the invocation is selected for Charon translation, the callback returns a `TransformCtx` and options after rustc has run. The driver then runs Charon’s post-processing transformations, wraps the result in `CrateData`, serializes it to the requested target file or files, and returns to `main`.

`main` converts the resulting status into warnings or an exit code. There is no event loop around multiple translation requests in this entry point.

The important boundary is not merely “Charon has a CLI.” The extraction-owned rustc state is scoped to a driver invocation. The exposed program flow reaches a serialized result and process termination rather than retaining compiler/translation state for a later request.

Basis: pinned **source**.

### The pinned CLI has no server/daemon command or request protocol

The `Charon` clap subcommand enum contains:

- `rustc`;
- `cargo`;
- `ui_test`;
- `toolchain-path`;
- `pretty-print`; and
- `version`.

The manifest’s executable targets are `charon`, `charon-driver`, and `generate-ml`. No server/daemon binary or server subcommand is exposed by these pinned entry points.

This is narrower than saying “no server could be built from Charon.” It establishes that the examined revision does not ship an extraction server as part of its supported CLI/target surface.

Basis: pinned **source**.

### A persistent wrapper would not automatically make extraction persistent

A caller can always build its own long-lived process around a command-line tool. If that wrapper invokes `charon cargo` or `charon rustc` for each request, however, the pinned Charon topology still creates new child processes and new rustc-driver invocations for those requests.

Therefore process persistence at the outermost layer and persistence of Charon/rustc translation state are separate properties. Reusing the same wrapper process does not, from the pinned source alone, establish reuse of an earlier `TransformCtx`, rustc `TyCtxt`, item queue, or translated crate.

Basis: pinned **source** + **derived** process-lifetime distinction.

### The current library/process split offers three different integration choices

The pinned architecture admits three distinct boundaries, each with different coupling:

1. **Batch CLI + serialized LLBC.** A consumer runs `charon` and reads the resulting LLBC. This keeps rustc-private extraction behind a process boundary and couples the consumer to Charon’s serialized representation.
2. **Batch extraction + in-process `charon_lib`.** A Rust consumer can deserialize once and then keep/manipulate `TranslatedCrate` in memory. This removes repeated serialization inside the consumer but does not remove the extraction process boundary.
3. **Refactored/embedded extraction.** A consumer could in principle reuse Charon’s driver machinery inside another Rust program, but the pinned repository does not expose that as a supported `charon_lib` API. Doing so would require depending on or refactoring the binary-only rustc integration and accepting its exact nightly/rustc-private coupling.

These are architecture facts, not a recommendation among the choices.

Basis: pinned **source** + **derived** interface comparison.

### The pinned interface has no Charon-level snapshot or invalidation contract

The process API communicates a translation request through command-line arguments, Cargo/rustc arguments, environment variables, filesystem inputs, and output files. The public AST library operates on values already in memory or loaded from files.

The examined entry points do not define server concepts such as:

- request IDs or sessions;
- source-document versions;
- a persistent project/workspace identity;
- invalidation of individual translated items after source edits;
- a generation number for cached `TranslatedCrate` state;
- cancellation of an in-flight translation request; or
- a protocol for reusing compiler state across requests.

A future interactive Charon service would therefore need to define these semantics rather than inherit them from an existing Charon server protocol at this pin.

Basis: pinned public entry-point **source** + **derived** absence from the exposed contract.

### This architecture does not answer whether repeated batch extraction is cheap

`charon cargo` deliberately delegates compilation orchestration to Cargo. Cargo and rustc have their own build and incremental mechanisms, and rustc arguments may carry incremental-cache paths. The batch Charon process model does not imply that all lower-layer work is recomputed from scratch.

Conversely, normal Cargo/rustc reuse would not itself provide an interactive Charon API or a stable Charon AST invalidation contract. The performance and semantic behavior of repeated edits therefore requires separate investigation and, where useful, execution.

Basis: pinned **source** + **derived** scope boundary.

## Boundaries

- **Not examined by execution:** no Charon process was run and no latency, memory, cache reuse, or concurrency measurement was performed.
- **Separate question:** this report does not determine how much work Cargo or rustc incremental compilation can reuse between repeated `charon cargo` invocations.
- **No impossibility claim:** absence of a pinned server entry point does not mean Charon cannot be refactored or wrapped into a server. It means no such supported extraction interface is present in the examined public targets/subcommands.
- **Library nuance:** `charon_lib` contains post-extraction code and can be built with its default rustc-related feature, but the pinned `lib.rs` does not publicly expose the rustc-driver extraction module. The report does not claim that every library function is free of rustc-private coupling under every feature configuration.
- **rustc lifetime not generalized:** this report does not establish whether `rustc_driver::run_compiler` can safely or efficiently be invoked repeatedly inside one custom process, nor what compiler globals would need resetting. That requires rustc-specific investigation.
- **No protocol survey beyond Charon:** LSP, MCP, or Aeneas server designs are separate #3720 subjects.
- **No Anneal design decision:** whether Anneal should use a subprocess, directly link `charon_lib`, or introduce a service belongs to Anneal design authority, not this reference report.

## Evidence

Primary subject:

```text
AeneasVerif/charon
a535e914f74db4fd9e6be7048f4233270d8945c0
version 0.1.210
```

Pinned source:

- `charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`: `charon_lib`, executable targets, and the optional/default rustc feature boundary.
- `charon/src/lib.rs`, blob `a5530a1778d231297d8e480cf11531b141125a4f`: public library modules and LLBC deserialization helpers; points to the separately documented driver callbacks.
- `charon/src/bin/charon/cli.rs`, blob `3580a74c6079079510aba318949810bc1a95a15f`: complete pinned `charon` subcommand enum.
- `charon/src/bin/charon/main.rs`, blob `b4460ce4cd3baa32308718e79b6e194860b042a6`: wrapper topology, Cargo/driver subprocess creation, `RUSTC_WRAPPER`, `CHARON_ARGS`, and synchronous `spawn().wait()` behavior.
- `charon/src/bin/charon-driver/driver.rs`, blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`: rustc callback driver, selected-crate filtering, per-invocation option recovery, and returned `TransformCtx`.
- `charon/src/bin/charon-driver/main.rs`, blob `ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`: post-rustc transformation, `CrateData` serialization, status handling, and process termination.
- `README.md`, blob `6470a71c857dcb64be248cdb5dfe67576d914c99`: supported user flow (“run `charon`” to produce LLBC; use `charon-lib` to read/manipulate it) and alpha/API-stability boundary.

The repository tree for the pinned commit was also inspected to locate the binary/library source split. No fresh **execution** was performed.

## Revalidation

For a later Charon revision, the cheapest reliable architecture check is:

1. Read `charon/Cargo.toml` and record all library and binary targets plus feature boundaries.
2. Read `charon/src/lib.rs` and determine whether Rust-source extraction callbacks/driver functions are now publicly exported.
3. Read the `charon` clap subcommand enum and executable entry points; look specifically for server, daemon, RPC, watch, or long-lived modes.
4. Follow `charon cargo` and `charon rustc` far enough to determine whether they spawn a fresh driver, call extraction in-process, or send requests to a persistent service.
5. Follow the rustc callback path through result construction and determine the lifetime of compiler state, `TransformCtx`, and serialized output.
6. If a server exists, record its request/session identity, source/workspace versioning, cancellation, concurrency, cache/invalidation rules, and what native state survives between requests.

If the architecture remains batch-oriented, investigate “Charon incremental capabilities” separately. On an execution-capable surface, run repeated unchanged and edited `charon cargo` invocations while recording Cargo/rustc work, Charon driver invocations, output hashes, cache paths, and timings. That experiment can establish lower-layer reuse without conflating it with the presence of a Charon server API.
