# Rust-nightly upgrade checklist for the Anneal toolchain

## Summary

A Rust-nightly change in current Anneal is not an isolated compiler-version bump. The normal runtime Charon path is built around the Rust nightly required by the Charon revision pinned by Aeneas. At the examined baseline, Aeneas `nightly-2026.06.03` pins Charon `a535e914…`, and that Charon source embeds `nightly-2026-05-31`. Anneal separately hard-codes the same date in `anneal/flake.nix`, packages that Rust sysroot, and invokes the Aeneas-bundled Charon with `CHARON_TOOLCHAIN_IS_IN_PATH=1`. In that mode Charon trusts Anneal's `PATH` and dynamic-library environment; it does not compare the supplied rustc against its embedded channel.

The first upgrade rule is therefore simple: **derive the required Rust nightly from the exact Charon revision that will run, then make Anneal package that nightly**. Editing `rustDate` alone tests an unsupported cross-version combination unless the selected Charon revision itself requires the new nightly. A same-date Charon release label is not a substitute for resolving Aeneas's exact Charon pin.

A complete upgrade has four distinct gates: identity/coupling, distribution/packaging, executable compatibility, and semantic revalidation. Passing `rustc --version` or successfully starting Charon covers only part of the third gate. Charon uses `rustc_private` and compiler-internal MIR APIs, so a nightly change can alter extraction behavior even when the process starts. The upgrade must therefore run a small old-versus-new MIR/LLBC fixture matrix and re-evaluate corpus reports whose subjects are bound to the old rustc/Reference/Charon revisions.

Current Anneal also has an invalidation trap worth making explicit. Exocrate's installed-toolchain namespace hashes `anneal/Cargo.toml`, `anneal/Cargo.lock`, OS, and architecture; it does **not** hash `anneal/flake.nix`. A flake-only Rust-date change can therefore leave the existing installation identity unchanged. Normal released remote metadata partly closes this gap because changing the archive URL/hash in `Cargo.toml` changes the slug, but local-development or local-archive testing must deliberately avoid stale installations.

`upgrade-checklist.json` records the gates in machine-readable form. `source-map.json` records the exact implementation evidence used here.

## Applicability

This checklist describes the toolchain topology at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, with Aeneas `nightly-2026.06.03` (`ac9f1bc5…`), its pinned Charon `a535e914…` (0.1.210), and Rust `nightly-2026-05-31`, whose compiler source is identified in the current corpus as `rust-lang/rust@14210df0…`.

The checklist is intended for a future change that replaces the selected Rust nightly while preserving Anneal's current architecture: a packaged Rust sysroot plus an Aeneas release containing Charon, invoked through Anneal's trusted-PATH mode. If that architecture changes—for example, Anneal stops using Aeneas's bundled Charon, Charon gains a stable compiler-facing interface, or the extraction boundary moves away from rustc-private MIR—the upgrade gates must be re-derived rather than copied mechanically.

The report does not assume that a new Aeneas release, a new Charon release, and a new Rust nightly share a date or move together. The baseline already demonstrates why: Aeneas's `nightly-2026.06.03` pins Charon `a535e914…`, while Charon's own same-date release tag names a different revision and a different Rust nightly. Exact revision relationships carry the coupling; labels do not.

No fresh rustc, Charon, Aeneas, Nix, or Anneal execution was performed for this report. The upgrade procedure combines exact source contracts with the current reference corpus's pinned identities and mechanically indexed applicability.

## Findings

### 1. Resolve the runtime Charon first; derive Rust from that exact source

Current Aeneas source records the Charon commit it expects in `charon-pin`:

```text
a535e914f74db4fd9e6be7048f4233270d8945c0
```

That Charon revision records:

```toml
channel = "nightly-2026-05-31"
components = ["rustc-dev", "llvm-tools-preview", "rust-src", "miri"]
```

and its wrapper compiles that file into the binary with `include_str!`. This makes the Charon revision the source of truth for the compiler channel used by the rustc-facing driver.

For a normal Anneal toolchain upgrade, resolve the new Aeneas revision or otherwise selected runtime Charon revision, inspect that exact Charon source, and use its embedded channel as the required Rust nightly. If the proposed change instead keeps Charon fixed and changes only Rust, classify it as a deliberate compatibility experiment until execution establishes that the combination works. Do not silently treat an adjacent nightly as supported.

Basis: **source** — Aeneas `charon-pin`; Charon `charon/rust-toolchain` and `charon/src/bin/charon/toolchain.rs`.

### 2. Anneal's current Rust metadata is not an independent derivation from Aeneas

`anneal/flake.nix` hard-codes:

```nix
rustDate = "2026-05-31";
```

Its `aeneas-unpacked` derivation writes `metadata.json` with `RUST_DATE=${rustDate}` and `RUST_VERSION="nightly-$RUST_DATE"`. The Lean version in the same derivation is parsed from the unpacked Aeneas archive, but the Rust date is not parsed from Aeneas or Charon. It is copied from Anneal's own `rustDate` variable.

Consequently, reading the generated `metadata.json` cannot independently prove that a proposed Rust nightly matches the selected Charon. The upgrade must compare Anneal's value against the exact Charon toolchain source before building the archive.

Basis: **source** — `google/zerocopy@41f5b37…`, `anneal/flake.nix`; conclusion **derived** from the different data flows for Lean and Rust metadata.

### 3. Rebuild the complete packaged Rust sysroot on every supported host

Current `fetchRustToolchain` constructs one sysroot from Rust distribution components. It downloads host-specific `cargo`, `rustc`, `rust-std`, `rustc-dev`, `llvm-tools`, and `miri`, plus the date-specific `rust-src` archive. Anneal maintains a separate fixed-output SHA-256 for each supported host:

- Linux x86_64;
- Linux aarch64;
- macOS x86_64;
- macOS aarch64.

A nightly change therefore requires more than changing one string. For every supported host, confirm that all required distribution artifacts exist, rebuild the merged sysroot, and update the corresponding fixed-output hash from the resulting derivation. Preserve the current distinction between Charon's rustup component name `llvm-tools-preview` and the Rust distribution archive component named `llvm-tools`.

The Charon toolchain file also lists target triples. Charon's own rustup fallback deserializes only `channel` and `components`, so that target list is not installed by its runtime installer. Anneal's current packager likewise downloads host `rust-std`, not every target listed by Charon. If an upgrade introduces cross-target verification requirements, target standard-library availability must be checked explicitly instead of inferred from Charon's checked-in target list.

Basis: **source** — Anneal `anneal/flake.nix`; Charon `charon/rust-toolchain` and `toolchain.rs`.

### 4. Verify the trusted-PATH contract, not just the compiler binary

Charon's normal rustup path executes programs through `rustup run <embedded-channel>`. Anneal deliberately bypasses that selection. `Toolchain::command(Tool::Charon)` sets `CHARON_TOOLCHAIN_IS_IN_PATH=1`, puts the packaged Rust `bin` directory first on `PATH`, and points `LD_LIBRARY_PATH` or `DYLD_LIBRARY_PATH` at the packaged Rust libraries.

At Charon 0.1.210, trusted-PATH mode performs no version comparison. This matters because `charon-driver` enables `rustc_private`, imports many `rustc_*` crates directly, and dynamically links rustc libraries. A wrong compiler can therefore reach a low-level linking, startup, API, or translation failure without a dedicated "wrong toolchain" diagnostic.

For the new archive, verify all of the following from the same installed root:

1. packaged `rustc -Vv` identifies the intended nightly;
2. packaged `cargo -V` starts;
3. the Aeneas-bundled `charon` sees the intended sysroot through its effective toolchain path;
4. `charon-driver` starts under the library environment Anneal constructs;
5. a minimal Rust crate completes extraction and produces parseable LLBC;
6. Aeneas accepts that output and generates Lean for the representative path used by Anneal.

Startup without extraction is insufficient because the unstable compiler-facing APIs are exercised during translation.

Basis: **source** — Charon `toolchain.rs`, `charon-driver/main.rs`, `charon/Cargo.toml`; Anneal `anneal/src/setup.rs`.

### 5. Treat MIR and LLBC behavior as part of the upgrade, not merely process compatibility

The selected Charon driver reads rustc-internal MIR and relies on unstable compiler queries and representations. Current corpus reports bind concrete findings about MIR phases, reachability, unsafe operations, spans, layout, type identity, and Charon lowering to the old rustc/Charon pair. A new nightly can therefore change the verification input even if all binaries execute successfully.

The minimum semantic upgrade probe should preserve a compact fixture suite and compare old and new outputs for at least:

- constant and structurally unreachable control flow;
- calls, drops, unwind edges, panic, and divergence;
- raw-pointer operations and representative intrinsics;
- structs/enums/unions and layout-sensitive operations;
- generics, traits, closures, constants/statics, and one dependency body;
- build-script- and proc-macro-generated code if those paths are in Anneal's covered configuration;
- source spans and item identities needed for diagnostics.

Record the rustc identity, Charon identity, invocation, MIR stage where observable, serialized ULLBC/LLBC, warnings/errors, and exit status. A byte diff is useful but should not be the only acceptance criterion: harmless serialization/order changes and semantic representation changes must be distinguished.

Basis: **source** for Charon's rustc-private dependency; **derived** from the corpus's revision-bound MIR/Charon findings.

### 6. Revalidate the affected corpus mechanically, then investigate only material deltas

At reference head `e1ef8f81d5e12ea48c35023ef8da740ca9dbfd10`, `CATALOG.json` contains:

- 42 report packages whose `subjects` directly identify `rust-lang/rust@14210df0…`;
- 32 packages whose subjects directly identify `rust-lang/reference@ad35aca4…`;
- 57 packages whose subjects directly identify `AeneasVerif/charon@a535e914…`.

These sets overlap. They are a **revalidation index**, not a list of reports that become false when the nightly changes. The efficient upgrade procedure is to query the catalog for exact old subject identities, classify each report by whether its claims depend on changed source/behavior, and revalidate only the material regions or preserved probes. Reports about stable normative language rules may continue to apply; reports about rustc-private layout, MIR, diagnostics, or Charon lowering deserve closer scrutiny.

A newer version should normally receive a distinct report package when preserving its behavior is useful. Do not mutate an old precisely identified report merely because the current toolchain moved.

Basis: **derived** from the exact current `CATALOG.json` metadata at blob `4f12c8e2…` plus the corpus format contract.

### 7. Make installation identity move with the archive

Current Exocrate configuration uses:

```text
versioned_files = ["../Cargo.toml", "../Cargo.lock"]
```

The version slug also includes OS and architecture. `anneal/flake.nix` is not one of the hashed inputs. Therefore changing only `rustDate` or Rust fixed-output hashes in `flake.nix` does not mechanically select a new installed-toolchain directory.

For a real remote release, Anneal's archive URL and expected SHA-256 live in `anneal/Cargo.toml`. Updating those values changes a versioned file and therefore changes the installation slug. This is the normal release path to preserve. During local development, however, a new local archive combined with unchanged `Cargo.toml`/`Cargo.lock` can resolve to an already-existing installation and reuse it before opening the new archive.

An upgrade test must therefore either change the versioned release metadata as production will, or use an isolated/cleared installation namespace. Otherwise a passing test may have exercised the previous toolchain rather than the newly built nightly.

Basis: **source** — Anneal `anneal/src/setup.rs`, `anneal/Cargo.toml`; Exocrate behavior already source-indexed in the current reference corpus; conclusion **derived**.

### 8. Keep packaging and semantic gates separate

A fixed-output derivation proves that a particular build input produced the expected output bytes; it does not prove the compiler/Charon pair is semantically compatible. Conversely, a successful one-crate extraction does not establish that all four platform archives can be built, relocated, or installed safely.

Use separate acceptance gates:

| Gate | Minimum evidence |
| --- | --- |
| Identity/coupling | exact Aeneas → Charon → Rust resolution and Anneal equality |
| Distribution | all required Rust components available on every supported host; fixed-output hashes updated |
| Runtime | packaged rustc/cargo/Charon start and one end-to-end extraction/translation succeeds |
| Semantic | representative MIR/LLBC golden matrix inspected for meaningful deltas |
| Corpus | old rustc/Reference/Charon subject-index reports triaged and material claims revalidated |
| Installation | new release selects the new archive rather than reusing an old Exocrate installation |
| Platform | omnibus layout, runtime libraries, relocation/fixups, and representative execution checked on supported hosts |

Do not collapse these into one "toolchain builds" signal. They fail for different reasons and establish different properties.

Basis: **derived** from the source contracts above and current corpus boundaries.

## Boundaries

- **No fresh execution.** This report did not download a replacement Rust nightly, build an omnibus archive, run Charon, generate LLBC, or execute Aeneas/Lean. The checklist identifies the experiments that an execution-capable upgrade must perform.
- **No adjacent-version compatibility claim.** The report does not claim any Rust nightly other than the baseline is compatible with Charon `a535e914…`.
- **Rust release provenance is not reproved here.** The current corpus binds `nightly-2026-05-31` to `rust-lang/rust@14210df0…`; this report uses that identity but does not reproduce Rust's distribution-to-Git provenance chain.
- **The catalog counts are a snapshot.** They describe reference head `e1ef8f81…`. Future corpus growth changes the revalidation index. Query the then-current catalog during a real upgrade.
- **Not every revision-bound report needs new research.** Subject identity is a conservative dependency signal, not proof that a claim changed.
- **The target-list distinction does not imply Anneal currently supports cross-compilation.** It only prevents treating Charon's toolchain-file target list as evidence that Anneal packages all corresponding standard libraries.
- **Current remote Exocrate metadata is placeholder data.** `anneal/Cargo.toml` explicitly requires real URLs/hashes before crate publication. The invalidation rule is still relevant because those metadata bytes are part of the version slug.
- **`charon_lib` is not used here as the runtime compiler driver.** Current Anneal's `Cargo.toml` also pins a no-default-features `charon_lib` dependency through Charon's own `nightly-2026.06.03` tag. If future Anneal code makes that library semantically active, its independent revision/toolchain/API relationship must join this checklist.
- **The checklist does not replace tool-specific upgrade reports.** Aeneas, Charon, Lean, Lake, Mathlib, and Rust each have distinct behavior surfaces. This report specifies the Rust-nightly portion and its coupling edges.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

### Anneal source

`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`
  - `rustDate = "2026-05-31"`;
  - four platform-specific `rustToolchainSha256` values;
  - exact Rust component download/merge procedure;
  - `aeneas-unpacked/metadata.json` writes Rust identity from Anneal's `rustDate` rather than parsing it from Aeneas;
  - omnibus archive composition and layout checks.
- `anneal/src/setup.rs`, blob `9e17911f4d1e7695cc63fe9f8b2b20b2f0322f00`
  - Exocrate versioned files;
  - `Tool::Charon` points at `aeneas/bin/charon`;
  - trusted-PATH and Rust dynamic-library environment.
- `anneal/Cargo.toml`, blob `9edee13427fd5e3699abd3709cc9f33d7652873e`
  - remote archive URL/hash metadata is versioned by Exocrate;
  - current metadata is explicitly placeholder release data;
  - independent no-default-features `charon_lib` dependency is pinned to Charon's `nightly-2026.06.03` tag.

Evidence role: **source**.

### Aeneas and Charon source

`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- `charon-pin`, blob `06dbe0dbf1d5b7f1e6f2a21889ab6bf770e89de6`, pins Charon `a535e914…`.

`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `charon/rust-toolchain`, blob `3c98116ae62afb83263fa1654037badaf569e1c1`, pins `nightly-2026-05-31`, components, and targets;
- `charon/src/bin/charon/toolchain.rs`, blob `b35d1d0236cd7e1c5f68ad5b80b3371b82f2e784`, embeds the toolchain and defines rustup versus trusted-PATH selection;
- `charon/src/bin/charon-driver/main.rs`, blob `ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`, enables `rustc_private` and imports rustc implementation crates;
- `charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`, documents dynamic linkage of the driver to rustc dylibs and the wrapper requirement.

Evidence role: **source**.

### Rust source identity

`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` is the compiler source identity already bound by the current corpus to Anneal-era `nightly-2026-05-31`. `src/ci/channel`, blob `bf867e0ae5b6c08df1118a2ece970677bc479f1b`, identifies that source tree as the nightly channel.

Evidence role: **source** for the source tree/channel; the exact distribution-date-to-Git mapping is inherited from the current pinned corpus and is not independently reproved here.

### Current corpus applicability index

Reference head `e1ef8f81d5e12ea48c35023ef8da740ca9dbfd10`, `CATALOG.json` blob `4f12c8e2bb294d910ad85338477c7673bb4dfcf0`:

- 42 packages directly identify the baseline rustc revision;
- 32 directly identify the baseline Rust Reference revision `ad35aca481751a06afeb23820a672b0f3b11a476`;
- 57 directly identify the baseline Charon revision.

The counts were obtained by exact subject-identity matching, not topic-name search.

Evidence role: **derived** deterministic catalog query.

### Existing corpus source indexes used to avoid rediscovery

The current reference corpus already preserves the underlying source analysis in reports including:

- `reports/charon-toolchain-requirements-nightly-2026-06-03/`;
- `reports/charon-toolchain-contract-0-1-210/`;
- `reports/exocrate-cache-version-identity-main-41f5b37/`;
- `reports/rustc-mir-before-charon-nightly-2026-05-31/`;
- `reports/aeneas-charon-compatibility-nightly-2026-06-03/`.

These are navigation aids to the primary evidence, not substitutes for the upstream sources listed above.

## Revalidation

For a future Rust-nightly upgrade, run the following sequence rather than redoing broad research.

1. Resolve the exact Aeneas revision and its `charon-pin`. Resolve the exact Charon revision that Anneal will execute.
2. Read that Charon revision's toolchain file and wrapper implementation. Record the required Rust channel, components, target list, and whether trusted-PATH mode now performs any version check.
3. Compare the required channel to Anneal's `rustDate`. If they differ, stop treating the combination as a normal supported upgrade until the discrepancy is intentionally resolved.
4. Recompute all supported-host Rust fixed-output derivations. Verify every required component exists and record the new hashes.
5. Build the complete Anneal toolchain archive on each supported host. Verify the archive layout and the platform-specific dynamic-link/relocation behavior already covered by the corresponding reference reports.
6. Install into a fresh Exocrate namespace. Confirm `rustc -Vv`, `cargo -V`, Charon's effective sysroot, a minimal Charon extraction, and Aeneas acceptance of the resulting LLBC.
7. Run an old-versus-new MIR/ULLBC/LLBC specimen suite covering control flow, unsafe operations, layout, drops/unwind, generics/traits, generated code, dependencies, and source identity. Classify semantic deltas instead of accepting or rejecting by byte difference alone.
8. Query the then-current `CATALOG.json` for subjects matching the old Rust, Rust Reference, and Charon identities. Revalidate reports whose material claims touch changed implementation/specification regions or whose preserved probes now differ.
9. Confirm release metadata in `Cargo.toml` selects the new archive and changes the Exocrate installation identity. For local archives, explicitly isolate or clear the old installation because local archive bytes are not part of the slug.
10. Preserve the new exact compiler/Charon identities, hashes, fixture outputs, and any materially changed report findings in the reference corpus before using the upgrade as an Anneal baseline.

A passing run establishes compatibility for the concrete tested toolchain and fixtures. It does not establish a compatibility interval across neighboring Rust nightlies.