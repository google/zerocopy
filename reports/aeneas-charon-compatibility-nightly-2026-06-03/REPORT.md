# Aeneas–Charon compatibility for Anneal at Aeneas nightly-2026.06.03

## Summary

At `google/zerocopy@0eca5581c6d27aaeaba4c421f7bf2a26bdd50228`, Anneal's Nix toolchain assembly selects the Aeneas release `nightly-2026.06.03`. That Aeneas tag resolves to `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`. The four release assets selected by Anneal are identified below by their GitHub release SHA-256 digests, which equal the hashes encoded in `anneal/flake.nix` after converting Nix SRI form to hex.

Aeneas does **not** use the Charon commit named by Charon's own `nightly-2026.06.03` tag. Aeneas's `charon-pin` and `flake.lock` both select `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, and Aeneas's release recipe copies the `charon` and `charon-driver` executables built from that input into its release archive. In contrast, Anneal independently declares `charon_lib` using Charon's `nightly-2026.06.03` tag; `anneal/Cargo.lock` resolves that tag to `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`. The two Charon subjects therefore differ. `0c91ca1…` is a descendant 15 commits ahead of `a535e914…`.

The discrepancy is currently dependency state, not an executing cross-revision LLBC boundary. Anneal's live CLI exposes only `setup`, no code under `anneal/src` refers to `charon_lib`, and the source-defined `Tool::Charon` path selects `aeneas/bin/charon` from the installed toolchain. Thus the Charon that current Anneal source is prepared to invoke is the Aeneas-bundled `a535e914…` binary, while the independently locked `0c91ca1…` Rust library is unused at this commit.

Primary source gives useful but bounded compatibility evidence for the two exact Charon revisions: both report Charon version `0.1.210`, and the Aeneas-facing JSON deserializer, generated JSON parser/type definitions, Charon version file, serialization implementation, and Charon manifest are byte-identical between the two commits. This establishes that the declared JSON LLBC parsing/version surface examined here did not change. It does **not** establish end-to-end cross-revision compatibility, semantic equivalence, or a generally stable LLBC format. No executable cross-revision probe was possible in the observation environment.

## Applicability

This report applies only to the exact subjects listed in `REPORT.json`, observed on 2026-09-25. In particular, it describes Anneal source at `google/zerocopy@0eca5581c6d27aaeaba4c421f7bf2a26bdd50228`, Aeneas release `nightly-2026.06.03` at `ac9f1bc…`, Aeneas's pinned Charon at `a535e914…`, and Anneal's independently locked `charon_lib` at `0c91ca1…`.

At this Anneal commit, there are two distinct acquisition layers. `anneal/flake.nix` names and hashes the real Aeneas `nightly-2026.06.03` release assets and assembles them into the Nix-built Anneal toolchain archive. The `cargo anneal setup` executable, however, obtains its default remote-archive metadata from `anneal/Cargo.toml`, whose four URLs and hashes are still explicit placeholders. `setup --local-archive` can install a supplied real archive. Accordingly, this report's Aeneas subject is the exact release consumed by the current Nix toolchain assembly; it is not a claim that the live default CLI remote setup path already downloads those release assets.

The four Aeneas release assets selected by the Nix assembly are:

| Anneal target | Release asset | SHA-256 |
| --- | --- | --- |
| Linux x86_64 | `aeneas-linux-x86_64.tar.gz` | `00fb8ef427d4d06dcabd90f5196266e07731adf2a7466964ce6f4f6d1e8cbc11` |
| Linux aarch64 | `aeneas-linux-aarch64.tar.gz` | `25402c4cbcb7da2d337cb168663542bc9c75ae9b10d2d2708f5289e8ca9d1902` |
| macOS x86_64 | `aeneas-macos-x86_64.tar.gz` | `ba25ee857a76fa8f4c1022f6dff4072c9a01007453d67c61cfbaa1aa1c03e317` |
| macOS aarch64 | `aeneas-macos-aarch64.tar.gz` | `76f78b645e338ec7e89329f0ad22792997f42bd9b5eb14643ac32ade224eeb61` |

The report does not generalize to adjacent nightly releases or other Charon commits merely because their dates, versions, or tags are similar.

## Findings

### Anneal's Aeneas subject and release packaging

`anneal/flake.nix` sets `releaseTag = "nightly-2026.06.03"` for the Aeneas download package. Its platform mapping selects `linux-x86_64`, `linux-aarch64`, `macos-x86_64`, or `macos-aarch64`; `fetchAeneas` downloads `aeneas-${target}.tar.gz` from the matching Aeneas GitHub release and verifies the platform-specific Nix hash. GitHub's release metadata for those four assets reports the same SHA-256 values shown above.

The Aeneas Git tag `nightly-2026.06.03` resolves to `ac9f1bc5262a5e4ff1e24ca78617121382202727`. Aeneas's release workflow builds the Linux and macOS release packages from the tagged checkout. The Aeneas flake's release construction copies Aeneas itself plus Charon's `charon` and `charon-driver` executables into the release tree. Anneal's toolchain assembly unpacks the Aeneas asset and requires the resulting archive to contain `aeneas/bin/aeneas`, `aeneas/bin/charon`, and `aeneas/bin/charon-driver`.

Basis: **source** (`google/zerocopy@0eca5581…`, `anneal/flake.nix`; `AeneasVerif/aeneas@ac9f1bc…`, `flake.nix` and release workflow) + **source** Git tag/release metadata. The released binary assets were not independently rebuilt or unpacked during this observation, so the source-to-binary provenance chain is the release recipe plus exact asset hashes, not a reproducible-build verification.

### Aeneas pins Charon `a535e914…`

At `AeneasVerif/aeneas@ac9f1bc…`, `charon-pin` names exactly:

`a535e914f74db4fd9e6be7048f4233270d8945c0`

The same revision is the locked `charon` input in Aeneas's `flake.lock`. Aeneas's `check-charon-pin` flake check compares the locked input revision to the final line of `charon-pin`, and `scripts/check-charon-install.sh` requires a checked-out Charon installation to have that exact Git revision. These are mechanical checks of the source coupling, not just prose documentation.

Aeneas's release package is built from the flake's Charon input: the release recipe copies `${charon-portable}/bin/charon` and `charon-driver`. Aeneas itself links Charon's OCaml library; `src/llbc/LlbcOfJson.ml` includes `Charon.OfJson` and `Charon.OfJson.Llbc`, and Aeneas's main input path reads `.llbc` through that parser. Therefore the source-defined Aeneas release couples its bundled Charon producer and its Aeneas-side LLBC parser to the same pinned Charon subject, `a535e914…`.

Basis: **source** at `AeneasVerif/aeneas@ac9f1bc…`: `charon-pin`, `flake.lock`, `flake.nix`, `scripts/check-charon-install.sh`, `src/dune`, `src/llbc/LlbcOfJson.ml`, and `src/Main.ml`.

### Anneal independently locks `charon_lib` to `0c91ca1…`

Anneal's `Cargo.toml` declares:

`charon_lib = { package = "charon", git = "https://github.com/AeneasVerif/charon.git", tag = "nightly-2026.06.03", default-features = false }`

At the examined Anneal commit, `Cargo.lock` resolves that dependency to:

`0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`

Charon's own Git tag `nightly-2026.06.03` resolves to the same `0c91ca1…` commit. This is not Aeneas's Charon pin. A Git comparison shows `0c91ca1…` is 15 commits ahead of `a535e914…`, with `a535e914…` as the merge base.

A complete search of the five Rust files under `anneal/src` found no reference to `charon_lib` or to LLBC deserialization through that library. The dependency is declared and locked but unused by live Anneal source at this commit.

Basis: **source** (`google/zerocopy@0eca5581…`, `anneal/Cargo.toml`, `anneal/Cargo.lock`, complete `anneal/src/*.rs` source set) + **source** Charon tag and commit ancestry.

### The two `nightly-2026.06.03` labels do not name the same Charon source

The Aeneas release tag `AeneasVerif/aeneas@nightly-2026.06.03` resolves to Aeneas commit `ac9f1bc…`; that source pins Charon `a535e914…`. Separately, `AeneasVerif/charon@nightly-2026.06.03` resolves to Charon `0c91ca1…`. Anneal uses the Aeneas release label for its Nix toolchain and the Charon release label for `charon_lib`, but the resulting Charon revisions are different.

This is a concrete example of why a shared release-label string is insufficient as an immutable cross-repository identity.

Basis: **source** tag resolution + the two exact dependency encodings above; the final sentence is **derived** from those observations.

### Current Anneal does not execute a cross-revision LLBC boundary

Anneal's current executable command enum contains only `Setup`. The setup/toolchain code nevertheless defines where later pipeline code will obtain tools: `Tool::Charon` resolves to `toolchain.aeneas_bin_dir().join("charon")`, i.e. `aeneas/bin/charon` inside the installed Anneal toolchain. `scanner.rs` states that Charon-generated LLBC is the source of truth for later Aeneas processing and defines the LLBC artifact paths, but that processing is not wired into the live CLI at this commit.

Consequently, there is no current live V2 path in this source snapshot where LLBC serialized by Charon `0c91ca1…` is handed to Aeneas's parser from Charon `a535e914…`. The source-defined external Charon selection instead points at the Aeneas-bundled `a535e914…` executable, while `0c91ca1…` is an unused Rust dependency.

Basis: **source** (`anneal/src/main.rs`, `anneal/src/setup.rs`, `anneal/src/scanner.rs`, and complete source search) + **derived** pipeline conclusion.

### Exact source evidence is consistent with the two revisions sharing the examined LLBC JSON interface

Both Charon commits declare version `0.1.210`. Charon serializes a `charon_version` field into `CrateData`. Both its Rust deserializer and its OCaml deserializer reject an input whose version string differs from the locally supported Charon version. The OCaml path used by Aeneas therefore has a mechanical version-equality check.

That check does not discriminate these two commits because both report `0.1.210`. More importantly, the following files have identical Git blob identities at `a535e914…` and `0c91ca1…`:

| File | Shared Git blob |
| --- | --- |
| `charon-ml/src/OfJson.ml` | `a30706a384a78d51cf5a2fe566028ba3e902d0a0` |
| `charon-ml/src/generated/Generated_OfJson.ml` | `b82b3475b953c231e39fb63ca93bc3adb9e0aa81` |
| `charon-ml/src/generated/Generated_Types.ml` | `69aad6059931c8b365f7d1abb800e5716aec8ad5` |
| `charon-ml/src/CharonVersion.ml` | `ea6a2833a3432b63eb95b1bda95dc333f60d6b4b` |
| `charon/src/export.rs` | `d5428958eb870f9f8531a8d193385c6be782338a` |
| `charon/Cargo.toml` | `8c9936202e7bdbdaaefbc19305363da1ab6c0084` |

This is strong **source** evidence that the examined JSON serialization/deserialization definitions and explicit version gate did not change between the revisions. It is not execution evidence. The 15 intervening commits do change translation implementation and generated full-AST material, so byte-identical parser/type definitions do not imply that the two Charon executables produce semantically identical LLBC for every Rust input.

## Boundaries

- **Execution compatibility is unknown.** No minimal cross-revision LLBC probe was run. The observation environment had no `rustc`, `cargo`, `rustup`, or Nix, and the available GitHub connector could inspect release metadata and source text but could not materialize the approximately 60 MB binary release assets. No claim here depends on pretending a source comparison was an execution test.
- **The exact release archives were not unpacked.** Their identities are fixed by GitHub's release SHA-256 digests and Anneal's matching Nix hashes. The claim that they contain Charon built from `a535e914…` is supported by the exact tagged Aeneas build/release recipe and pin checks, not by binary provenance or reproducible-build verification performed here.
- **General LLBC stability is not established.** Equality of Charon version `0.1.210` and equality of the examined parser/serialization blobs cover these exact commits only. They do not establish compatibility of adjacent commits, adjacent nightlies, arbitrary Charon revisions, or future LLBC.
- **Semantic equivalence is not established.** Charon changes between `a535e914…` and `0c91ca1…` include translation code and generated full-AST material. The source evidence above says the examined serialized interface definitions did not change; it does not say every Rust input translates to equivalent LLBC.
- **The current runtime pipeline is incomplete.** `scanner.rs` and `Tool::Charon` describe intended/source-defined pieces, but the live `cargo-anneal` CLI exposes only setup. This report does not infer execution behavior from helpers that are not yet wired into a command.
- **The independent `charon_lib` discrepancy is latent at this commit.** Because no Anneal source uses the dependency, this report does not claim that LLBC currently crosses from `0c91ca1…` to the Aeneas `a535e914…` parser.

## Evidence

The corpus contract used to author this report was read from `google/zerocopy` `reference` tip `702d9d821bf6b9928cccb9324bc755e76da33896`, including `AGENTS.md`, `FORMAT.md`, `README.md`, and `CATALOG.json`. Issue `google/zerocopy#3720` supplied research scope and report-quality expectations; it was not used as behavioral authority for Anneal, Aeneas, or Charon.

**Source — Anneal.** `google/zerocopy@0eca5581c6d27aaeaba4c421f7bf2a26bdd50228`: `anneal/flake.nix` (`fetchAeneas`, `aeneas-download`, toolchain assembly/layout checks); `anneal/Cargo.toml` (placeholder exocrate remote metadata and `charon_lib` declaration); `anneal/Cargo.lock` (`charon` resolution); `anneal/src/main.rs` (live command surface); `anneal/src/setup.rs` (`Tool::Charon` path and managed command environment); `anneal/src/scanner.rs` (LLBC artifact role). The complete `anneal/src/*.rs` set was checked for `charon_lib` use and contained none.

**Source — Aeneas.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`: `charon-pin`; `flake.lock`; `flake.nix` (Charon input, pin check, release construction); `scripts/check-charon-install.sh`; release workflow; `src/dune`; `src/llbc/LlbcOfJson.ml`; `src/Main.ml`. Git tag `nightly-2026.06.03` resolves to this commit.

**Source — Aeneas release metadata.** GitHub release `nightly-2026.06.03`, published 2026-06-03, identifies the four `aeneas-{target}.tar.gz` assets and their SHA-256 digests. Those digests equal the four hashes encoded by Anneal's `anneal/flake.nix` after conversion from Nix SRI notation.

**Source — Charon.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` and `@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`: `charon/Cargo.toml`, `charon/src/export.rs`, `charon-ml/src/OfJson.ml`, `charon-ml/src/CharonVersion.ml`, and the generated JSON/type files listed above. Git comparison establishes that `0c91ca1…` is 15 commits ahead of `a535e914…`. Charon tag `nightly-2026.06.03` resolves to `0c91ca1…`.

**Execution — environment only.** Tool discovery in the observation sandbox found no `rustc`, `cargo`, `rustup`, or Nix. Attempts to obtain the binary release asset outside the GitHub metadata/source connector had no usable network path. This evidence establishes why no compatibility execution probe is reported; it is not compatibility evidence.

**Derived.** The two exact Charon revisions are different; the later one is a descendant of the Aeneas pin; Anneal's independent library is unused by live source; and therefore no current live V2 LLBC crosses between these two revisions. These conclusions follow from the exact source and ancestry observations above.

## Revalidation

For a new Anneal revision, first repeat the pin comparison without broad research:

1. Resolve Anneal's selected Aeneas release in `anneal/flake.nix`; resolve the Aeneas release tag to its immutable Aeneas commit and verify Anneal's asset hash against current release metadata.
2. At that Aeneas commit, read both `charon-pin` and the locked `charon` input in `flake.lock`; verify they agree and inspect the release recipe that supplies `charon`/`charon-driver`.
3. Read Anneal's `Cargo.toml` and `Cargo.lock`; resolve `charon_lib` to the immutable Charon commit.
4. Search live Anneal source for `charon_lib` use and inspect the executable command path before asserting that any serialized LLBC crosses between revisions.
5. If the Charon commits differ, compare their LLBC version plus the Aeneas-facing serializer/deserializer and generated JSON/type blobs before making any source-level compatibility statement.

The cheapest execution probe for a future revision that actually puts the two Charon subjects on opposite sides of an LLBC boundary is a two-case fixture, not the full Anneal suite:

1. With the independently consumed Charon revision, use its recorded Rust toolchain to generate JSON LLBC for a tiny Rust crate with the Aeneas preset.
2. Feed that exact `.llbc` to the exact Aeneas release binary and request one minimal backend translation. Record the Charon revision, Aeneas asset hash, command lines, LLBC hash, and result.
3. Run the same fixture with the Charon bundled in the Aeneas release as a control.

A passing cross-revision case would establish only that the preserved fixture parses/translates under that exact pair. It would not prove general LLBC compatibility. A failure would provide a concrete incompatibility specimen to preserve with a later report.
