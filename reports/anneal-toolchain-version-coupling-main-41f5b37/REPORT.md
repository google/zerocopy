# Anneal toolchain version-coupling graph at `google/zerocopy@41f5b37`

## Summary

Current Anneal does not have one single version pin. It has several overlapping dependency graphs that happen to agree on the versions used by the ordinary runtime toolchain, while one separate Cargo dependency already demonstrates why repository-local release labels and semantic versions are not sufficient identities.

For the installed omnibus toolchain, `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` selects Aeneas `nightly-2026.06.03`, Rust `nightly-2026-05-31`, and Lean `v4.30.0-rc2`. The selected Aeneas release resolves to `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`; that source pins Charon `a535e914f74db4fd9e6be7048f4233270d8945c0`, whose own toolchain file selects the same Rust nightly. Aeneas's Lean backend selects the same Lean release and its Lake manifest resolves Mathlib to `5450b53e5ddc75d46418fabb605edbf36bd0beb6` plus eight exact transitive package revisions.

Those agreements are currently duplicated configuration, not one mechanically derived production graph. Anneal's normal Nix packages use static `rustDate = "2026-05-31"` and `leanVersion = "v4.30.0-rc2"`. A separate `packages.test-ifd` experiment reads metadata from the unpacked Aeneas archive, but only the Lean version is actually discovered from Aeneas. Its Rust fields are copied from Anneal's own static `rustDate` and then read back. The experiment also reuses the already-declared fixed-output hashes instead of discovering new artifact identities. A future update can therefore make Anneal's static Rust or Lean selection disagree with the Aeneas release unless the coupling is checked explicitly.

Anneal also has a distinct Cargo dependency on Charon's repository-local tag `nightly-2026.06.03`. `anneal/Cargo.lock` resolves that tag to `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, not Aeneas's `a535e914…` pin. The two commits both report Charon version `0.1.210`; the later commit is 15 commits ahead. Current native corpus evidence establishes that this independently locked library is not the Charon executable used by the ordinary installed-toolchain path at the examined pipeline boundary. It remains a separate coupling edge that must be reconsidered if Anneal starts using `charon_lib` for live translation or LLBC processing.

The durable identity model is therefore a graph of exact source revisions, release-asset digests, toolchain channels, manifest-resolved dependency revisions, and platform-specific fixed-output hashes. Matching date strings or package versions are useful labels, but they are not sufficient compatibility evidence.

No fresh Nix, Rust, Charon, Aeneas, Lean, or Lake execution was performed for this report. The graph below is reconstructed from exact current Anneal source, exact upstream pins/manifests, and already-published corpus evidence for the repository-local tag relationship.

## Applicability

The primary Anneal subject is `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. This report describes the version-selection and artifact-coupling structure visible in that source revision and the exact upstream revisions selected by it.

The graph has three layers that should remain distinct:

1. **Anneal runtime/archive graph.** `anneal/flake.nix` chooses the Aeneas release asset, Rust distribution date, Lean distribution version, Mathlib cache inputs, and auxiliary archive tools used to construct the installed omnibus archive.
2. **Aeneas source/release graph.** Aeneas pins the Charon source used for its release and carries its own Lean toolchain and Lake dependency manifest.
3. **Anneal Cargo build graph.** `anneal/Cargo.toml` independently depends on Charon's repository-local nightly tag, which resolves to a different Charon commit.

This report is about identity and coupling. It does not repeat the full Aeneas/Charon compatibility analysis, artifact packaging anatomy, Nix fixed-output semantics, host-platform support matrix, or end-to-end trusted-base argument. Those are neighboring corpus subjects.

The installed archive graph is also distinct from the current default remote-install metadata in `anneal/Cargo.toml`. At this revision, those Exocrate URLs and hashes remain explicit placeholders. `setup --local-archive` and the Nix-built CI/test archive exercise the real archive shape, but this report does not claim that an unconfigured default `cargo anneal setup` already names a production remote archive.

## Findings

### The ordinary Anneal archive starts from three top-level version choices

`anneal/flake.nix` defines three principal selections:

```text
Aeneas release: nightly-2026.06.03
Rust date:      2026-05-31
Lean version:   v4.30.0-rc2
```

The Aeneas release is fetched as one of four platform-specific `aeneas-{target}.tar.gz` assets. Each platform has its own fixed-output hash. Rust and Lean are fetched separately into standalone toolchain derivations, also with platform-specific fixed-output hashes.

The resulting omnibus staging tree has three top-level directories:

```text
aeneas/
lean/
rust/
```

This is a material architectural fact: the Aeneas archive does not itself supply the Rust and Lean distributions installed alongside it. Anneal assembles those distributions independently and relies on their versions being compatible with the Aeneas release.

Basis: current Anneal **source** in `anneal/flake.nix`.

### The selected Aeneas release pins Charon `a535e914…`

The Aeneas release tag `nightly-2026.06.03` resolves to `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

At that source revision, `charon-pin` names:

```text
a535e914f74db4fd9e6be7048f4233270d8945c0
```

Aeneas's `flake.lock` independently locks its `charon` input to the same revision. The existing compatibility report records the release recipe connection: the release's `charon` and `charon-driver` executables come from that pinned Charon input.

The relationship is therefore:

```text
Aeneas nightly-2026.06.03
  -> Aeneas ac9f1bc…
     -> Charon a535e914…
```

This is stronger than inferring Charon from the shared nightly date. The exact Charon commit is explicitly pinned by the Aeneas source.

Basis: pinned Aeneas **source** plus existing current-corpus **source synthesis** for release packaging.

### Aeneas's Charon pin selects Rust `nightly-2026-05-31`

At Charon `a535e914…`, `rust-toolchain` selects:

```text
nightly-2026-05-31
```

and requests `rustc-dev`, `llvm-tools-preview`, `rust-src`, and `miri`.

Anneal independently sets:

```nix
rustDate = "2026-05-31";
```

and uses that date to fetch its packaged Rust sysroot. Thus the source-defined runtime pair currently agrees:

```text
Aeneas ac9f1bc…
  -> Charon a535e914…
     -> Rust nightly-2026-05-31

Anneal 41f5b37…
  -> Rust nightly-2026-05-31
```

The equality is **derived** from two independently stored selectors. It is not produced by Anneal reading Charon's `rust-toolchain` in the ordinary build path.

Basis: pinned Charon **source** + current Anneal **source**.

### Aeneas and Anneal independently select Lean `v4.30.0-rc2`

Aeneas's checked-in `backends/lean/lean-toolchain` contains:

```text
leanprover/lean4:v4.30.0-rc2
```

Anneal independently sets:

```nix
leanVersion = "v4.30.0-rc2";
```

and downloads that Lean release directly.

The selected Lean source revision is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, as established elsewhere in the current reference corpus.

Again, the current equality is duplicated state:

```text
Aeneas ac9f1bc…
  -> Lean v4.30.0-rc2

Anneal 41f5b37…
  -> Lean v4.30.0-rc2
```

A change to either side requires explicit revalidation until the production path derives one selector from the other.

Basis: pinned Aeneas **source** + current Anneal **source** + current corpus identity for the Lean tag.

### Aeneas's Lake manifest fixes Mathlib and its transitive graph

At `ac9f1bc…`, `backends/lean/lake-manifest.json` resolves the direct Mathlib input `v4.30.0-rc2` to:

```text
mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6
```

The same manifest records exact revisions for the inherited Lake packages used by that Aeneas Lean project:

| Package | Resolved revision | Manifest input |
| --- | --- | --- |
| `plausible` | `86210d4ad1b08b086d0bd638637a75246523dbb8` | `main` |
| `LeanSearchClient` | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` | `main` |
| `importGraph` | `cdab3938ccabbdb044be6896e251b5814bec932e` | `main` |
| `proofwidgets` | `2db6054a44326f8c0230ee0570e2ddb894816511` | `v0.0.98` |
| `aesop` | `f0c6e183ea26531e82773feb4b73ab6595ca17a5` | `v4.30.0-rc2` |
| `Qq` | `1cc7e819b9b9bc1e87c9edcccb62e0269e00a809` | `v4.30.0-rc2` |
| `batteries` | `5c57f3857ba81924a88b2cdf4f062e34ec04ff11` | `v4.30.0-rc2` |
| `Cli` | `13567aed1ac4f12aea9484178e07e51f8c9f7658` | `v4.30.0-rc2` |

Anneal's Mathlib-cache path does not reconstruct this dependency graph from a separate hand-written list. `packages.aeneas-metadata-files` extracts Aeneas's `lakefile.lean`, `lake-manifest.json`, and `lean-toolchain`; `packages.mathlib-cache-download` uses those files when invoking Lake's cache tooling.

Thus the Lake dependency graph is more tightly coupled to the Aeneas release than the top-level Rust and Lean distribution selectors are.

Basis: pinned Aeneas **source** + current Anneal **source**.

### Cache artifact identity adds platform-specific state on top of the source graph

The manifest revisions above identify source packages. Anneal separately pins a platform-specific fixed-output hash for `mathlib-cache-download`.

Those two identity layers answer different questions:

- the manifest says **which source revisions** constitute the Aeneas Lean dependency graph;
- the fixed-output hash says **which downloaded cache/package-tree bytes** Anneal accepted for one platform.

A source-compatible manifest update can still change the expected cache bytes. Conversely, preserving a cache hash does not replace the need to know which source graph it represents.

The same distinction applies to the Aeneas, Rust, and Lean release assets: version selectors describe intended upstream versions; platform hashes identify the exact fetched bytes accepted by the current Nix derivation.

Basis: current Anneal **source**; distinction is **derived**.

### `packages.test-ifd` does not make the ordinary toolchain fully Aeneas-derived

Anneal contains an import-from-derivation experiment named `packages.test-ifd`.

Its input `packages.aeneas-unpacked` reads `backends/lean/lean-toolchain` from the extracted Aeneas release and writes a `metadata.json`. For Lean, this is a genuine derivation:

```text
Aeneas archive
  -> backends/lean/lean-toolchain
     -> metadata.json lean-toolchain
        -> dynamicLean version selector
```

The Rust fields look similar, but they have different provenance. `aeneas-unpacked` sets:

```text
RUST_DATE=${rustDate}
```

where `rustDate` is already Anneal's static Nix binding. `test-ifd` then reads that value back. It does not inspect the Aeneas archive's top-level `rust-toolchain` or Charon's source pin to discover Rust.

The experiment also passes the ordinary `rust-toolchain.outputHash` and `lean-toolchain.outputHash` into its dynamically constructed derivations. It therefore does not discover fixed-output identities for a newly discovered version.

Finally, the normal `packages.rust-toolchain` and `packages.lean-toolchain` definitions continue to use the static top-level bindings directly. The IFD package is a verification experiment, not the production source of truth.

Basis: current Anneal **source**. The distinction between discovered and round-tripped metadata is **derived** from the data flow.

### Anneal's Cargo graph selects a second, different Charon commit

`anneal/Cargo.toml` independently declares:

```toml
charon_lib = {
    package = "charon",
    git = "https://github.com/AeneasVerif/charon.git",
    tag = "nightly-2026.06.03",
    default-features = false
}
```

`anneal/Cargo.lock` resolves that dependency to:

```text
0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1
```

That is not Aeneas's `a535e914…` Charon pin. Git ancestry shows `0c91ca1…` is 15 commits ahead. Both revisions declare Charon package version `0.1.210`.

The resulting graph therefore contains two different Charon identities:

```text
Aeneas release path
  -> Charon a535e914…  (version 0.1.210)

Anneal Cargo dependency
  -> Charon 0c91ca1…  (version 0.1.210)
```

A shared release-label date and shared semantic version do not collapse those nodes.

The existing native compatibility report establishes that, at the examined Anneal pipeline boundary, the ordinary installed-toolchain path uses the Aeneas-bundled Charon and does not currently create an executing cross-revision LLBC boundary through the independent library. This report preserves that boundary rather than treating the extra Cargo dependency as proof of a runtime mismatch.

Basis: current Anneal **source/lockfile**, Git ancestry, pinned Charon **source**, and current-corpus compatibility evidence.

### `default-features = false` makes the independent library edge materially different from the Charon driver edge

Both exact Charon revisions declare package version `0.1.210`. Charon's manifest makes its `rustc` feature part of the default feature set and documents that this feature hooks rustc-internal APIs; disabling default features permits the library to be compiled without that rustc-private driver integration.

Anneal declares `charon_lib` with `default-features = false`. That dependency is therefore not equivalent to “Anneal compiles a second Charon driver against another Rust nightly.” It is a library-source coupling edge.

The Aeneas release's `charon` / `charon-driver` executables are a different artifact path and remain coupled to Aeneas's Charon/Rust pin. If Anneal later uses the independent library for shared serialized types or LLBC processing, compatibility must be assessed at that actual boundary rather than inferred from the existence of the dependency.

Basis: current Anneal **source** + pinned Charon **manifest** + **derived** distinction.

### The complete current graph has both semantic and packaging-only nodes

For version-coupling purposes, the high-value graph is:

```text
google/zerocopy main 41f5b37…
├─ Aeneas release nightly-2026.06.03
│  └─ Aeneas ac9f1bc…
│     ├─ Charon a535e914… / 0.1.210
│     │  └─ Rust nightly-2026-05-31
│     ├─ Lean v4.30.0-rc2
│     │  └─ Lean 3dc1a088…
│     └─ Lake manifest
│        ├─ Mathlib 5450b53e…
│        └─ eight exact inherited package revisions
├─ Anneal Rust package: nightly-2026-05-31
├─ Anneal Lean package: v4.30.0-rc2
├─ Mathlib cache/package materialization from Aeneas manifest
├─ leantar 0.1.16
└─ Cargo charon_lib tag nightly-2026.06.03
   └─ Charon 0c91ca1… / 0.1.210
```

Anneal's `flake.lock` additionally fixes Nixpkgs at `549bd84d6279f9852cae6225e372cc67fb91a4c1` and flake-utils at `11707dc2f618dd54ca8739b309ec4fc024de578b`. Aeneas's own release-build flake has its own locked Nix inputs.

Those Nix revisions matter for reproducing package construction and tool versions used during derivation. They are not interchangeable with the Rust/Charon/Aeneas/Lean semantic-version graph. A report should state which layer changed rather than calling every lockfile edge a “toolchain compatibility” edge.

Basis: current Anneal and Aeneas **source/lockfiles** + **derived** graph classification.

### Upgrade safety requires checking relationships, not only values

The current values are internally coherent for the ordinary Aeneas executable path, but the configuration has several independent edges.

A disciplined update should re-establish at least these invariants:

1. Resolve the selected Aeneas release to an immutable Aeneas revision and exact platform asset digests.
2. Resolve that Aeneas revision's Charon pin and verify its required Rust toolchain.
3. Compare Anneal's packaged Rust selection with that requirement.
4. Read Aeneas's Lean toolchain and compare it with Anneal's packaged Lean selection.
5. Read Aeneas's Lake manifest and preserve Mathlib plus all resolved transitive revisions.
6. Recompute/revalidate platform-specific fixed-output hashes for Aeneas, Rust, Lean, and Mathlib cache artifacts after any relevant version change.
7. Resolve Anneal's independent `charon_lib` tag/lockfile to its immutable Charon commit and decide whether the library participates in a live compatibility boundary.
8. If the independent library becomes part of LLBC serialization/deserialization or another shared representation boundary, compare exact source/schema behavior or eliminate the split pin rather than relying on `0.1.210`.
9. Keep build-system pins such as Nixpkgs separate from source-language semantic pins, but preserve them when reproducible archive construction matters.

The central rule is that every compatibility assertion should name the edge it justifies. “All components say June 3” or “both Charon commits are 0.1.210” is not such an assertion.

Basis: **derived** from the exact graph above.

## Boundaries

**No fresh execution.** This report did not build the Nix graph, run Charon, translate LLBC, invoke Aeneas, run Lean/Lake, or compare cache bytes.

**No claim that the default remote installer is production-ready.** The current `anneal/Cargo.toml` Exocrate URLs and hashes remain placeholders. The real Nix omnibus graph and local-archive setup tests are sufficient to describe version coupling, but they do not make those placeholder URLs real.

**No complete platform matrix.** Four systems are encoded in current Anneal Nix source, but platform support, linkage fixups, and per-platform release contents are separate checklist subjects.

**No independent Aeneas-release reconstruction.** The Aeneas source revision and release asset identities are grounded in current corpus/source evidence. This report does not prove that independently rebuilding Aeneas at `ac9f1bc…` reproduces the published binaries byte-for-byte.

**No claim that `charon_lib` is harmless forever.** Current corpus evidence says the independent Charon library is not the executing cross-revision LLBC boundary at the examined current pipeline state. If source begins using it for live translation, serialization, or LLBC interpretation, this report's compatibility boundary must be revalidated immediately.

**No claim that semantic version equality implies compatibility.** The two Charon commits are the counterexample inside this very graph: both are `0.1.210` but are distinct revisions separated by 15 commits.

**No automatic production derivation from Aeneas metadata.** `packages.test-ifd` demonstrates a prototype metadata flow. Normal Rust/Lean packages still use static selectors, and the Rust metadata in the experiment is itself sourced from Anneal's static value.

**No claim that source revisions identify cache bytes.** Source manifests and fixed-output artifact hashes are separate identity layers.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

**Anneal source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: Aeneas release selection; static Rust/Lean selectors; platform mappings and hashes; Mathlib metadata/cache materialization; omnibus assembly; `leantar`; IFD experiment.
- `anneal/flake.lock`, blob `92ac56b0a777d280f0a76e28f163b20ff6fb2003`: Anneal build-system inputs, including Nixpkgs `549bd84d6279f9852cae6225e372cc67fb91a4c1`.
- `anneal/Cargo.toml`, blob `9edee13427fd5e3699abd3709cc9f33d7652873e`: independent Charon tag dependency, `default-features = false`, Exocrate placeholder metadata.
- `anneal/Cargo.lock`, blob `eeaa3f7119369d79b735d8c4836fc08bcc7f7e6d`: immutable resolution of the Charon dependency to `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`.
- `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`: current setup command and local/remote archive installation surface.

**Aeneas source.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`):

- `charon-pin`, blob `06dbe0dbf1d5b7f1e6f2a21889ab6bf770e89de6`: Charon `a535e914f74db4fd9e6be7048f4233270d8945c0`.
- `flake.lock`, blob `d6862b6ef779bf72dd7ec5b787f4e3b97b472a6d`: same locked Charon source plus Aeneas release-build Nix inputs.
- `backends/lean/lean-toolchain`, blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`: Lean `v4.30.0-rc2`.
- `backends/lean/lake-manifest.json`, blob `1a5af703163d8b39f4311aafe22ae171788179ee`: Mathlib `5450b53e…` and exact transitive Lake package revisions.

**Charon source.**

- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0/rust-toolchain`: Rust `nightly-2026-05-31` and requested components.
- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0/charon/Cargo.toml`, blob `8c9936202e7bdbdaaefbc19305363da1ab6c0084`: Charon version `0.1.210`, `charon_lib`, and the rustc-private default feature boundary.
- The same `charon/Cargo.toml` blob occurs at Anneal's independently locked `0c91ca1…` revision. Git ancestry shows `0c91ca1…` 15 commits ahead of `a535e914…`.

**Current reference corpus.**

- `reports/aeneas-charon-compatibility-nightly-2026-06-03`, `REPORT.md` blob `5691d44c19c00a51ec7fcc3ef550d356c6759525`: exact repository-local tag distinction, ancestry, release-asset identities, and current non-executing boundary for the independent Charon library.
- Other current reports establish the Lean tag's exact source revision and the surrounding Aeneas/Lean/package anatomy; this report uses those identities but rechecks the primary current pin files above.

Evidence roles are **source**, **lockfile**, current-corpus **source synthesis**, and **derived** graph relationships. There is no fresh **execution** evidence.

## Revalidation

For another Anneal revision, reconstruct the graph from the roots rather than carrying forward version strings.

1. Read `anneal/flake.nix` and `anneal/flake.lock` at the exact Anneal revision. Record Aeneas release tag plus platform digests, static Rust/Lean selectors and hashes, Mathlib-cache hashes, auxiliary versions such as `leantar`, and Nix build-system revisions.
2. Resolve the Aeneas release to an immutable Aeneas commit. Read `charon-pin`, `flake.lock`, `backends/lean/lean-toolchain`, and `backends/lean/lake-manifest.json`.
3. At the pinned Charon revision, read `rust-toolchain` and the package manifest. Compare the required Rust channel with Anneal's packaged Rust channel.
4. Resolve the Lean release to its immutable source revision and compare Aeneas's Lean selector with Anneal's packaged Lean selector.
5. Preserve the resolved Mathlib commit and every inherited Lake manifest revision. If the manifest changes, treat the Mathlib cache/package materialization as stale until its fixed-output identities are re-established.
6. Resolve `anneal/Cargo.toml` / `Cargo.lock` Charon dependency to its immutable commit. Compare it with the Aeneas Charon pin and inspect current Anneal source to determine whether the library participates in a live semantic or serialization boundary.
7. Inspect `packages.test-ifd` or its successor separately from production packages. For every metadata field, trace whether its value is actually discovered from Aeneas or merely copied from an Anneal static binding.
8. If production is changed to derive toolchain versions from the Aeneas archive, verify that artifact hashes and failure behavior are also accounted for; dynamic version discovery alone cannot produce the expected fixed-output hash for unknown new bytes.
9. Run the smallest execution matrix that corresponds to any changed edge: Charon under the selected Rust sysroot, Aeneas consuming the selected Charon LLBC, and the Aeneas Lean project under the selected Lean/Mathlib graph. Preserve exact commands and artifact identities.

A future automated consistency check can cheaply validate the two current duplicate invariants without rebuilding the world: compare Anneal's `rustDate` with the selected Aeneas Charon's `rust-toolchain`, and compare Anneal's `leanVersion` with Aeneas's `backends/lean/lean-toolchain`. Those checks would not replace full compatibility testing, but they would convert two silent duplicated pins into explicit upgrade gates.
