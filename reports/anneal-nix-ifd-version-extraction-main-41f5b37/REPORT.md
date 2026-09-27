# Nix import-from-derivation and toolchain-version extraction in Anneal

## Summary

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, Anneal contains one explicit import-from-derivation (IFD) probe: `packages.test-ifd`. Evaluation interpolates the output path of `packages.aeneas-unpacked` into `builtins.readFile`, reads the generated `metadata.json`, parses it with `builtins.fromJSON`, and uses those values to construct Rust and Lean toolchain derivations.

The probe is narrower than its name can suggest. Only the Lean version is actually discovered from the Aeneas archive: `aeneas-unpacked` reads `backends/lean/lean-toolchain` from the extracted release. The Rust date is still the statically configured `rustDate = "2026-05-31"` from `anneal/flake.nix`; the derivation merely copies that value into `metadata.json` before evaluation reads it back.

The ordinary current toolchain packages do not depend on this IFD path. `packages.rust-toolchain` and `packages.lean-toolchain` use the same static `rustDate` and `leanVersion` bindings directly, and `packages.default` is `aeneas-unpacked`. `packages.test-ifd` is therefore a verification experiment showing that derivation-produced metadata can drive later evaluation, not the authoritative current version-selection mechanism for Anneal's normal bundle.

Under Nix's documented IFD semantics, reading `${unpacked}/metadata.json` during evaluation can force `aeneas-unpacked` to be realized before evaluation can continue. Evaluation therefore acquires a build-time dependency and fails when IFD is disabled with `allow-import-from-derivation = false`.

## Applicability

This report describes `anneal/flake.nix` blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

It covers:

- how `aeneas-unpacked` constructs `metadata.json`;
- which metadata is archive-derived versus statically injected;
- the `packages.test-ifd` evaluation flow;
- the relationship between the IFD probe and the normal Rust/Lean package definitions;
- the evaluator/build boundary implied by Nix IFD.

It does not establish the exact Nix executable version used by every Anneal consumer. IFD semantics are interpreted using versioned Nix reference documentation; the exact current flake does not itself pin the evaluator binary.

The report also does not repeat the fixed-output acquisition analysis. The upstream archive/toolchain hashes and network-materialization boundaries are covered separately by the candidate report for “Nix fixed-output derivations used for upstream archives/caches.”

## Findings

### `builtins.readFile` of `aeneas-unpacked` is the IFD trigger

`packages.test-ifd` defines:

```nix
unpacked = self.packages.${system}.aeneas-unpacked;

aeneasMetadata =
  builtins.fromJSON (builtins.readFile "${unpacked}/metadata.json");
```

`unpacked` is a derivation output, not a source-tree file. Nix documents `builtins.readFile` of a derivation-produced store path as import from derivation: evaluation must realize the required store object before it can inspect the file and continue evaluating the dependent expression.

The `builtins.fromJSON` call is not the operation that creates the build dependency. It parses bytes after `readFile` obtains them. The material boundary is the filesystem read from the derivation output.

Basis: **source** + **documentation**.

### The IFD chain first realizes the Aeneas archive unpacking derivation

`packages.aeneas-unpacked` has the upstream Aeneas release archive as `src`. Its build phase:

1. extracts that archive into `$out`;
2. reads `$out/backends/lean/lean-toolchain`;
3. parses a Lean version string;
4. writes `$out/metadata.json`.

Consequently, evaluation of `packages.test-ifd` may need more than a pure evaluator computation. If the `aeneas-unpacked` output is not already available through the store/substitution path, Nix must realize it before `builtins.readFile` can return the metadata bytes.

The IFD dependency is therefore on a small metadata-producing derivation whose source is already hash-gated by the Aeneas release fetch. It does not require the full compiled Anneal omnibus archive before version extraction can proceed.

Basis: **source** + **documentation**.

### Lean version extraction is genuinely archive-derived

The `aeneas-unpacked` build reads:

```text
$out/backends/lean/lean-toolchain
```

and removes the `leanprover/lean4:v` prefix to construct the JSON field `lean-toolchain`. At the selected Aeneas release, that file contains `leanprover/lean4:v4.30.0-rc2`.

`packages.test-ifd` later assigns:

```nix
leanVersion = aeneasMetadata.lean-toolchain;
```

and passes that value into `fetchLeanToolchain`.

For the IFD probe, the Lean URL/version selector is therefore derived from the contents of the realized Aeneas archive rather than from the top-level `leanVersion` binding.

Basis: **source**.

### Rust version extraction is only round-tripped, not discovered

The same metadata derivation writes:

```text
RUST_DATE=${rustDate}
RUST_VERSION="nightly-$RUST_DATE"
```

where `rustDate` is the Nix-level static binding `"2026-05-31"`.

`packages.test-ifd` reads those JSON fields back as `rustDate` and `rustVersion`, but no Rust version file is inspected from the extracted Aeneas archive. The apparent dynamic Rust metadata therefore originates in the current flake expression itself.

This distinction matters to a future attempt to make Aeneas the source of truth for toolchain selection. The current IFD experiment demonstrates archive-driven Lean selection; it does not yet demonstrate archive-driven Rust selection.

Basis: **source** + **derived** data-flow tracing.

### Dynamic version selection does not mean dynamic hash discovery

After reading metadata, `packages.test-ifd` reconstructs toolchain derivations like this:

```nix
dynamicRust = fetchRustToolchain {
  inherit rustDate;
  sha256 = self.packages.${system}.rust-toolchain.outputHash;
};

dynamicLean = fetchLeanToolchain {
  inherit leanVersion;
  sha256 = self.packages.${system}.lean-toolchain.outputHash;
};
```

The versions flow through the IFD metadata path. The expected output hashes do not. They are copied from the already-declared normal toolchain derivations.

The probe therefore verifies a constrained compatibility property: metadata-derived version selectors can rebuild the same fixed-output declarations under the statically configured expected content identities. It does not solve the bootstrapping question of how to obtain a new expected hash when a newly discovered upstream version changes toolchain content.

Basis: **source**.

### Current normal Anneal packages bypass IFD

The ordinary packages are declared separately:

```nix
packages.rust-toolchain = fetchRustToolchain {
  inherit rustDate;
  sha256 = rustToolchainSha256;
};

packages.lean-toolchain = fetchLeanToolchain {
  inherit leanVersion;
  sha256 = leanToolchainSha256;
};
```

Those bindings use the top-level static `rustDate` and `leanVersion`. Other current bundle derivations consume these normal packages. `packages.default` is `aeneas-unpacked`, not `test-ifd`.

No other `builtins.readFile`/`fromJSON` use matching this metadata flow was found in the current Anneal flake. The current source therefore supports a strong scope statement: `test-ifd` is an explicit experiment/verification package, not a hidden prerequisite of every ordinary evaluation path.

A future refactor could promote this mechanism into normal package selection; this report must be revalidated if that happens.

Basis: **source** + **source-tree search**.

### IFD moves part of dependency discovery from build planning into evaluation

Nix documents IFD as allowing a Nix expression's value to depend on a realized store object's contents. When the evaluator reaches the read, it pauses evaluation until the store object exists, then resumes with the file contents.

For Anneal's probe, the evaluator cannot know the metadata-derived Lean version until `aeneas-unpacked` is available. This introduces a phase dependency:

```text
evaluate test-ifd
    -> need aeneas-unpacked/metadata.json
    -> realize/substitute aeneas-unpacked
    -> read + parse metadata
    -> construct dynamicLean/dynamicRust
    -> finish evaluating the dependent build plan
```

That phase coupling is the main operational consequence of adopting this pattern broadly. It can reduce the amount of duplicated version metadata in the expression, but it prevents evaluation from producing the complete dependent build plan before the metadata producer is available.

Basis: **documentation** + **derived** application to Anneal.

### Disabling IFD makes this probe unavailable even when the design is otherwise pure

The Nix reference documents `allow-import-from-derivation = false` as rejecting expressions that use IFD. Recent Nix documentation further states that the restriction applies even when the required store object is already available.

Thus an environment or service that intentionally disables IFD cannot evaluate `packages.test-ifd` as written. The ordinary current Rust/Lean package declarations do not share that requirement because their versions are static expression values.

This is relevant to CI/evaluation services: “can build Anneal's current toolchain” and “can evaluate the IFD experiment” are distinct capabilities.

Basis: **documentation** + **source**.

### The generated metadata is a deliberately small interface

`metadata.json` has exactly three fields in the current source:

```json
{
  "lean-toolchain": "...",
  "rust-toolchain-date": "...",
  "rust-toolchain-version": "..."
}
```

The IFD consumer reads all three, but only `lean-toolchain` and `rust-toolchain-date` affect reconstructed derivation parameters; `rustVersion` is emitted to the `test-ifd` output text as a diagnostic.

This narrow JSON interface keeps evaluator-visible data small. It also makes the provenance split easy to audit: one field is parsed from the archive, two are generated from the static Rust date.

Basis: **source**.

## Boundaries

**No fresh Nix evaluation or build.** The report traces exact source and versioned Nix semantics. It does not contain an observed `nix build .#test-ifd` transcript.

**No exact evaluator-version claim.** `nixpkgs` selection does not identify the Nix binary used by the caller. The report therefore does not claim a specific Nix release at runtime.

**No archive-derived Rust pin.** The current `metadata.json` Rust fields are generated from the flake's static `rustDate`. Treating them as independently recovered Aeneas metadata would be incorrect.

**No dynamic expected-hash discovery.** The dynamic derivations reuse normal packages' configured `outputHash` values. IFD does not remove the need to update expected hashes when admitted toolchain content changes.

**No claim that IFD is required by the normal current bundle.** Source inspection shows `test-ifd` as a separate package and ordinary toolchain packages use static version bindings.

**No performance measurement.** Nix documentation warns that IFD can impede evaluation/build planning because store objects must be realized during evaluation. This report does not quantify that cost for Anneal.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary implementation source:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`.
  - top-level `rustDate` and `leanVersion`;
  - `packages.aeneas-unpacked`;
  - `packages.rust-toolchain`;
  - `packages.lean-toolchain`;
  - `packages.test-ifd`;
  - `packages.default`.

Nix semantic references:

- Nix 2.23 Reference Manual, “Import From Derivation”: filesystem reads such as `builtins.readFile` of a derivation-produced store path constitute IFD; evaluation realizes the store object before continuing; IFD can be disabled.
- Nix 2.34.7 Reference Manual, “Import From Derivation”: current versioned confirmation of the same evaluator/build boundary.
- Nix 2.21 configuration reference: `allow-import-from-derivation = false` rejects IFD even when the store object is already available.

Preserved support material:

- `metadata-flow.json`: exact producer fields, provenance classification, and consumer mapping.
- `source-map.json`: implementation source and documentation references.

Evidence roles: **source**, **documentation**, and **derived**. There is no fresh **execution** evidence.

## Revalidation

For another Anneal revision, use a narrow data-flow check before broader Nix research.

1. Inspect `packages.aeneas-unpacked` and record every `metadata.json` field and where its value originates.
2. Find every evaluator-time filesystem read whose path contains a derivation output, especially `builtins.readFile`, `import`, `readDir`, or `pathExists`.
3. Trace which reconstructed package arguments come from derived metadata versus static expression bindings.
4. Check whether normal bundle packages now consume metadata-derived values or whether IFD remains isolated to a test package.
5. Check whether expected fixed-output hashes remain static, are themselves metadata-derived, or moved to another source of authority.

A capable execution surface can cheaply discriminate the main operational claims:

```text
nix build .#test-ifd
nix build --option allow-import-from-derivation false .#test-ifd
```

Record the exact Nix version and whether the first evaluation realizes/substitutes `aeneas-unpacked` before completing evaluation. Then compare an ordinary static package such as `.#lean-toolchain` under the same IFD-disabled setting.

To test provenance rather than just capability, change only the archive-carried `lean-toolchain` metadata in a controlled fixture and confirm that the IFD-derived Lean selector changes. Separately change the top-level `rustDate` and confirm that the generated Rust metadata follows it. Do not use production release hashes for a mutated fixture.
