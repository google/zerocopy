# Lean identity and module-artifact hashes consumed by Lake at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake does not consume a separate Lean-defined "trace file" or Lean-defined artifact-hash format to decide whether a module build is reusable. The boundary is simpler and more important:

- Lean supplies a **toolchain identity string**: normally its Git hash, obtained from `Lean.githash` when Lake is collocated with Lean or from `lean --githash` otherwise.
- Lake hashes that string into its own `BuildTrace` and mixes it into Lean-dependent build jobs.
- After Lean produces module outputs such as `.olean`, `.olean.server`, `.olean.private`, `.ilean`, `.ir`, `.c`, and optionally `.bc`, Lake computes its own 64-bit content hashes over those files. Lake can persist those hashes in adjacent `.hash` sidecars and wraps them in `Artifact` values whose traces carry the hash and modification time.
- Import dependency propagation uses those Lake-computed artifact traces. In particular, the public, server/private, and meta-facing module outputs can have different hashes, so a change can invalidate only the downstream import classes that consume the changed artifact.

The `.hash` sidecars and module `.trace` file are therefore **Lake state around Lean-produced bytes**, not metadata owned by the Lean object formats. This distinction matters for Anneal cache and prepared-environment designs. Preserving an `.olean` without the matching Lake trace/hash state may force Lake to recompute or rebuild; preserving a `.hash` does not establish that the `.olean` is semantically valid for another Lean binary. Lake's hashes are non-cryptographic `UInt64` values, and `LEAN_GITHASH` can deliberately override the Lean identity used in traces.

No fresh Lean or Lake execution was performed. The report combines pinned implementation source with Lean's checked-in Lake regression test that exercises selective changes to `.olean.hash`, `.olean.private.hash`, `.olean.server.hash`, and `.ir.hash`.

## Applicability

This report applies to the Lake implementation shipped in Lean `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, which is the Lean revision selected by the Anneal toolchain examined here.

"Lean identity" means the Git-hash string exposed to Lake by the detected Lean installation, subject to Lake's `LEAN_GITHASH` override. "Artifact hash" means Lake's `Hash` of the bytes of a Lean-produced output. "Build trace" means Lake's `BuildTrace`, which combines a hash with a modification time and an input tree.

This report complements `lake-state-model-v4-30-0-rc2`. That report explains Lake's general trace-file and freshness model. This report narrows the boundary between Lean and Lake: which identity Lake obtains from Lean, which hashes Lake computes after Lean runs, and how those output hashes feed module import traces.

It does not describe the internal serialization of `.olean` or `.ilean`; those are separate inventory subjects.

## Findings

### Lake turns Lean's Git hash into the toolchain trace

`LeanInstall` stores a `githash` string. When Lake constructs a Lean installation, it uses `Lean.githash` if Lake and Lean are collocated. Otherwise it invokes the detected Lean executable with `--githash`; failure leaves the string empty.

`Lake.Env.leanGithash` chooses either that detected value or the environment-provided `LEAN_GITHASH` override. The source describes the override as a way to replace the Lean version used by a library without rebuilding everything, for example while testing a custom Lean build.

When a build starts, `Workspace.mkBuildContext'` creates `leanTrace` as:

`BuildTrace.ofHash (pureHash ws.lakeEnv.leanGithash)`

The caption also records `Lean.versionStringCore` and the selected Git-hash string, but the trace hash itself is computed from the `leanGithash` string. Build actions call `addLeanTrace` to mix that Lake-owned trace into their dependency trace.

The consequence is precise: Lake's ordinary Lean-toolchain invalidation token at this boundary is the selected Git-hash **string**, not a hash of the Lean executable, sysroot, standard-library `.olean` tree, or compiler configuration. `LEAN_GITHASH` can intentionally substitute a different string.

Basis: **source**.

### The module build dependency trace includes Lean identity before Lean runs

For a module's `leanArts` facet, Lake first fetches module setup and source. It then mixes into the job trace:

1. `addLeanTrace`;
2. the source trace;
3. a trace of Lean options;
4. whether module mode is enabled;
5. the module name;
6. package identity;
7. module Lean arguments;
8. dependency/import traces accumulated while producing setup.

`Module.buildLean` passes that completed dependency trace to `buildAction`. `buildAction` writes the module's Lake `.trace` metadata after a successful Lean build.

Thus the Lean Git-hash trace is one input to Lake's module freshness hash; it is not itself the complete module freshness hash.

Basis: **source**.

### Lean produces module files; Lake computes the content hashes used as artifacts

`Module.buildLean` clears existing output artifacts, runs Lean through `compileLeanModule`, clears cached output hashes, and then calls `Module.computeArtifacts`.

`computeArtifacts` calls Lake's `computeArtifact` for each output. `computeArtifact` obtains the file hash through `fetchFileHash`; because `buildLean` just cleared the sidecars, the post-build path computes the hash from the produced bytes and writes the adjacent `.hash` file. Module outputs include:

- `.olean`;
- `.olean.server` and `.olean.private` when module mode produces them;
- `.ilean`;
- `.ir` for module mode;
- `.c`;
- optional `.bc`.

Lake's artifact-cache path uses the same content hash as the artifact identity. `ArtifactDescr` stores the content `Hash` plus an extension, and the cache-relative artifact path is `{hash}.{ext}`.

The ownership boundary is therefore important: Lean emits the module-output bytes. Lake computes and persists the sidecar hash used for its build/artifact machinery.

Basis: **source**.

### The persisted `.hash` value is a Lake 64-bit non-cryptographic content hash

Lake's `Hash` is a wrapper around `UInt64`. The source contains an explicit TODO to replace the builtin Lean hash with a secure hash. It serializes as 16 lowercase hexadecimal digits.

For binary files, `computeBinFileHash` reads the bytes and hashes the `ByteArray`. Module artifacts are computed with binary hashing; the module-build source explicitly avoids text normalization for these outputs.

Lake writes the value to `<artifact>.hash`. When `trustHash` is enabled, `fetchFileHash` reads and trusts an existing sidecar instead of re-reading the artifact bytes. `--rehash` disables that trust and forces recomputation.

These hashes are suitable as Lake freshness and cache identifiers at this revision. They are not cryptographic integrity commitments and should not be used by Anneal as proof that independently supplied artifact bytes are authentic.

Basis: **source**.

### Module artifacts carry their content hash into downstream import traces

An `Artifact` contains its `ArtifactDescr`—including content hash—plus a preferred path and modification time. `Artifact.trace` turns those fields into a `BuildTrace`.

`Module.computeExportInfo` constructs different import-facing traces from different artifacts. For a module-system module, the ordinary public `artsTrace` mixes the public `.olean` artifact trace; the meta-facing trace additionally includes the IR artifact; other export paths include server/private artifacts as appropriate. Downstream `ModuleImportInfo` values combine direct artifact traces into transitive import traces.

The per-artifact content hash therefore provides a finer invalidation boundary than the whole module-build dependency hash. Lake can rebuild a module once, observe that only one output's content hash changed, and avoid rebuilding consumers that do not depend on that output class.

Basis: **source** + **derived**.

### Checked-in regression tests exercise selective public, private, server, and meta hashes

Lean's pinned Lake test `tests/lake/tests/module/test.sh` reads the actual sidecars after building a generated module.

The test makes four kinds of edits:

- A **public edit** changes `Module.olean.hash`; direct public imports and relevant transitive consumers rebuild.
- A **private edit** keeps `Module.olean.hash` unchanged but changes `Module.olean.private.hash`; ordinary public import consumers remain up to date while `import all`/private consumers that need the private artifact rebuild.
- A **server edit** changes `Module.olean.server.hash` while ordinary direct import consumers remain up to date; consumers that need the broader artifact set rebuild.
- A **meta edit** keeps `Module.olean.hash` unchanged but changes `Module.ir.hash`; meta/import-all consumers rebuild while ordinary public consumers can remain current.

This is checked-in test intent and script logic, not fresh execution evidence from this report. Still, it directly corroborates the source model: Lake treats the content hashes of Lean's distinct output classes as separate dependency signals.

Basis: **source** (checked-in test fixture).

### The module `.trace` and output `.hash` files answer different questions

The module's `traceFile` path is the module path with extension `.trace`. Its `BuildMetadata.depHash` records the combined **input/dependency** hash used to decide whether the Lean build itself is current.

By contrast, `Module.olean.hash` and sibling sidecars record content hashes of individual **outputs**. Those hashes can remain stable for one output while another output changes, as the module regression test expects.

A prepared environment therefore needs to keep two directions distinct:

- input/dependency trace → "does this module build need to run again?";
- output artifact hash → "what bytes did this output contain, and which consumers depend on those bytes?"

Conflating them loses Lake's selective invalidation structure.

Basis: **source** + **derived**.

## Boundaries

- No fresh Lean or Lake command was executed. The report does not claim that the checked-in module test passes in the current automation environment.
- This report does not specify `.olean`, `.olean.server`, `.olean.private`, `.ilean`, or `.ir` binary formats. It only follows their treatment as files and artifacts at the Lake boundary.
- It does not establish that the Lean Git hash is a complete semantic identity for a compiler/toolchain. Lake explicitly allows `LEAN_GITHASH` to override it, and failed external detection can yield the empty string.
- It does not establish that an existing `.hash` sidecar matches its artifact bytes. With hash trust enabled, Lake may trust the sidecar without re-reading the file; `--rehash` is the discriminator for recomputation.
- It does not establish cryptographic collision resistance. Lake's `Hash` is a non-secure 64-bit hash by source definition.
- It does not inventory every module-output consumer or every built-in facet. The report follows the core module build/export path and the checked-in module-system regression test.
- It does not establish cross-machine cache portability, relocation, read-only use, concurrency safety, or offline behavior.
- It does not establish the separate "Lean environment hashing/invalidation" inventory item. Environment-level semantic invalidation inside Lean remains a distinct subject.

## Evidence

All source evidence below is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- **Source:** `src/lake/Lake/Config/InstallPath.lean`, blob `e309253fe8c39aa90ce48de295305d160286a9b1`: `LeanInstall`, `LeanInstall.get`, and the `lean --githash` fallback.
- **Source:** `src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969`: `githashOverride`, environment loading of `LEAN_GITHASH`, and `Env.leanGithash`.
- **Source:** `src/lake/Lake/Build/Run.lean`, blob `afae31b7d20a37e6a505d4dc7a9ce875467faf7e`: `mkBuildContext'` and construction of `leanTrace`.
- **Source:** `src/lake/Lake/Build/Context.lean`, blob `8f2eda8d462334f933f112d7ebc4acd3e9553568`: `BuildContext.leanTrace` and `getLeanTrace`.
- **Source:** `src/lake/Lake/Build/Trace.lean`, blob `656c991fab8a6475802373224514ec7e73f9b18b`: `Hash`, binary file hashing, `BuildTrace`, and trace mixing.
- **Source:** `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: `addLeanTrace`, `.hash` sidecar reading/writing, `computeArtifact`, build metadata, and freshness checking.
- **Source:** `src/lake/Lake/Config/Artifact.lean`, blob `41d6af1a9aa52d6888d3f245df38b4cd76a4dd5d`: `ArtifactDescr`, content-addressed cache paths, `Artifact`, and `Artifact.trace`.
- **Source:** `src/lake/Lake/Build/ModuleArtifacts.lean`, blob `9863290328250c33d9933b1569387d96ec244da8`: per-output artifact descriptions for `.olean`, server/private oleans, `.ilean`, IR, C, bitcode, and archives.
- **Source:** `src/lake/Lake/Config/Module.lean`, blob `f8b938e16fe53ada616364033b8d8353baa733ee`: output paths and the module `.trace` path.
- **Source:** `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`: module dependency-trace construction, Lean invocation, output-hash clearing/recomputation, artifact caching, export/import traces, and selective facet traces.
- **Source:** `tests/lake/tests/module/test.sh`, blob `50aeb17645d5f77296ca718cb5ceeb6db9f54f88`: checked-in regression logic for public/private/server/meta output-hash changes and downstream rebuild selection.
- **Documentation + source:** `src/lake/README.md` at the same revision describes a trace as data, generally a hash, used to determine whether a target is current and says target traces derive from inputs such as source, Lean toolchain, and imports.

No evidence above is fresh **execution**. Statements about the implementation and test fixture are **source** claims. The producer/consumer and cache-design consequences are **derived** from those pinned source relationships.

## Revalidation

For another Lean/Lake revision, first compare these narrow source boundaries:

1. how `LeanInstall.githash` is discovered and whether `Env.leanGithash` still supports an override;
2. how `BuildContext.leanTrace` is constructed;
3. the `Hash` representation and binary-file hash implementation;
4. `fetchFileHash`, `.hash` trust/rehash behavior, and `computeArtifact`;
5. `Module.recBuildLean` / `Module.buildLean` inputs and output-hash lifecycle;
6. `ModuleOutputArtifacts` and export/import trace construction;
7. the module-system regression test's expected public/private/server/meta invalidation behavior.

On a Lean-capable surface, run the pinned `tests/lake/tests/module` fixture. Preserve the verbose build output and the `.trace` plus `.hash` files before and after each public/private/server/meta edit. Add two focused controls:

- rerun one no-change build with the normal trusted sidecars and with `--rehash`, verifying which `.hash` files are re-read versus recomputed;
- set `LEAN_GITHASH` to a controlled alternate value without changing source and observe which Lean-dependent module traces become stale.

Those probes would turn the source-level boundary in this report into execution evidence. They still would not establish semantic or cryptographic equivalence of artifacts that merely share a Lake hash.