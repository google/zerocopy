# Archive timestamp normalization and Lake reuse in Anneal

## Summary

Current Anneal manipulates file modification times for two different reasons that should not be conflated.

First, the Mathlib-cache unpack derivation normalizes the entire unpacked result to `1970-01-01 00:00:00` with the stated goal of keeping that intermediate release archive reproducible. Second, later stages deliberately normalize only Lean source/configuration inputs to the epoch so that Lake `v4.30.0-rc2` running with `--old` sees prebuilt outputs as newer than those inputs. Anneal repeats that second normalization immediately before constructing the final toolchain tar because Nix finalization and staging copies can disturb the intended mtime ordering.

The Lake source explains exactly why the ordering matters. Ordinary reuse first compares the current dependency hash with the saved trace hash. If they match, modification time is irrelevant to freshness except for locating/existence metadata. When the hashes do **not** match and `--old` is enabled, Lake falls back to a modification-time check. `MTime.checkUpToDate` uses a strict comparison: the input/reference time must be **strictly older** than the output time. For Lean module builds, `Module.recBuildLean` explicitly supplies the source file's mtime as that fallback reference.

Therefore, setting source/configuration inputs to the epoch is not evidence that Anneal's rewritten dependency graph is hash-equivalent to the producer graph. It is an intentional compatibility mechanism that makes a hash mismatch tolerable under old mode, provided the corresponding output artifacts remain strictly newer. Lake further labels an mtime-only result `mtimeUpToDate` and treats it as **not cacheable**, which prevents old-mode acceptance from masquerading as a content-addressed cache proof.

This also exposes a sharp validation requirement: if source/configuration inputs and outputs collapse to the same timestamp, old-mode reuse fails because the comparison is strict. Anneal's final timestamp normalization must preserve an ordering, not merely a common timestamp. A future v2 design that wants hash-defined cache validity should remove this dependency on ordering by making prepared state hash-consistent or by using a cache representation whose input identity survives relocation/vendoring.

## Applicability

The Lake behavior is pinned to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). The Anneal construction is pinned to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

The report concerns Anneal's prepared Aeneas/Lean package tree and final omnibus archive. It does not claim that every tar entry has a normalized timestamp or that the final compressed archive is byte-for-byte reproducible; archive byte determinism is a separate subject. It also does not claim that `--old` is equivalent to Lake's ordinary hash-based reuse.

“Source/configuration inputs” below refers to the exact file classes Anneal touches in the relevant commands: `*.lean`, `lakefile.lean`, `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`. Other inputs can participate in Lake target traces and may have their own mtime behavior.

## Findings

### Lake ordinary freshness is hash-first; old mode is a fallback

`SavedTrace.replayIfUpToDate'` ultimately calls `checkHashUpToDate'`. If the current dependency trace hash equals the saved `depHash`, Lake checks only that the requested output exists and reports `hashUpToDate`.

If the hashes differ and old mode is disabled, the result is out of date. If the hashes differ and old mode is enabled, Lake instead calls `oldTrace.checkUpToDate info`. A missing/invalid saved trace can also use the mtime fallback in old mode.

This means a successful `lake --old build` has two materially different interpretations:

- hash match: the saved dependency identity still matches;
- mtime fallback: the hash identity did not establish freshness, but output ordering was accepted.

Anneal's comments explicitly say its vendoring rewrite changes Lake dependency hashes even though source content and cached artifacts came from the same upstream revisions. Its use of `--old` is therefore deliberately aimed at the second case.

Basis: **source** in Lake `Build/Common.lean` and current Anneal `flake.nix`.

### Old-mode freshness requires a strict timestamp ordering

At the pinned Lake revision, `MTime.checkUpToDate info self` reads the output's mtime and returns `self < mtime`. Equal timestamps are not up to date.

`BuildTrace` combines mtimes with `max`, so generic build helpers normally compare an output against the newest mtime represented by their input trace. Some build paths override that reference.

For Lean module compilation, `Module.recBuildLean` computes `srcTrace` for the module source and passes `oldTrace := srcTrace.mtime` to both writable-cache and non-writable-cache saved-trace checks. When hash reuse fails, old mode therefore asks whether the module output is newer than the module source mtime.

The strict inequality is operationally important for archive preparation. Setting both source and output to the same epoch does not create a reusable old-mode module result. The source must be older than the output used for the check.

Basis: **source** in Lake `Build/Trace.lean`, `Build/Common.lean`, and `Build/Module.lean`.

### Anneal's intermediate Mathlib normalization serves archive reproducibility, not old-mode ordering by itself

`packages.mathlib-cache-unpacked` expands every downloaded `*.ltar` into its output and then runs:

```text
find $out -exec touch -h -d "1970-01-01 00:00:00" {} +
```

The adjacent source comment says this keeps the release archive reproducible. This operation assigns the same epoch timestamp throughout that derivation output.

By itself, that all-tree normalization cannot satisfy a strict “input older than output” old-mode predicate. Its role is different: it removes timestamp variation from the intermediate unpacked cache result.

Later stages copy this material into a new derivation and establish a fresh ordering for old-mode use.

Basis: **source** in current Anneal `anneal/flake.nix`; the distinction from old-mode ordering is **derived** from Lake's strict comparison.

### Before the verification build, Anneal resets only source/configuration inputs to the epoch

The `aeneas-compiled` derivation rewrites Git dependencies into final vendored path dependencies. The flake comments record the consequence: the rewrite changes Lake dependency hashes even though source and cached artifacts derive from the same upstream revisions.

Anneal then resets selected source/configuration file mtimes to the epoch:

```text
*.lean
lakefile.lean
lakefile.toml
lake-manifest.json
lean-toolchain
```

and runs `lake --old build`.

The source comment states the intended invariant directly: these rewritten inputs should be older than the already-unpacked cache artifacts so Lake accepts the cache rather than deleting it and attempting to rebuild Mathlib inside the Nix sandbox.

This is a compatibility assertion about temporal ordering. It is not a content-hash equivalence assertion. If the actual copied output artifacts are not strictly newer than the normalized inputs on a platform/filesystem, Lake's source predicts that the fallback will fail.

Basis: **source** in current Anneal `flake.nix` plus pinned Lake mtime logic; the failure condition is **derived**.

### Anneal re-establishes the ordering after final staging

The final `omnibus-tar` derivation copies the prepared Aeneas tree, Lean toolchain, and Rust toolchain into `$TMPDIR/dist_staging`. Immediately before creating the tar, it again touches only the Aeneas source/configuration file classes above to the epoch.

The source comment gives the reason: Nix store finalization and the staging copy can collapse file mtimes in the final archive. Anneal wants generated v1 workspaces to be able to use `lake --old` against the installed archive without repairing mtimes at setup time.

Repeating the touch here is therefore not redundant with the earlier intermediate derivation. The earlier ordering can be lost at a copy/finalization boundary; the second normalization reconstructs the intended “inputs old, prepared outputs newer” relation at the artifact that users actually install.

The report records Anneal's documented rationale. It does not independently measure Nix's timestamp transformation on each supported platform.

Basis: **source/documented rationale** in current Anneal `flake.nix`; Lake's required ordering is **source**.

### Mtime-only acceptance is deliberately non-cacheable

Lake's `OutputStatus` distinguishes `hashUpToDate` from `mtimeUpToDate`. `OutputStatus.isCacheable` returns false for `mtimeUpToDate`.

When a writable artifact cache is enabled, `buildArtifactUnlessUpToDate` uses that distinction: an output accepted only by mtime is not promoted into the cache as if it were a hash-validated result. `Module.recBuildLean` follows the same pattern when its saved result was accepted by the mtime fallback.

This is an important trust boundary for Anneal. `lake --old` can preserve/use a prepared output across a known hash mismatch, but Lake does not treat that success as proving the output corresponds to the current hash identity.

Basis: **source** in Lake `Build/Common.lean` and `Build/Module.lean`.

### Timestamp normalization and archive reproducibility are separate contracts

Anneal has at least two timestamp policies:

1. normalize an entire intermediate unpacked cache tree to reduce nondeterministic timestamp variation; and
2. normalize only selected source/configuration inputs to establish old-mode freshness ordering.

Those policies can coexist, but they prove different things. The first is one input to reproducible archive construction. The second deliberately creates *different* timestamp classes—old inputs and newer outputs—because equal mtimes would defeat Lake's old-mode check.

Consequently, a future report on byte-reproducible toolchain archives must inspect tar metadata, file order, permissions, compression, remaining output mtimes, and host/platform effects independently. It cannot infer reproducibility merely because some files are touched to the epoch.

Basis: **derived** synthesis from Anneal's distinct touch sites and Lake's strict mtime rule.

## Boundaries

**No fresh archive execution.** The exact final mtimes inside a built Anneal archive were not measured in this investigation. The source defines the intended ordering; an execution probe should confirm it on each supported system.

**No claim that every Lake target uses the module-source mtime fallback.** `Module.recBuildLean` explicitly uses `srcTrace.mtime`. Generic build helpers default to the full dependency trace mtime, and specialized targets may override their old trace. Revalidate the concrete target path when extending the claim beyond Lean module artifacts.

**No hash-equivalence claim.** Current Anneal explicitly documents that vendoring changes dependency hashes. Successful `--old` reuse is weaker evidence than ordinary hash-mode reuse.

**No final-archive reproducibility claim.** The final staging step does not normalize every tar entry to one timestamp. Deterministic tar ordering, ownership/mode metadata, compression determinism, native binaries, and other platform effects remain outside this report.

**No filesystem-resolution assumption.** A filesystem or archive format with coarse timestamp resolution can collapse intended distinctions. Because Lake requires strict `<`, that is a correctness-relevant property for the old-mode workaround.

**No v2 requirement.** Current source labels the final staging manipulation a v1-only workaround/FIXME. A future v2 implementation may choose a different cache-validity strategy.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary Anneal subject: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`:
  - whole-tree epoch normalization after Mathlib cache unpacking;
  - source/configuration epoch normalization before `lake --old build`;
  - documented dependency-hash change after Git-to-path vendoring;
  - repeated source/configuration epoch normalization in final staging;
  - documented v1-only mtime-workaround rationale.

Primary Lake subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/lake/Lake/Build/Trace.lean`, blob `656c991fab8a6475802373224514ec7e73f9b18b`: mtime representation, `MTime.checkUpToDate` strict comparison, `BuildTrace` mtime max composition.
- `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: hash-first freshness, old-mode mtime fallback, `OutputStatus`, non-cacheability of mtime-only reuse, generic build/cache behavior.
- `src/lake/Lake/Build/Module.lean`, source at the same revision: `Module.recBuildLean` passes `srcTrace.mtime` as the old-mode fallback reference for module output reuse.

Relevant existing corpus context includes `reports/lake-state-model-v4-30-0-rc2` and the source-grounded module-invalidation report/candidate. They provide the broader build-trace model; this report isolates Anneal's timestamp manipulation and its precise old-mode consequence.

Evidence roles are **source**, **documentation/source-comment rationale**, and **derived**. There is no fresh **execution** evidence.

## Revalidation

The cheapest source revalidation after either Anneal or Lake changes is:

1. inspect every `touch`/timestamp-normalization command in Anneal's build and staging pipeline;
2. inspect Lake's `MTime.checkUpToDate`, `SavedTrace.replayIfUpToDate'`, and the concrete target's supplied `oldTrace`;
3. confirm whether an mtime-only result remains distinct from and non-cacheable as hash reuse; and
4. confirm which source/configuration file classes the archive intends to age.

For the exact current revision, build one archive on each supported host platform and preserve a compact timestamp manifest containing path, type, mtime, and relevant Lake trace/output identity for:

- one rewritten `.lean` source;
- its `.olean`, `.ilean`, trace, and hash sidecars;
- one package `lakefile.lean` or `lakefile.toml`;
- the corresponding compiled package configuration `.olean`/trace;
- one unpacked Mathlib artifact; and
- the same files after final tar extraction.

Then run `lake --old --no-build build` or another no-build check against the extracted archive. Verify that every old-mode-reused output is strictly newer than the fallback input mtime and that no setup-time timestamp repair occurs.

Add a negative fixture that deliberately makes a source and output mtime equal. The pinned Lake source predicts the old-mode check will reject it. This fixture cheaply protects against future archive/staging changes that accidentally collapse the timestamp ordering.

Finally, run the same generated workspace in ordinary hash mode. If it succeeds without rebuild and with current hashes matching, the mtime workaround is no longer carrying correctness for that path and can be considered for removal rather than preserved by inertia.
