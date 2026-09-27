# Lake trace relocation and rewrite boundaries at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), a Lake `*.trace` filename does not identify one uniform data format or one uniform class of path strings.

Ordinary build traces use `BuildMetadata`. Lake stores the build's dependency hash in `depHash`, while it stores the dependency tree's human-readable captions in `inputs` and the saved build messages in `log`. The core freshness path compares the current dependency hash with `depHash`; it does not recompute that hash from the saved captions or log. An absolute producer path can therefore remain in an input caption or saved log without, by itself, making the build stale. Rewriting only those explanatory strings can preserve hash-based build identity, although it changes audit text and replayed diagnostics.

That narrow result does **not** make arbitrary textual rewriting of every `*.trace` safe. `BuildMetadata.outputs` is operational cache state: when the dependency hash matches, Lake can resolve artifacts from the saved output description. Separately, compiled Lean package configurations use a different `ConfigTrace` format in files named `*.olean.trace`. Its `options` map is not merely explanatory; when a configuration trace becomes stale and reconfiguration was not explicitly forced, Lake reuses the persisted options to elaborate the configuration again. A blanket path substitution that reaches either an operational `outputs` value or a path-valued configuration option can therefore change later behavior.

The Anneal remediation examined here, at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, performs textual prefix substitution over every UTF-8 file selected by `rglob("*.trace")`. Its preserved unit test demonstrates the intended narrow case: an upstream Aeneas staging root appears in a build-trace input caption and saved log, and the rewrite removes that root while retaining the relative suffix. The test does not establish generic safety for `outputs`, `ConfigTrace.options`, or any future trace schema. The glob also does not select Lake's `*.trace.nobuild` files.

The resulting relocation rule is narrower than “rewrite trace paths.” A prepared tree may retain producer-root text in `BuildMetadata.inputs` or `log` without changing the saved `depHash`, but whole-environment relocation still depends on the current dependency trace, output artifacts, setup files, compiled package configuration, and other state. If a path-scrubbing transformation is required, the evidence supports a schema-aware, field-limited transformation rather than an undifferentiated byte rewrite of all `*.trace` files.

Basis: pinned source + historical Anneal source/test + derived synthesis. No fresh Lean or Lake execution was performed.

## Applicability

The Lake findings apply to the implementation shipped in Lean `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. They concern two Lake trace families at that exact revision:

- ordinary build traces represented by `Lake.BuildMetadata`; and
- compiled Lean package-configuration traces represented by `Lake.ConfigTrace` and stored beside a cached `lakefile.olean` as `*.olean.trace`.

The Anneal rewrite findings apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, specifically `anneal/rewrite-lake-vendor.py`, its unit test, and the Nix archive-preparation call site in `anneal/flake.nix`. That code is historical evidence about one path-neutralization strategy. It is not part of Lake's contract and does not define what Lake itself promises to support.

“Relocation” in this report means moving a prepared filesystem tree to a different root while trying to preserve reuse of its prepared Lake state. “Rewrite” means changing producer-root strings already serialized into trace files. These are related but distinct questions: a trace may contain a stale producer path yet still be hash-current, and rewriting a trace may leave a different relocation blocker untouched.

This report complements the existing reference reports on Lake path embedding, read-only/offline/concurrent use, state modeling, and Lean/Lake trace hashes. It narrows a remaining question those reports intentionally leave open: which persisted trace strings participate in Lake's behavior and which are explanatory, and therefore what a trace-rewrite pass may safely assume.

## Findings

### `BuildTrace.caption` and `BuildTrace.hash` are independent state

`BuildTrace` contains four fields: a `caption`, child `inputs`, a `hash`, and an `mtime`. `BuildTrace.compute` derives the caption with `toString info`, computes the hash through the `ComputeHash` instance, and obtains modification time separately. `BuildTrace.mix` preserves one caption, appends another trace to the input tree, mixes the hashes, and takes the maximum mtime.

A caption is therefore not the serialized form from which Lake later reconstructs the hash. A file-backed trace can, for example, use an absolute file path as its caption while its hash reflects the file contents. Changing the caption string after the fact does not imply a corresponding hash change.

Basis: **source**. `src/lake/Lake/Build/Trace.lean`, blob `656c991fab8a6475802373224514ec7e73f9b18b`.

This separation is the foundation for the narrow safe case in path rewriting: some producer-root strings are labels for already-computed trace nodes rather than build-identity inputs themselves.

### Ordinary build trace files persist identity, explanation, outputs, and log separately

`BuildMetadata` stores:

- `depHash`, the combined dependency hash;
- `inputs`, an array of caption/JSON pairs derived from the input trace tree;
- optional `outputs`;
- `log`; and
- `synthetic`, which distinguishes a trace synthesized from cache restoration from an ordinary successful build.

`serializeInputs` uses each child `BuildTrace.caption` as the stored label. The value is either the child hash or a recursively serialized child-input tree. `BuildMetadata.ofBuildCore` assigns `depHash := depTrace.hash` separately from those serialized captions.

When Lake checks whether an existing build is current, `SavedTrace.replayIfUpToDate'` compares the newly computed `depTrace.hash` with the saved `data.depHash` and checks that the output exists. If the result is current, it replays `data.log`. The core check does not compare the saved `inputs` captions with the new captions.

Basis: **source**. `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`.

The direct consequence is limited but useful: producer-root text inside a saved input caption or log does not, by itself, cause a hash-based rebuild. Such text can survive relocation as stale explanatory metadata while the build remains current, provided the newly computed dependency hash is unchanged and the relevant output still exists.

### Rewriting `inputs` captions is different from rewriting the saved log

Both fields are outside the saved dependency hash, but they have different observable roles.

The saved `inputs` tree preserves why Lake computed a dependency hash. In the core freshness path, it is not the value compared with the current trace. Rewriting a path prefix in a caption therefore changes explanation and auditability rather than the hash comparison itself.

The saved `log` is actively replayed when an output is accepted as current. Rewriting a path in `log` can therefore change user-visible diagnostics or informational output on a later invocation even though the build does not rerun. A scrubbed log may be preferable for a relocatable archive, but it is still a mutation of observable provenance rather than a semantically invisible byte edit.

Basis: **source** + **derived** from `BuildMetadata` serialization and `SavedTrace.replayIfUpToDate'` in `src/lake/Lake/Build/Common.lean`.

A rewrite can also collapse two distinct producer captions to the same relative-looking caption. That still need not change `depHash`, but it can make the saved trace tree less discriminating for a future human or `--explain`-style diagnostic workflow. Path neutrality and provenance fidelity are therefore separate goals.

### `BuildMetadata.outputs` is operational state and cannot be treated like a caption

A build trace's `outputs` value can be consumed later. `getArtifactsUsingTrace?` first checks that the saved `depHash` equals the requested input hash. If it does, and `outputs` is present, Lake passes that JSON to the target-specific `ResolveOutputs` implementation. A successful resolution can also repopulate Lake's local input-to-output cache mapping.

For the built-in `Artifact` case, `ToOutputJson Artifact` serializes the artifact descriptor rather than its runtime path. That is relocation-friendly. It is not a general guarantee about every target: `ResolveOutputs` is type-specific, and `BuildMetadata.outputs` is deliberately opaque JSON at the trace-format layer.

Basis: **source**. `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`, including `ToOutputJson Artifact`, `getArtifactsUsingTrace?`, and `ResolveOutputs`.

A generic textual path replacement over the entire JSON document therefore crosses an operational boundary. It is safe only if the transformation has established that the particular `outputs` schema either cannot contain the matched path or is intentionally being migrated with matching semantics. “The path occurs in a `.trace` file” is not enough evidence.

### `*.olean.trace` is a different schema whose persisted options can affect future elaboration

Lean-authored package configurations use a separate trace format. `ConfigTrace` contains package index, assigned package name, target platform, Lean Git hash, configuration-file content hash, and `options : NameMap String`.

When Lake loads a compiled configuration, it first checks the persisted identity fields against the current package and toolchain. If the cached `.olean` and those identity fields are current, it imports the compiled configuration. If the trace is stale and `-R`/explicit reconfiguration was **not** requested, Lake calls `elabConfig` with `trace.options`, not with the current `cfg.lakeOpts`. Only forced reconfiguration uses the current options directly.

Basis: **source**. `src/lake/Lake/Load/Lean/Elab.lean`, blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`.

This makes `ConfigTrace.options` semantically different from a `BuildMetadata.inputs` caption. The option values are arbitrary strings supplied through Lake configuration options. A path-like option can therefore be rewritten by a blind prefix substitution and later become an input to re-elaboration. No path rewrite of `ConfigTrace.options` is justified merely because the file ends in `.trace`.

The other `ConfigTrace` identity fields are also semantic. Rewriting an accidental textual match inside `name`, `platform`, `leanHash`, or another identity field would alter the validity test. The current Anneal prefixes are path-shaped, so such a match is unlikely in those fields; the important point is structural: the extension alone carries no field-safety contract.

### The examined Anneal remediation rewrites whole UTF-8 trace files, not parsed fields

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `rewrite_trace_prefixes` constructs a set of producer roots and replacements, then walks every `*.trace` under the prepared root and vendored package directories. It reads each UTF-8 file as text and performs ordinary string replacement plus two regular-expression substitutions. If any text changes, it overwrites the file.

The substitution is intentionally broader than a `BuildMetadata.inputs` transformation. It can reach any matching string in the JSON document: input captions, logs, output descriptions, configuration options, or fields introduced by a future trace schema.

Basis: **source**. `anneal/rewrite-lake-vendor.py`, blob `e61fc992837435a43b3e434ddd3b07aa7d13b48c`.

The implementation sorts exact prefixes longest-first, which reduces accidental partial replacement among nested known roots. That ordering does not establish field semantics. The two regexes are broader still: one strips absolute package-root prefixes ending in a recognized vendored package, and one strips any absolute prefix ending in `/backends/lean/`.

### The preserved Anneal test proves the intended caption/log case, not generic trace safety

`test_rewrites_upstream_aeneas_backend_trace_prefix` constructs the shape that motivated one rewrite: a JSON trace contains an absolute upstream Aeneas staging root in a saved log message and in an `inputs` caption. The test runs `rewrite_trace_prefixes` and checks that `/var/lib` and `backends/lean` disappear while `AeneasMeta/Utils.lean` remains.

Basis: **source fixture**. `anneal/tests/test_rewrite_lake_vendor.py`, blob `380b6e763d9472070f6a6e85513dc6cb5a43c806`.

That fixture aligns with the `BuildMetadata` safe case above: the changed strings are explanatory/replayed fields, not `depHash` or a cache output mapping. It does not include a complete current `BuildMetadata` object, a `ConfigTrace`, an `outputs` value, or a path-valued configuration option. It therefore cannot support the stronger conclusion that arbitrary matches anywhere in any `*.trace` are harmless.

### Anneal's archive path scan enforces textual neutrality, not semantic equivalence

The Nix archive preparation primes Aeneas package configuration, runs `rewrite-lake-vendor.py --rewrite-traces`, and then fails if any selected `*.trace` still contains a path matching its producer-root regular expression. This is a strong check for one property: the selected trace text must not retain those recognized absolute roots before the archive is copied into its final layout.

The scan says nothing about whether a rewritten trace continues to encode the same operational values. It is therefore a path-neutrality check, not a semantic-equivalence check.

Basis: **historical source**. `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, especially the archive preparation around the configuration primer, trace rewrite, and `TRACE_ABS_RE` scan.

This distinction also explains why a path-free trace archive is not sufficient evidence for whole-environment relocation. Setup files, response files, compiled artifacts, package-local configuration state, manifests, and current dependency hashes are independent relocation surfaces documented elsewhere in the corpus.

### `*.trace.nobuild` falls outside the current rewrite and scan glob

When Lake is invoked in no-build mode and discovers an out-of-date target whose normal trace file already exists, `buildAction` writes a diagnostic trace to `traceFile.addExtension "nobuild"`. For an ordinary `foo.trace`, the diagnostic path is therefore `foo.trace.nobuild`.

The examined Anneal rewrite uses `Path.rglob("*.trace")`, and the Nix path scan uses `find ... -name "*.trace"`. A filename ending in `.trace.nobuild` does not match either pattern. Such a diagnostic trace can therefore retain producer-root captions even when all selected `*.trace` files pass the archive scan.

Basis: **source** + **derived filename matching**. Lake source: `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`. Anneal source: blobs `e61fc992837435a43b3e434ddd3b07aa7d13b48c` and `433fcf5c64da4f51b9fac471f1faf45c1f730cba`.

This report does not characterize the full lifecycle of `.trace.nobuild`; that is a separate inventory subject. The finding here is only about rewrite coverage: the current glob does not include those files.

### A schema-aware rewrite has a much smaller proof obligation

The pinned source supports a practical classification, preserved in `rewrite-field-matrix.json`:

- `BuildMetadata.depHash` is build freshness identity and must remain unchanged unless the dependency identity itself is intentionally changed.
- `BuildMetadata.inputs` captions are outside the core hash check; rewriting them changes explanation/provenance.
- `BuildMetadata.log` is outside the hash check but is replayed, so rewriting it changes later user-visible text.
- `BuildMetadata.outputs` is operational cache state and should not be rewritten generically.
- `BuildMetadata.synthetic` affects replay/fetch action selection and is semantic state.
- `ConfigTrace` identity fields control compiled-configuration reuse.
- `ConfigTrace.options` can feed future re-elaboration and should not be rewritten generically.

Basis: **derived** from the pinned source above.

If relocation requires removing producer-root text, parsing the trace format and limiting edits to fields whose role is understood produces a tractable correctness argument. A whole-file textual pass instead needs a correctness argument for every current and future string-valued field selected by the glob.

## Boundaries

No fresh Lean or Lake process was executed. In particular, this report does not claim that a prepared v4.30.0-rc2 tree with rewritten traces successfully relocates, remains read-only, or avoids every rebuild. Those require an exact-pin execution probe across two roots.

This report does not claim that every string in `BuildMetadata.inputs` is semantically irrelevant to every Lake feature. The core freshness path shown here uses `depHash`; saved input captions remain valuable explanatory data and may feed diagnostic tooling. The narrower established result is that `replayIfUpToDate'` does not derive or compare freshness from those saved captions.

This report does not enumerate every `ToOutputJson`/`ResolveOutputs` pair. Ordinary `Artifact` output JSON is path-neutral at this revision, but a generic statement about all custom targets would require a separate inventory.

The `.trace.nobuild` finding is only a coverage observation. It does not replace the separate investigation of `.trace.nobuild` semantics, lifetime, or consumers.

The Anneal script is historical evidence, not a recommendation to keep that implementation. The report establishes what its current transformation can touch and why its preserved test covers only one safe shape.

No claim is made about adjacent Lean/Lake revisions. Trace schemas, configuration ownership, cache semantics, or rewrite requirements can change independently. Revalidate the exact fields and call paths on any new revision.

The report also does not establish that path scrubbing is necessary for every producer-root occurrence. A stale path in an explanatory caption may be harmless to build identity while still being undesirable for reproducibility, diagnostics, or archive privacy. Those goals should be stated separately.

## Evidence

Primary pinned Lake source at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`):

- `src/lake/Lake/Build/Trace.lean`, blob `656c991fab8a6475802373224514ec7e73f9b18b`: `BuildTrace`, `compute`, `mix`, and hash/time checks. This establishes that captions, hashes, child traces, and mtimes are distinct state.
- `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: `BuildMetadata`, JSON serialization/parsing, `serializeInputs`, trace read/write, `SavedTrace.replayIfUpToDate'`, `replayOrFetchIfUpToDate`, `buildAction`, `getArtifactsUsingTrace?`, `ToOutputJson`, and `ResolveOutputs`. This establishes the freshness role of `depHash`, the replay role of `log`, the operational role of `outputs`, and the `.trace.nobuild` filename construction.
- `src/lake/Lake/Load/Lean/Elab.lean`, blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`: `ConfigTrace` and `importConfigFile`. This establishes the separate `.olean.trace` schema, its validity fields, and reuse of `trace.options` during stale-trace re-elaboration.

Historical Anneal source at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `anneal/rewrite-lake-vendor.py`, blob `e61fc992837435a43b3e434ddd3b07aa7d13b48c`: `trace_prefixes`, `rewrite_trace_prefixes`, and `--trace-prefix`. This establishes whole-file textual rewriting over UTF-8 `*.trace` files.
- `anneal/tests/test_rewrite_lake_vendor.py`, blob `380b6e763d9472070f6a6e85513dc6cb5a43c806`: `test_rewrites_upstream_aeneas_backend_trace_prefix`. This preserves the intended upstream-staging-root fixture in a log and input caption.
- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: archive preparation that primes Aeneas configuration, rewrites traces, and rejects recognized absolute roots still present in `*.trace` files.

Related current reference reports at `google/zerocopy` `refs/heads/reference@b6c1ba9f891840fc95a1de167bc17ebc38f5cf07`:

- `reports/lake-path-embedding-v4-30-0-rc2/` establishes the broader split between relative manifests, path-bearing setup/trace/link metadata, and unresolved compiled-artifact interiors.
- `reports/lake-readonly-relocation-offline-concurrency-v4-30-0-rc2/` establishes the broader prepared-state contract and historical read-only archive evidence while leaving stronger relocation execution claims open.
- `reports/lean-lake-trace-hash-artifacts-v4-30-0-rc2/` separates Lake's input/dependency trace from per-output artifact hashes.

Evidence class: pinned **source**, historical source/test fixture, and **derived** synthesis. There is no fresh **execution** evidence in this report.

## Revalidation

For a source-only revalidation on another Lake revision, inspect these boundaries in order:

1. Find the current `BuildTrace` representation. Verify whether caption, hash, input tree, and mtime remain separate and whether caption text participates in hash construction.
2. Find the current persisted build-trace schema. Record every field and identify which fields are read by freshness checks, replay, cache-output restoration, diagnostics, or other consumers.
3. Follow the exact up-to-date path. Determine whether saved input captions are still explanatory or have acquired a semantic comparison role.
4. Follow saved output restoration. Inventory the `ToOutputJson`/`ResolveOutputs` pairs relevant to the prepared environment and determine whether any serialized output value contains filesystem paths.
5. Find every other file format sharing the `.trace` suffix. In particular, inspect compiled package-configuration traces and determine whether any string field is later reused as configuration input.
6. Inspect no-build trace naming and consumers separately; do not assume `*.trace` matches every Lake trace-related file.

For an exact-pin execution specimen, use two filesystem roots, A and B, and preserve the before/after trace bytes:

1. Build a minimal target under A and record its `BuildMetadata.depHash`, input captions, output JSON, log, and artifact bytes.
2. Move or copy the prepared tree to B while keeping source/artifact contents stable. Make A unavailable. Run the same target and record whether Lake reuses the output, which trace text remains rooted at A, and whether the current dependency hash equals the saved `depHash`.
3. On a copy of the original trace, rewrite **only** input-caption and log path prefixes. Confirm that `depHash`, `outputs`, `synthetic`, and artifact bytes remain byte-identical and that Lake's rebuild decision is unchanged. Record the changed replayed log text explicitly.
4. Construct a target or cache-output case whose saved `outputs` contains an operational path if one exists at the pin. Show that changing that value is either rejected, changes restoration behavior, or is proven irrelevant for that exact output schema. Do not generalize from ordinary `ArtifactDescr` output JSON.
5. Create a Lean package configuration with a path-valued `-K` option. Produce its `.olean.trace`, make the configuration trace stale without forcing `-R`, and confirm that re-elaboration consumes the persisted `trace.options`. Then repeat after a path rewrite and with explicit `-R` to separate persisted-option behavior from current-option behavior.
6. Invoke no-build mode on a stale target with an existing normal trace, preserve the resulting `*.trace.nobuild`, and verify whether any producer-root captions remain outside a `*.trace` scrub/scan.
7. Run the Anneal rewrite utility against copies of each specimen, parse every rewritten file as its actual schema, and diff semantic fields rather than checking only for absence of absolute strings.

Preserve the fixture trees, exact commands, trace JSON, artifact hashes, and a field-by-field before/after diff as report support material if this probe is later executed. A passing path scan alone should not be treated as evidence of semantic equivalence.
