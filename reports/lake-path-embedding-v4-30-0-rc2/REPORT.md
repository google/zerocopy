# Path embedding in Lake manifests, traces, setup files, and artifacts

## Summary

Lake v4.30.0-rc2 does not have one uniform rule for filesystem paths. Its normal dependency manifest is deliberately relative and relocatable, but Lake also carries absolute runtime paths and persists some of them in build-side metadata. In particular, module `setup.json` files can serialize import-artifact, dynamic-library, and plugin paths; `.trace` files serialize path-bearing input captions and saved logs; and linker response files serialize the concrete object and library arguments passed to the linker.

Those persisted paths do not all participate in build identity. A build trace stores a dependency hash separately from its human-readable input captions and log. Lake also distinguishes `traceArgs`, which affect the dependency trace, from `weakArgs`, which are passed to a compiler or linker without affecting that trace; the source explicitly recommends the weak channel for system-dependent `-I` and `-L` paths. Ordinary artifact-cache mappings similarly serialize content-addressed `ArtifactDescr` values rather than the runtime `Artifact.path`.

The practical result is a split relocation model. Keep manifests relative. Treat setup files and other path-bearing build sidecars as tied to the filesystem topology that produced their paths unless they are regenerated or their validity has been established separately. Trace captions and logs can retain stale producer roots without changing the trace hash. Do not infer that compiler-produced `.olean`, `.ilean`, object, library, or executable bytes are path-free from Lake's orchestration source: that question is format- and tool-dependent and needs an exact-pin execution probe.

Basis: source + historical execution evidence + derived synthesis.

## Applicability

The implementation findings apply to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`. They describe Lake's ordinary manifest, build-trace, module-setup, artifact-cache, compiler, and linker paths at that exact revision. They do not assume continuity to another Lake revision.

The report also examines the historical Anneal V1 relocation remediation merged as `google/zerocopy@64bd6d6f1142022eb9297e880214ceb2d87ef72a` in PR #3450. That evidence is useful because it preserves an Anneal-specific case where upstream Lake trace files contained an absolute build root and Anneal deliberately rewrote it. It is evidence about that historical prepared archive, not execution evidence for every path-bearing surface at the pinned Lake revision above.

No fresh Lean, Lake, Aeneas, Nix, compiler, or linker execution was performed for this report. Source inspection establishes the data flow and persistence mechanisms. Where the conclusion depends on the actual bytes produced by an external tool or on a concrete runtime topology, the report leaves that conclusion open.

## Findings

### Normal manifest identity is relative

Lake's manifest model is designed to represent path dependencies relative to the package containing the manifest. `PackageEntrySrc.path` documents its `dir` that way, and manifest package entries also store configuration and nested-manifest paths as relative package-local paths. During materialization, Lake combines the workspace directory with the recorded relative package directory. When Lake writes a workspace manifest, it writes the packages' relative configuration and manifest paths together with the workspace's relative Lake and packages directories.

This is a stronger property than merely accepting relative paths: the ordinary dependency-resolution path preserves both a relative identity and a current absolute runtime location. `Package` has absolute `dir` and `configFile` fields alongside `relDir`, `relConfigFile`, and `relManifestFile`. The absolute form is useful while Lake is running; the relative form is what the normal manifest machinery carries across roots.

Basis: source.

Consequently, a prepared environment can preserve path-dependency identity across relocation when its relative topology is preserved. This does not prove that every user-authored manifest is relative; the JSON representation can carry a `FilePath`, and this report did not test or establish a rejection rule for manually supplied absolute path entries.

### Module setup files persist filesystem paths

Lean's `ModuleSetup` JSON format contains three path-bearing fields: `importArts`, whose values are arrays of `FilePath`; `dynlibs`, an array of dynamic-library paths; and `plugins`, an array of plugin paths. Lake's module setup job fills the latter two from fetched artifacts' `.path` fields and fills `importArts` from resolved import artifacts. `compileLeanModule` then writes the `ModuleSetup` value to `setup.json` and passes that file to Lean with `--setup`.

There is no relativization step at the serialization boundary. The JSON stores the path values that Lake has already resolved. In the normal workspace model, `Package.dir` is absolute. Lake's default artifact cache is rooted below the package's `.lake/cache`; a cached `Artifact.path` is therefore rooted in the current package/cache location unless an environment override or `useLocalFile` path changes that choice. At minimum, the setup format is capable of preserving producer-root path strings, and the normal absolute runtime model gives those strings a direct route into persisted setup JSON.

Basis: source + derived.

Unlike a trace caption, a setup path is operational input to Lean. A relocated prepared environment therefore cannot treat an old `setup.json` as cosmetic metadata merely because the corresponding artifact content still exists somewhere else. Reuse is sound only when its named paths still resolve correctly, or when Lake regenerates the setup file for the relocated topology.

### Build traces separate identity from path-bearing explanation

`BuildTrace` stores four pieces of information: a caption, nested input traces, a hash, and an mtime. `BuildTrace.compute` obtains the caption with `toString info`, but computes the hash independently. Combining traces mixes the hashes and mtimes; it does not hash the caption. File traces make this distinction concrete: `fetchFileTrace` uses `file.toString` as the caption and the file content hash as the hash.

When Lake writes a `.trace`, `BuildMetadata` stores the combined `depHash`, a serialized tree of `(caption, value)` inputs, output metadata, and the build log as distinct fields. `serializeInputs` uses each nested trace's caption as the JSON key while storing its hash or nested inputs as the value. The build log is also saved and can be replayed when a build is skipped.

Basis: source.

An absolute producer root can therefore survive in a `.trace` input caption or log without becoming part of the dependency hash merely because the string is present. Rewriting such explanatory strings does not, by itself, imply a new dependency hash. This distinction is why a path scan of `.trace` files answers a different question from an up-to-date check: the former finds stale producer identity and diagnostic leakage; the latter primarily compares the recorded dependency hash and artifact state.

Historical Anneal evidence confirms that this case occurred in practice. PR #3450 added a trace-rewrite pass that removes known absolute package/root prefixes from every `*.trace`. Its regression test constructs the exact shape seen upstream: an absolute Aeneas staging root appears both in an `inputs` caption and in a saved log message. The rewrite removes the producer root while preserving the suffix identifying `AeneasMeta/Utils.lean`.

Basis: historical source + historical execution fixture.

### Link response files are another persisted path surface

Lake's linker helpers write response files next to the output. `mkArgs` creates `basePath.rsp` and writes each linker argument into it. Shared-library and executable links then invoke the linker using that response file. The argument list is built from concrete object and library `FilePath` values plus configured link arguments.

Basis: source.

These `.rsp` files are build auxiliaries rather than Lake's dependency identity. The inspected helper does not delete the response file after linking. Thus a successful prepared build can retain concrete producer paths even when the final output is content-addressed elsewhere. If no relink occurs after relocation, the stale response file may be inert; if a relink occurs, Lake recreates it from the current argument set. It should still be included in any audit whose objective is "no producer absolute paths remain in the prepared tree."

### Compiler and linker path arguments are not uniformly hashed

Lake deliberately separates invocation arguments from dependency identity. `buildO` documents `traceArgs` as part of the dependency trace and `weakArgs` as excluded from it; it specifically recommends putting system-dependent `-I` or `-L` options in `weakArgs` so a changed filesystem path does not force a rebuild. `buildLeanO`, `buildLeanSharedLib`, and `buildLeanExe` all preserve that split.

The actual tool invocation includes more path-bearing arguments than the explicit trace argument array. For example, `buildLeanO` adds the Lean include directory as `-I <lean include dir>`, and Lean shared-library/executable links add `-L <Lean library dir>`. Object and library paths are also passed to linkers. These concrete paths are necessary to run the tool, but the wrapper does not simply hash their literal strings as `traceArgs`.

At the configurable library/module layer, Lake passes `weakLeancArgs` separately from `leancArgs`, and `weakLinkArgs` separately from `linkArgs`. The non-weak forms are mixed into the trace in the relevant build paths; the weak forms are invocation-only by design.

Basis: source.

This means "a path changed" is not enough to predict whether Lake will rebuild. The answer depends on where the path entered the build graph: as content-hashed input, trace-bearing configuration, weak configuration, a toolchain location, an object/library location represented by another job's trace, or a purely explanatory caption. Relocation tests should therefore inspect both behavior and persisted strings rather than using either as a proxy for the other.

### Ordinary artifact-cache metadata is path-neutral, but artifacts are not proved path-free

An `ArtifactDescr` identifies an artifact by content hash plus extension and serializes to a relative cache path of the form `{hash}.{ext}`. The runtime `Artifact` structure separately contains a preferred filesystem `path`. For ordinary build outputs, Lake's `ToOutputJson Artifact` instance serializes only `artifact.descr`, not `artifact.path`. Cache output mappings therefore retain content identity while reconstructing local paths below the active cache root at use time.

Basis: source.

This is an important relocation-friendly boundary: the ordinary Lake artifact-cache mapping does not need to preserve the producer's cache-root path. It does not imply that the artifact *bytes* are independent of the producer root. Lake passes concrete source, output, setup, include, library, object, and search-path arguments to Lean, C compilers, and linkers. Whether those tools encode any of those strings into `.olean`, `.ilean`, generated C/bitcode, object files, static/shared libraries, executables, debug information, or other outputs is outside the evidence established by Lake's orchestration source.

Custom targets and custom `ToOutputJson` implementations are another boundary: they may serialize arbitrary JSON and are not covered by the ordinary `Artifact` rule.

### Compiled Lake configuration has a path-neutral trace schema, but its `.olean` payload is unresolved

Lake caches an elaborated Lean `lakefile` under `.lake/config/<package>/`. The associated `ConfigTrace` records package index and name, target platform, Lean toolchain hash, the configuration file's content hash, and Lake options. Its freshness check compares those values and the existence of the compiled `.olean`; the trace schema itself has no workspace-root field.

Basis: source.

The cached `lakefile.olean` is different. It contains the elaborated configuration environment, and arbitrary user configuration can contain path-valued data. Source inspection of the cache wrapper does not establish a generic "no producer absolute paths inside the `.olean`" property. PR #3450 deliberately primed Aeneas' compiled package configuration before freezing a read-only archive, which establishes that this cache mattered operationally for that prepared environment, but not that the compiled module was or was not path-free.

Basis: source + historical source; payload property unknown.

### Implications for a relocatable prepared Anneal environment

The source supports four different treatments rather than one blanket rewrite rule:

1. Preserve relative manifests. Lake's normal manifest machinery already supplies a relocation-friendly dependency identity; Anneal V1's historical remediation likewise generated a locked relative manifest.
2. Regenerate operational path sidecars when topology changes unless reuse has been demonstrated. `setup.json` is consumed by Lean and directly contains path values, so stale paths are potentially semantic.
3. Treat trace captions and saved logs as metadata distinct from the dependency hash. They can retain producer roots even when the build remains up to date. Anneal V1 historically stripped such prefixes to make its prepared archive path-neutral.
4. Verify compiled artifact interiors separately. Content addressing says that identical bytes have identical cache identity; it does not establish that the bytes are independent of the producer path.

Basis: derived from the preceding source and historical evidence.

## Boundaries

**Not examined by fresh execution:** This report did not build the pinned Lean/Lake revision in two roots, relocate a prepared workspace, remove the producer root, or run a byte-level path scan over the resulting tree. The source-level mechanisms above are established; their exact concrete footprint in one Anneal V2 build remains to be measured.

**Unknown:** Whether the compiled `lakefile.olean` for Anneal's exact dependency set embeds the producer root. The `ConfigTrace` JSON schema is path-neutral, but that does not constrain arbitrary values serialized into the compiled configuration environment.

**Unknown:** Which compiler-produced artifacts at this exact toolchain revision contain producer paths. In particular, this report does not establish path freedom or path dependence for `.olean`, `.ilean`, generated C, bitcode, object files, archives, shared libraries, executables, debug information, or platform-specific metadata.

**Configuration-dependent:** `ModuleSetup` serializes the paths it is given. The default package/cache model makes absolute runtime paths common, but environment cache overrides, local-file artifacts, custom targets, and unusual package layouts can change the exact strings.

**Not covered:** Arbitrary user-authored/custom output JSON and logs. The ordinary `Artifact` cache representation is content-addressed and path-neutral; a custom output type may persist paths intentionally.

**Not a claim of semantic safety for text rewriting:** Historical Anneal rewrote trace captions/logs. This report does not generalize that operation to `setup.json`, compiled configuration, response files, or binary artifacts. Those surfaces have different consumers and must be handled according to their semantics.

## Evidence

The primary implementation subject is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). Evidence was acquired on 2026-09-27.

- **Manifest representation and relative path dependency contract — source.** `src/lake/Lake/Load/Manifest.lean`, blob `760eb81419762fb0ab11393e93082930645e2b6d`, especially lines 64–118 (`PackageEntrySrc`, `PackageEntry.toJson`) and 174–196 (`Manifest`).
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Manifest.lean#L64-L118

- **Path dependency materialization — source.** `src/lake/Lake/Load/Materialize.lean`, blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`, especially lines 155–223 and 225–265. Path dependencies retain a relative package directory while runtime package paths are formed below the current workspace root.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L155-L223

- **Workspace manifest writing — source.** `src/lake/Lake/Load/Resolve.lean`, blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`, lines 384–400. Lake writes relative config/manifest paths and workspace-relative Lake/packages directories.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L384-L400

- **Absolute and relative package runtime fields — source.** `src/lake/Lake/Config/Package.lean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`, lines 27–48 and 203–225.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Package.lean#L27-L48

- **Module setup JSON schema — source.** `src/Lean/Setup.lean`, blob `38e7f619e852e8ae17d13c94de35a25d279387b6`, lines 65–75 (`ImportArtifacts`) and 135–167 (`ModuleSetup`).
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Setup.lean#L135-L167

- **Lake population of setup paths — source.** `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`, lines 493–551. The setup job collects import artifacts and maps dynamic libraries/plugins to their `.path` fields.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L493-L551

- **Writing and consuming `setup.json`; response files — source.** `src/lake/Lake/Build/Actions.lean`, blob `5b3ab3cc3e9f45b8c695e31680342acc795004c7`, lines 28–100 and 101–125. `compileLeanModule` writes `ModuleSetup` JSON and passes it with `--setup`; `mkArgs` writes linker arguments into `<base>.rsp`.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Actions.lean#L28-L125

- **Build trace structure — source.** `src/lake/Lake/Build/Trace.lean`, blob `656c991fab8a6475802373224514ec7e73f9b18b`, lines 317–380. Captions, hashes, and mtimes are separate; trace mixing combines hashes independently of captions.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Trace.lean#L317-L380

- **Persisted trace metadata and file captions — source.** `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`, lines 57–77, 125–150, and 390–438. `BuildMetadata` serializes `depHash`, captioned inputs, outputs, and log separately; file trace captions use `file.toString`.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L125-L150

- **Weak versus traced compiler/linker arguments — source.** Same `Build/Common.lean`, lines 814–860 and 905–975. `traceArgs` affect dependency traces; `weakArgs` do not; Lean include/library directories and concrete link inputs are passed to tools as path-bearing arguments.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L814-L860

- **Default cache root — source.** `src/lake/Lake/Config/Workspace.lean`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`, lines 25–30. In the absence of an environment override, the Lake cache is below the package's Lake directory.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Workspace.lean#L25-L30

- **Artifact descriptor versus runtime path — source.** `src/lake/Lake/Config/Artifact.lean`, blob `41d6af1a9aa52d6888d3f245df38b4cd76a4dd5d`, lines 14–47 and 72–94. `ArtifactDescr` serializes a content-addressed relative cache path; `Artifact` separately stores the runtime `path`.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Artifact.lean#L14-L47

- **Ordinary artifact output serialization — source.** `Build/Common.lean`, lines 288–305. `ToOutputJson Artifact` serializes only `artifact.descr`.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean#L288-L305

- **Configuration cache trace — source.** `src/lake/Lake/Load/Lean/Elab.lean`, blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`, lines 166–188 and 232–297. `ConfigTrace` contains package/toolchain/platform/config-hash/options metadata but no root path; the compiled config `.olean` is stored separately.
  https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L166-L188

The historical Anneal evidence is `google/zerocopy@64bd6d6f1142022eb9297e880214ceb2d87ef72a`, merged in PR #3450 on 2026-06-16.

- **Historical remediation — source/history.** PR #3450 records that generated workspaces were changed to use a locked relative manifest and that archive preparation rewrote upstream trace prefixes. The merged `anneal/v2/rewrite-lake-vendor.py`, blob `e61fc992837435a43b3e434ddd3b07aa7d13b48c`, lines 101–126 rewrites package manifest entries to relative path dependencies; lines 145–189 strip recognized absolute prefixes from `*.trace` files.
  https://github.com/google/zerocopy/pull/3450
  https://github.com/google/zerocopy/blob/64bd6d6f1142022eb9297e880214ceb2d87ef72a/anneal/v2/rewrite-lake-vendor.py#L145-L189

- **Historical trace specimen — execution fixture.** `anneal/v2/tests/test_rewrite_lake_vendor.py`, blob `380b6e763d9472070f6a6e85513dc6cb5a43c806`, lines 33–62. The fixture preserves the relevant trace shape: an absolute staging root appears in both a log message and an input caption, and the rewrite removes that root.
  https://github.com/google/zerocopy/blob/64bd6d6f1142022eb9297e880214ceb2d87ef72a/anneal/v2/tests/test_rewrite_lake_vendor.py#L33-L62

## Revalidation

For a source-only revalidation, pin the Lean repository to the exact subject revision and re-check the symbols above. The load-bearing distinctions are: manifest paths remain relative; `ModuleSetup` still serializes path-valued artifacts/libraries/plugins; `BuildTrace` still separates caption from hash; `BuildMetadata` still persists captioned inputs and logs; ordinary `Artifact` output JSON still serializes only the descriptor; and compiler/linker helpers still distinguish weak from traced arguments.

For the unresolved runtime boundary, use a minimal two-package Lake workspace at the exact toolchain pin and preserve the entire build tree before moving it. Choose two distinct absolute roots whose byte strings cannot occur accidentally. Build in the first root, then inventory at least:

- `lake-manifest.json` and nested manifests;
- `.lake/config/**`, including compiled configuration and its trace;
- module `setup.json` files;
- all `*.trace`, `*.hash`, and `*.rsp` files;
- cache output mappings and cached artifacts;
- `.olean`, `.ilean`, generated C/bitcode, object files, archives, shared libraries, and executables.

Search both text and binary files for the producer-root byte string. Record every hit by file type and whether the hit is in an operational input, a caption/log, a response file, or compiled output bytes. Then relocate the prepared tree to the second root, make the producer root unavailable, and rerun the same build with external network denied. Record which files Lake reads, rewrites, rebuilds, or leaves untouched, and compare trace `depHash` values before and after.

A useful second pass should delete or regenerate only the path-bearing sidecars (`setup.json`, traces, response files as appropriate) while leaving content-addressed artifacts intact. That separates "the artifact bytes are reusable" from "the producer's operational metadata is reusable."

Do not close the artifact-interior question from a successful build alone. A build can succeed while stale producer paths remain in diagnostic metadata or unused sections. Conversely, a byte-level path hit does not by itself prove semantic non-relocatability. Record both the string inventory and the observed reuse/rebuild behavior.