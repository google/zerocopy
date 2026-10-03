# Anneal V1 with immutable SDK imports, native plugins, and live Lean server

## Summary

On the examined macOS arm64 RC2 toolchain, stock Lake can build the local
Anneal V1 fixture against a single immutable Aeneas/Mathlib artifact tree
exposed through an extended Lean sysroot. The root Lake package contains
only local libraries and a target referring to the prebuilt native plugin;
it has no `require aeneas` dependency graph. Positive verification, false and
forbidden-`sorry` controls, native plugin setup/loading, and selected live
server interactions worked under this topology.

This is a validated design candidate, not a production implementation. An
immutable SDK identity must invalidate local outputs when the SDK changes;
the separate [SDK invalidation report](../lean-external-sdk-invalidation-v4-30-0-rc2/REPORT.md)
demonstrates stale proof reuse when that input is absent. Upgrading only the
compiler is insufficient: final 4.30 rejected the tested RC2 artifacts.

## Applicability

The execution subjects are the combination of Lean/Lake
`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, the SHA-identified published
Anneal archive, and local fixture inputs drawn from zerocopy
`79a357870ee0f5a403cf7c7dd43055c0eddbeda2`. The archive's Aeneas tree and
nine path packages were extracted; its additional Lean and Rust payloads
were not extracted for these runs. An existing relocated Nix RC2 runtime
supplied the compiler and Lake. The final 4.30 runtime was used only for the
incompatible-artifact control. See [subject identity](evidence/subject-identity.json).

The omnibus archive is 1,464,207,302 compressed bytes. Its extracted Aeneas
payload contains 1,825,191,796 logical bytes. That exact archive is the
artifact authority here. Its path manifests remove upstream Git revisions;
matching package names do not prove that whole source trees equal upstream
commits. The navigation tests' two source files were separately byte-matched
to Aeneas `ac9f1bc5262a5e4ff1e24ca78617121382202727` and Mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

Commands ran serially on macOS arm64 with 8 GiB RAM and eight logical CPUs,
`LEAN_NUM_THREADS=1`, cache/restoration settings disabled, private consumer
state, read-only shared trees, and resource guards. V1 commands invoked the
original RC2 Lake with `LEAN_SYSROOT` and `LAKE_OVERRIDE_LEAN=true`, selecting
the copied SDK Lean for compilation. Server runs launched the copied SDK
Lean explicitly with `--server`. A separate fresh
native smoke run tested a coherent SDK containing real copies of both small
launchers and ordinary `lake env lean` selection. These are distinct cells;
the coherent launcher pair was not used to repeat the full V1/LSP suite.

## Findings

### Keep external prebuilt packages outside the consumer's Lake graph

**Basis: execution + fixture source + derived.** The SDK view merges
top-level artifact providers from RC2 `lib/lean`, Aeneas
`backends/lean/.lake/build/lib/lean`, and each path package's build library
directory. It consists mainly of symlinks to the immutable providers. The
probe rejects conflicting top-level providers instead of silently choosing
one; this is a limited prototype collision check, not complete installation
validation. The consumer Lakefile declares `Generated` and `Anneal` and an
explicit native plugin target, but no inherited dependency packages.

Lake successfully compiled six local modules: `SdkIdentity`, `Config`,
generated `Types` and `Funs`, `Anneal`, and `Generated`. It obtained external
imports from the SDK sysroot without scheduling Aeneas/Mathlib package build
jobs. The local identity module embeds the archive digest and is imported
by every compilation root in the fixture. A warm `lake build Generated Anneal`
replayed the six local modules in 0.629 seconds; it did not repeat the Specs
audit or server checks. In the smaller native fixture, a source edit
or deleted local OLean rebuilt the local output; an unchanged rerun replayed
it. These are observed timings, not a general performance comparison.

The resulting V1 workspace occupied approximately 3.2 MiB. The primary SDK
view occupied 88 KiB before the coherent launcher variant. Those measured
sizes demonstrate avoiding a per-workspace copy of the approximately
1.8 GiB dependency tree for this fixture; they do not predict arbitrary
project output sizes. The
[selected outcomes](evidence/selected-outcomes.json),
[no-op log](evidence/logs/native-lake-v1-noop.selected.txt), and captured
[view construction](evidence/harness/real_sdk_lake.py) preserve this evidence.

### Supply native plugin metadata explicitly at the root

**Basis: execution + fixture source.** Merely exposing OLeans is not a
complete native/server integration. The root package's `plugins` contains
a `Dynlib` target whose `inputFile artifact false` refers to the immutable
`libaeneas_AeneasMeta.dylib`. The target maps the path to a Dynlib with
`plugin := true`; it does not compile or copy that library. The exact Lake
syntax is preserved in [V1-lakefile.lean](evidence/fixture/V1-lakefile.lean).

`lake setup-file Smoke.lean` returned the native plugin in its JSON, and
macOS dyld logged an actual load of that prebuilt library during the server
run and the separate coherent-view build. The smoke proof uses
`aeneas_saturate`. Its deliberately false counterpart exited 1. Thus this
probe checks native elaboration and plugin propagation, not only an import
that could succeed without exercising the tactic.

The V1 positive `expand_output.foo.spec` audit exited 0 and reported no
axiom dependencies. Adding a `contradiction : False` field to the generated
postcondition exited 1 because its constructor lacked the required field.
Replacing the proof with
`sorry` exited 1 with the expected forbidden-tactic diagnostic. A later
`[sorryAx]` printout in error recovery does not turn that failing command
into an accepted proof. See the preserved
[positive audit](evidence/logs/native-lake-v1-audit.stdout),
[false output](evidence/logs/native-lake-v1-false.stdout), and
[sorry output](evidence/logs/native-lake-v1-sorry.stdout).

### Select the SDK consistently and preserve source roots for the server

**Basis: execution + source.** A symlinked Lean launcher selected the
original installation's sysroot. Copying Lean alone made direct SDK
compilation work, but `lake env lean` still selected the original binary.
Real copies of both Lean (49,968 bytes) and Lake (51,840 bytes) in the SDK's
`bin` made `lake env lean --print-prefix` return the coherent SDK view.
Its fresh Smoke build succeeded and its setup JSON carried the Aeneas
native plugin. Runtime and dependency artifacts were linked/referenced in
place, rather than copied per project. The
[companion report](../lean-external-sdk-invalidation-v4-30-0-rc2/REPORT.md)
preserves the launcher and external-`LEAN_PATH` failure controls.

The first explicit-SDK server run completed initialize/open, returned a
nonnull `⊢ True` goal with empty final diagnostics, loaded the actual native
library, and exited cleanly. The second added `LEAN_SRC_PATH` entries for
the Aeneas backend and all nine archive package source roots. Go to
Definition resolved `aeneas_saturate` to the readable
`AeneasMeta/Saturate/Tactic.lean` region at lines 741–745, and
`Nat.succ_injective` to `Mathlib/Data/Nat/Basic.lean` line 56. An unsaved
`False` edit produced an error; restoring `True` cleared diagnostics and
restored the goal without changing the on-disk source. The first document
version in that navigation run had an informational `#check` message and
a tactic warning; the report does not claim all versions were diagnostic-free.
See [selected LSP messages/results](evidence/lsp-selected.json) and
[loader lines](evidence/logs/native-plugin-load.selected.txt).

At the pinned RC2 source,
[`Lean.Server.Utils.documentUriFromModule?`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lean/Lean/Server/Utils.lean#L181-L201)
searches the source path for `<module>.lean` and resolves real paths before
forming a URI. Lake's
[`augmentedLeanSrcPath`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Workspace.lean#L329-L333)
prepends local library source roots to inherited `LEAN_SRC_PATH`. The
external Aeneas/Mathlib mappings came from those explicit archive source
roots, not the toolchain's `src/lean` fallback.

### Missing or mismatched artifacts fail without consumer repair in the tested SDK cells

**Basis: execution + derived.** A private masked view omitting only
`Aeneas.olean` failed compilation; a missing plugin target failed, and a
private corrupt dylib failed with `slice is not valid mach-o file`. No
shared artifact was deleted to create these controls. The corresponding
instrumented masked-SDK cells observed zero blocked shared mutation attempts
and zero network attempts. This result does not extend to damaged
path-package graphs in the companion report. The final 4.30 compiler against an RC2 AeneasMeta artifact
failed promptly with `incompatible header`. Changing the compiler requires
a compatible artifact closure and native/server validation.

The complete extracted Aeneas tree's before/after inventories were
byte-identical across 28,893 entries, covering file hashes, mode, size,
mtime, and symlink targets. The primary SDK view's 217 entries also matched.
The coherent probe separately compared its view/primary SDK content and
metadata, archive metadata, and selected artifact hashes. This supports
unchanged shared state for the observed experiment sequence; it is not a
universal no-write theorem.

The older published archive also exposed a concrete compatibility boundary:
normal and `--old` path-package consumers attempted to create the absent
dependency-context `.lake/config/aeneas` slot and failed. The archive
contains the `[anonymous]` root config slot instead. Its release preceded
the current producer's June 16 config primer. This observation does not
establish that the current Nix-produced archive fails its own gate. The
[producer-gap record](evidence/producer-gap.json) and
[pinned producer excerpt](evidence/source/producer-primer-and-gate.txt)
preserve that distinction. The SDK route bypasses that package-config graph;
the separate [RC2/final report](../lake-frozen-package-config-ownership-v4-30-0-rc2-v4-30-0/REPORT.md)
tests the newer config ownership behavior on tiny packages.

### Bound resource use and retain incomplete attempts

**Basis: execution.** Selected completed commands peaked at 1,633.2 MiB
of summed sampled process RSS; sampled host free memory stayed at or above
27% and disk at or above 25.97 GiB. Summed RSS may double-count shared
mapped pages. It is not a measurement of peak physical memory. The two LSP
checks completed in 10.843 and 18.921 seconds with sampled peaks 1,152.7 and
1,032.2 MiB. Background host pressure varied, so these are resource bounds
for these cells, not controlled speedup estimates.

Earlier attempts include an enclosing 240-second controller timeout and
four stops at the initial 1.5 GiB RSS cap. The first final-runtime extraction
also hit its selected-byte cap before a later bounded extraction succeeded.
Admission was deferred at low headroom. Later guarded serial proof controls
completed; the interrupted controls are not treated as negative proof
results. [Final-check.json](evidence/final-check.json) retains those stops.

## Boundaries

- **Not examined:** Linux loaders/servers, other architectures, concurrent
  large consumers, arbitrary user libraries, broad V1 integration suites,
  automatic Elan/editor installation selection, or a matching final-4.30
  Aeneas/Mathlib build. No production source changes were made.
- **Not examined:** a real-archive digest swap or automatic publisher
  enforcement of SDK-to-local identity. This integration fixture imported
  `SdkIdentity`, but its archive digest never changed. The companion tiny
  canary tests the invalidation mechanism synthetically.
- **Known not to apply:** selecting final 4.30 while keeping this RC2
  artifact closure; the mismatch control failed. An SDK swap without local
  identity invalidation is also unsafe for reuse, as the companion canary
  demonstrates.
- **Unknown:** the complete publisher/admission checks needed for every
  artifact class and module/source collision. The prototype checks only
  conflicting top-level artifact providers and selected source matches.
- **Evidence limit:** `ps` and nested `sandbox-exec` were unavailable.
  The tracer interposes selected libc mutation/network calls; it is not
  exhaustive syscall tracing or a network firewall. Zero attempts means
  zero observed by that instrumentation. Read-only modes, inventory
  equality, and the absence of external Lake package jobs supply additional
  evidence, not a formal guarantee.

The publication preserves snapshot digests/counts rather than entire
multi-megabyte inventories, and selected LSP messages rather than the large
dyld/progress stream. The offline checker can verify their internal
consistency and retained-file integrity; it cannot reconstruct the omitted
raw inventories or authenticate the original execution.

## Evidence

Evidence was acquired on 2026-10-03. [INDEX.json](evidence/INDEX.json) lists
each retained artifact, its original source SHA-256, the transformed output
SHA-256, and any selection/redaction. `<PROJECT>` and `<HOME>` replace local
filesystem prefixes; they are explanatory placeholders, not runnable paths.
The captured scripts are evidence specimens and require their recorded path
inputs to be adapted before execution. No runtime binaries are included.

Primary source coordinates are:

- zerocopy `79a357870ee0f5a403cf7c7dd43055c0eddbeda2`,
  `anneal/v1/tests/fixtures/expand_output/expected-aeneas.stdout` and
  `expected-anneal.stdout`, `anneal/v1/src/Anneal.lean`, and `flake.nix`
  producer primer/gate. Fixtures and narrow excerpts are preserved here.
- Lean RC2 `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`,
  `src/lean/Lean/Util/Path.lean` (`getBuildDir`, `getSrcSearchPath`),
  `src/lake/Lake/Config/InstallPath.lean` (`findLeanInstall?`,
  `findLakeInstall?`), `src/lake/Lake/Config/Workspace.lean`
  (`augmentedLeanSrcPath`), and `src/lean/Lean/Server/Utils.lean`
  (`documentUriFromModule?`).
- The [SHA-identified release asset](https://github.com/google/zerocopy/releases/download/anneal-toolchains-v0.1.0-alpha.24-27079750833-09497849a10d/anneal-toolchain-macos-aarch64.tar.zst),
  its bundled path manifests and config entry inventory. Upstream Git
  manifest coordinates and the two source-match hashes are preserved in
  `subject-identity.json`; they do not establish a whole-tree source match.

`selected-outcomes.json` preserves commands, outcomes, and resource bounds
for 19 successes and seven expected failures. `lsp-selected.json` preserves
both server outcomes, request responses, final diagnostics by document
version, goal results, navigation URIs/ranges, and observed trace counts.
`snapshot-equality.json` records the full-inventory comparison scope and
digests. `size-and-launcher-identity.json` records allocation measurements
and launcher hashes; `coherent-sdk-results.jsonl` retains the separate
coherent-view run and integrity summary. `harness/guard.py`, `trace.c`, and `lsp_driver.py` preserve the
measurement and server methods; the selector documents evidence reduction.

## Revalidation

Run the cheap offline integrity/consistency check from this report directory:

```console
python3 -B check.py
```

For runtime revalidation, first rerun the companion report's tiny SDK
invalidation probe; it distinguishes a correct local invalidation contract
without importing Mathlib. Then prepare a fresh read-only SDK view from a
checksum-verified compatible archive and runtime, copying both launchers
and linking each unique compiled provider under `lib/lean`. Preserve
matching archive source roots in `LEAN_SRC_PATH`, select SDK paths for
`LEAN_SYSROOT`, `LAKE_OVERRIDE_LEAN`, `PATH`, and native loader search, and
disable cache restoration as recorded in the captured harness.

The cheapest real-bundle checks are `lake env lean --print-prefix`, the
preserved NativeSmoke proof with the root plugin target, `lake setup-file`,
and the false Smoke control. Confirm the plugin is in setup JSON and
actually loaded. Then run one bounded live server sequence: open, goal,
both source definitions, unsaved false edit, restored true edit, shutdown.
Only changes touching V1 fixture generation or its prelude require repeating
the six-module V1 build and positive/false/`sorry` audit here.

Compare shared content/metadata inventories before and after, and record
attempts separately from successful writes. Use one heavy command at a
time with host headroom checks and process-group time/RSS stops. A new
compiler, archive, native ABI, launcher strategy, or editor selector is a
new combination needing these discriminating checks; passing this report's
offline checker does not validate it.
