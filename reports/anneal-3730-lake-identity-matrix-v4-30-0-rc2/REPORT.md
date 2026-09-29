# Lake cache ownership, package identity, and artifact-family execution matrix

## Summary

At Lean/Lake `v4.30.0-rc2`, `LAKE_CACHE_DIR` selected the cache *location* and `LAKE_ARTIFACT_CACHE` selected whether this fixture populated it. An empty cache-dir input resolved to each consumer's `.lake/cache`; with artifact caching true, the build wrote six artifacts and two mappings there. An explicit cache directory received the same eight files when caching was true. Either location with caching false received none. This executes the ownership distinction previously established from pinned Lake source.

The operation-specific artifact matrix was narrower than a generic “prepared” state. Removing the producer's `.olean`, `.ilean`, `.trace`, or generated `.c` made `--no-build build Dep` and `--no-build setup-file Generated.lean` exit 3. Direct batch `lake env lean --json Generated.lean` required the `.olean` but still evaluated 7 when `.ilean`, `.trace`, or `.c` was missing. Removing `Dep.setup.json` did not change any of these three outcomes in this fixture.

Package and path identity also remained visible. Changing a consumer's package declaration and matching manifest name at the *same path* changed its compiled configuration OLean/trace bytes and `setup-file` package field, while the imported producer OLean path remained the same. Changing producer source bytes at the same path without advancing its mtime made hash-mode `--no-build` reject the old target and an ordinary rebuild added a new producer cache mapping. A symlink alias to the same producer inode yielded the same imported OLean path in two `setup-file` results. These are bounded execution observations, not a complete Lake cache-key proof.

## Applicability

The local binaries correspond to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `v4.30.0-rc2`: `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` and `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The host was macOS Darwin 25.6.0, arm64, APFS, with 8 GiB physical RAM. Runs were sequential on a tiny local two-module fixture and each command was bounded by 15 seconds. The source, manifest, lakefiles, command arguments, environment choices, exit codes, stdout/stderr, file inventories, and SHA-256 hashes are reconstructible from [`support/probe.py`](support/probe.py) and [`support/results.json`](support/results.json). Script SHA-256: `d1ac13b75671a9454259bc2e1377d7fb426683bfbc111b7b7ff3823436bed50e`.

The producer package `probe_dep` defines `depValue : Nat := 7`; the consumer imports it, proves equality to 7 with `decide`, and evaluates it. Each consumer starts with a complete relative path manifest. Runs set `ELAN_TOOLCHAIN=leanprover/lean4:v4.30.0-rc2`, `LEAN_NUM_THREADS=1`, and `MATHLIB_NO_CACHE_ON_UPDATE=1`, and call the pinned Lake binary with `--keep-toolchain`. Cache-location/policy cells use the exact environment values shown below. Artifact-family cells use `LAKE_CACHE_DIR=''` and `LAKE_ARTIFACT_CACHE=false` so missing outputs cannot be restored from a cache. No remote dependency, Mathlib archive, native library, plugin, or Anneal generated model is present.

The tested hypothesis was that a pooled Lake environment requires separate identities for cache location/policy, root package configuration, producer source/artifact generation, and operation-specific artifact placement. A wrong cache location, unchanged setup identity after a package rename, false cache hit after a same-mtime source edit, or successful no-build setup with a missing required module artifact would challenge that contract. The design impact is to record those dimensions explicitly instead of using one unqualified prepared flag.

The preserved script was replayed from a second empty work directory. All 36 labelled command exits matched the first run; the 2×2 cache file counts, source hashes, and before/after compiled configuration OLean hashes matched as well. The replay log is retained separately; this repeat does not establish cross-version or cross-platform stability.

## Findings

### Cache location and read/write policy are independent in execution

Each matrix cell built a new producer and consumer from identical source with `build Generated` and then asked `lake env printenv LAKE_CACHE_DIR` what path Lake exported. All builds exited 0 and printed 7.

| Incoming `LAKE_CACHE_DIR` | `LAKE_ARTIFACT_CACHE` | Resolved child cache path | Files there after build |
| --- | --- | --- | ---: |
| empty string | `false` | consumer `.lake/cache` | 0 |
| empty string | `true` | consumer `.lake/cache` | 8 |
| explicit absolute directory | `false` | that directory | 0 |
| explicit absolute directory | `true` | that directory | 8 |

The eight-file true cases contained six content-addressed artifacts (`.olean`, `.ilean`, `.c` for producer and consumer) and two package-scoped output mappings. The explicit path controls where those files live; the artifact-cache Boolean controls whether this build populated them. The empty-string location still allowed a workspace-local artifact cache when the Boolean was true. This exactly scoped run does not establish default behavior when either variable is absent, package-specific overrides, or remote cache interactions; the existing [cache environment report](../lake-cache-environment-v4-30-0-rc2/REPORT.md) owns the pinned source analysis of those branches. Basis: **execution**.

### Same path, changed source and configuration

In the explicit-cache/true cell, `Dep.lean` changed from `depValue := 7` to `depValue := 9` at the same path. The script restored its original nanosecond mtime; SHA-256 changed from `15bbf60d162408dade43c6e618dd0d09b28c8fdeb7528c80e40329908f12b7a2` to `f24ea593a7ec12a08b2ab0c096b8babdbf9baeaef4c4a46286e12bf19959c0d0` (the exact values are also in the log). Hash-mode `--no-build build Dep` exited 3 as out of date. Ordinary `build Dep` exited 0 and added a second producer output mapping and new `.olean`/`.c` objects; the previous cache entries remained. This shows a source-byte mutation triggering a new traced input in this fixture despite stable path/mtime. It does not prove every relevant input is covered by Lake's key. Basis: **execution**.

In an independent consumer, `package probe_consumer` and the manifest root name were changed to `probe_consumer_alt` at the same directory. `--no-build build Dep` still exited 0. `setup-file Generated.lean` changed its `package` result from `probe_consumer` to `probe_consumer_alt`; both setups used the same producer `Dep.olean` path. The root compiled configuration OLean SHA-256 changed from `b14e1bbac7ece9818f6f3dac1f25a49d8f825bb402b406b729faa007fecb6f67` to `6647e5c18fa405cc29091f736e3e2d9361391453eedb450d7c70265e0e526b5b`; its trace SHA-256 changed from `7d5612c273bf2488d76aa2a1f7f6d17dbeaff617b35f024f1475b0df9b91d1de` to `e191429fd6ae3ba82d7e7881f00e4ede843a6505d1fb031655d1cfa887a909f1`. Thus same directory and imported artifact are insufficient to identify the consumer's setup. Basis: **execution**.

### One missing producer artifact at a time

The intact fixture passed `--no-build build Dep`, `--no-build setup-file Generated.lean`, and `lake env lean --json Generated.lean` (the batch JSON evaluated 7). Each missing-artifact/operation cell used its own copy of that intact built fixture, then removed only the named producer file before invoking that operation. This avoided one operation repairing the state before another observed it.

| Removed producer file | No-build `build Dep` | No-build `setup-file` | Batch Lean JSON |
| --- | ---: | ---: | ---: |
| `.lake/build/lib/lean/Dep.olean` | 3 | 3 | 1, missing import error |
| `.lake/build/lib/lean/Dep.ilean` | 3 | 3 | 0, evaluates 7 |
| `.lake/build/lib/lean/Dep.trace` | 3 | 3 | 0, evaluates 7 |
| `.lake/build/ir/Dep.c` | 3 | 3 | 0, evaluates 7 |
| `.lake/build/ir/Dep.setup.json` | 0 | 0 | 0, evaluates 7 |

The `.ilean`, `.trace`, and `.c` omissions make Lake's module target incomplete even though ordinary batch Lean can import the remaining `.olean` and evaluate this file. This does not mean those files are optional to an editor, native build, or a different Lake target. The setup JSON side file was not required by these three invocations and remained absent after each cell in this fixture. `--no-build` surfaced incomplete target state with exit 3 rather than a success. Basis: **execution**.

### Symlink alias of one producer

After a direct consumer built the producer, a directory symlink `producer-alias` was created to the same physical producer. A second consumer's lakefile and preseeded manifest named `../producer-alias`. The alias and producer had the same inode. Both consumers' `--no-build setup-file Generated.lean` calls exited 0, reported package `probe_consumer`, and identified the same physical `producer/.lake/build/lib/lean/Dep.olean` path for `importArts.Dep`. This is one same-volume alias observation; it does not settle case-folding, Unicode, hard-link, distinct-root, or Lean document-URI identity behavior. Basis: **execution**.

## Boundaries

- The new execution partially informs #3731 I090, I092, I097, I098, I123, and I150. I090 still needs dependency indices/order, duplicate versions, renamed dependencies, and multiple real package graphs. I097 still needs tool/config/option/model ablations and false-hit controls beyond this one source change. I098 covers ordinary `.olean/.ilean/.trace/.c` and one setup side file; server/private OLeans, IR/bitcode, native objects, plugins, and mixed-generation truncation remain. I123 has one APFS symlink alias only. I150 still needs `lake serve`, InfoView/RPC, dynamic libraries, and a complete pool identity.
- This experiment did not enforce network denial or isolate user homes. The fixture has no remote dependencies and uses a selected local cache, but it is not evidence of I104's hermetic/offline contract. It did not use a real Anneal archive, so I089/I099 remain open. No version upgrade or executable/TOML configuration comparison was performed (I093/I094).
- The source-change cell built only the producer after the edit. Its old consumer mapping remained in the cache; this report does not claim its generated proof was rechecked against the new definition. That stronger cross-layer freshness question belongs to the separate changed-definition sentinel report.
- Read-only package behavior, other filesystems/OSes, native plugins, loaded dynamic libraries, and actual Lean server workers were not exercised here. Successful Lake operations in this synthetic fixture do not establish Anneal proof coverage or trust properties.

## Evidence

[`support/probe.py`](support/probe.py) constructs and runs every cell. [`support/results.json`](support/results.json) and [`support/replay-results.json`](support/replay-results.json) preserve labelled command arguments, selected cache environment, exits, elapsed times, stdout/stderr, producer and consumer SHA-256 inventories, source/config hashes, and alias inode observation. Home/toolchain roots in the retained results are replaced by `$WORK`, `$LEAN_BIN`, and `$LEAN_LIB`; raw output remains in the conversation-owned Meta/Data directory. The findings above are **execution** evidence for the exact binary/fixture. Pinned **source** context already exists in the [Lake cache environment](../lake-cache-environment-v4-30-0-rc2/REPORT.md), [workspace mutable state](../lake-workspace-package-mutable-state-v4-30-0-rc2/REPORT.md), and [server preparation](../lake-server-preparation-v4-30-0-rc2/REPORT.md) packages; their broader conclusions are not inferred from this execution matrix.

## Revalidation

With the pinned local binaries and fresh owned paths:

```console
python3 support/probe.py --lake /absolute/path/to/lake --lean /absolute/path/to/lean --work /new/empty/path/work --out /new/path/output
```

Compare command labels, exits, cache file class/count, hashes for semantic artifacts and configuration, and `setup-file` package/import identities. Do not compare absolute path strings or wall times byte-for-byte. For the full prepared-environment question, extend the same class-by-operation matrix to `lake serve`, per-file Lean workers, native/plugin dependencies, and another explicitly selected platform/revision.
