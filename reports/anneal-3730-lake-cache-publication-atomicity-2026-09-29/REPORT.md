# Lake artifact-cache publication: interrupted map, refused artifact, damaged object

## Summary

With pinned Lake 4.30.0-rc2, a 64-byte file-size limit interrupted the **actual output-map write** after all three module artifacts had entered the cache. The Lake process ended on signal 25 and left a 64-byte invalid JSON mapping. A fresh consumer's no-build setup rejected the map with “invalid JSON” and exited 3; ordinary build rewrote it, after which no-build setup and direct Lean import succeeded. A separate permission failure at the cache artifact directory stopped the first object insertion before any map appeared; restoring write permission and retrying completed the four-file cache.

A deliberately truncated `.olean` under its existing content-addressed name exposed a different failure: Lake's fresh no-build setup and ordinary build both exited 0 and continued to select the 100-byte object. Direct pinned Lean import of that object exited on signal 11. Removing the damaged object made no-build setup reject the missing artifact; ordinary build then repaired the object and direct Lean succeeded. The truncation was injected **after** a valid cache had been published. It is not evidence that Lake's writer caused the bad bytes.

Two private writable package trees then consumed a permission-read-only cache concurrently without changing its inventory. In a separate same-package-tree pair, both writers reached controlled elaboration markers and completed in this one schedule. This does not establish general safety for shared writable package directories. These controls inform [#3731](https://github.com/google/zerocopy/issues/3731) I089–I104/I108–I109/I150–I151 and [#3730](https://github.com/google/zerocopy/issues/3730) F06/F07/F11/F12/F13/J13/J15. No Anneal archive or server was executed.

## Pin, fixture, and write path

The host was macOS 26.6.2 arm64 with 8 GiB physical RAM. Binaries were `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`): Lake SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`, Lean SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. A local `probe_dep` package defines `depValue := 7`; a separate `probe_consumer` package imports `Dep` and proves `depValue + 1 = 8`. Both have pinned toolchain files and a complete relative-path manifest. The module has a conditional 1.5-second `run_cmd` marker to force overlap in the shared-writable pair. There are no external dependencies, plugins, native artifacts, Mathlib, or generated Rust models.

The pinned source `Lake/Config/Cache.lean` (SHA-256 `f5d1430622af25dd672c256ac50941735f9a3cc129abc3f5efe066a26fd4e3f7`) writes an output mapping with direct `IO.FS.writeFile` after creating parent directories. `Lake/Build/Common.lean` (SHA-256 `4ce4b9ce5ad8b55335719928c56ec5a057e2d1b749e54022bca0c95c553d8ea3`) checks whether a cache artifact path exists, then hard-links a binary artifact when possible or writes bytes on fallback. This source inspection explains why the file-size limit could tear the small JSON map while same-volume binary artifact publication used hard links. The experiment verifies the resulting files; it does not claim every writer path or filesystem behaves the same.

Every Lake call used `LAKE_ARTIFACT_CACHE=true` except explicit prebuilds and the shared-package control, an owned `LAKE_CACHE_DIR`, `LEAN_NUM_THREADS=1`, and an isolated `HOME`. The probe required 15 GiB free before starting; it allowed at most two consumers and enforced a sampled process-tree RSS guard of 5,500,000 KiB plus short timeouts. The largest observed summed sample was 3,563,664 KiB in the shared-writable pair; the private read-only-cache pair reached 1,326,192 KiB. Summing per-process RSS may double-count shared pages and misses peaks between samples.

## Publication and recovery observations

| Control | Publication state and consumer result | Repair result |
| --- | --- | --- |
| Output-map write under `RLIMIT_FSIZE=64` | Lake exit `-25`; three intact cache artifacts plus one 64-byte partial JSON output map. Fresh no-build setup exited 3 with invalid JSON. | Ordinary build exited 0 and rewrote the mapping; no-build setup and direct Lean theorem check exited 0. |
| Artifact directory permission denied | Lake exit 1 with `failed to cache artifact: permission denied` at the `.olean` path. Cache had no artifact or output-map files. | Restored directory permissions; ordinary build exited 0 with three artifacts and a map. |
| Existing `.olean` truncated from 4,896 to 100 bytes | Unchanged mapping still named the object. Fresh no-build setup exited 0, ordinary build reported `Fetched Dep` and exited 0; direct Lean exited `-11` (signal 11). | Unlinking the bad object made fresh no-build setup exit 3 with artifact missing. Ordinary build regenerated the 4,896-byte object; no-build setup and direct Lean exited 0. |

The valid `.olean` SHA-256 was `4d2519d8006d6b63510989fa471021ac046867c69ec94aa8e11212bc8468da85`; the truncated copy was `44a98c92e903ee59f4cdea10d0a485ad7d91d141f6ad14ab69d64159a8aa820d`. The valid output map was `4374ce75e3040a0287f0da02104f90620d0b53e417a218b68ab5e7c4cd21f4e7`; the preserved 64-byte partial was `02c91130c41608834ae358a017864d13285f30b71440dc877047a9d2ff4459bb`. The map and artifact basenames encode Lake's hash strings, but a **present** object with wrong bytes passed this tested cache lookup. A missing object and a syntactically invalid map were instead rejected explicitly. A consumer that needs byte-integrity assurance must validate the object before trusting the path; that is a design implication, not a claim about existing Anneal code.

The output-map interruption happened at `IO.FS.writeFile` itself; the artifact permission control failed before object creation, and the object corruption was manual after publication. Thus this suite does **not** show a torn artifact produced by an interrupted hard-link/fallback write, nor does it prove output-map crash atomicity under power failure. It shows a reproducible torn regular-file map and two distinct artifact failure modes. The earlier writer-recovery report covered a kill before module publication; this report reaches cache publication.

## Immutable cache versus shared writable package state

The repaired four-file cache was copied and made filesystem read-only (`0444` files, `0555` directories). Two fresh consumer package trees, each with its own writable producer/config/build directory, ran `lake build Dep` concurrently against it. Both exited 0; the cache's file/hash inventory was identical before and after; both independent no-build setups exited 0. This is one bounded read-only-cache consumption schedule. Permission bits are an operational control in this scratch experiment, not a sealed archive or an immutable filesystem mount.

Separately, two Lake processes ran `build Dep` in the **same** writable consumer and producer directories with the artifact cache disabled. Both process-specific elaboration markers appeared, both commands exited 0, and subsequent no-build setup exited 0. This is one overlapping schedule. It does not demonstrate correctness under conflicting source versions, interrupted writers, trace races, or many workers. The difference between the private/read-only and shared-writable experiments is preserved explicitly; a successful shared-directory schedule must not be promoted into an ownership contract.

## Exact residuals

| Investigation | Evidence added | Still unresolved |
| --- | --- | --- |
| I089–I092, I098–I099, I150 | Prebuilt package/cache bytes separated; missing/corrupt map and missing object reject no-build setup; repaired cache passes direct Lean. | Production generated archive, server startup and private artifacts, exact prepared-environment schema, clean-equivalence across full dependency universe. |
| I093–I097, I100–I101, I103–I104 | Explicit local cache path and isolated home; source inspection of writer and direct local replay. | Cache invalidation and naming across paths/platforms/toolchains, relocation, offline network denial, timestamp perturbation, upgraded Lake behavior. |
| I102 | Actual output-map write interrupted and retried; artifact insertion denied then retried; post-publication object corruption/missing-object controls. | Kill at each artifact hard-link/fallback write and mapping boundary, concurrent same-key map writers, power-loss durability, byte-integrity checks for all artifact types. |
| I108/I109 | Two-process caps, timeouts/RSS guard, one shared-writable overlap, explicit failure/repair outcomes. | Lock-order graph, writer kills after lock acquisition, resource exhaustion, orphan cleanup, stale-success fallback. |
| I151 | Two private writable packages consumed one read-only cache unchanged; a separate shared-writable pair happened to pass. | General shared-package writer safety, conflicting definitions, reproducible collision schedules, failure during shared trace/setup writes. |

No result here validates Rust-to-Lean correspondence, a proof authoring server, interactive goals, or an Anneal integration. The direct Lean check proves only the tiny fixture theorem under this pin. Signal 11 on a damaged `.olean` is an observed process result, not a general Lean failure classification.

## Evidence and replay

`support/probe.py` SHA-256 `b0402a686de8e3c8e880a8a888823ab04378b1475b5dd832deffe62cd7c94313` is the self-validating driver. `support/results.json` SHA-256 `73a4cd35877b30d9dbf4256d6ff1b98fcd9578c8458a55764e169b51209b562a` retains 23 labelled process records, exits, normalized commands, messages, cache/package SHA-256 inventories, samples, and repair identities. `support/artifacts/partial-output-map.json` and `truncated-olean.bin` preserve failure bytes. `map-repaired-cache/`, `artifact-repaired-cache/`, and `object-repaired-cache/` preserve successful cache trees. The fixture source and manifest are in `support/fixture/`.

Replay on the pinned host with `python3 support/probe.py --work /absolute/absent/owned/path`. The script will replace its package-local `support/results.json` and `support/artifacts/`, so copy the package first if retaining this run's raw bytes. The work path must be absent. The output-map signal, permission failure, bad-object false hit, missing-object rejection, repaired direct Lean check, private-cache nonmutation, and process/RSS guards are asserted. Concurrent shared-directory outcomes, timings, process IDs, and sampled RSS can vary; the script records them without treating one success as a universal guarantee.
