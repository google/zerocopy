# Lake same-key writers and interrupted OLean/ILean/C artifact writes

## Summary

With pinned Lake/Lean 4.30.0-rc2, three pairs of private package roots built the *same* `Dep` cache key against an initially empty shared cache. Both processes completed in each pair; the resulting map and `.olean`, `.ilean`, and `.c` object bytes matched a single-writer golden cache exactly. A fresh private consumer's no-build setup and direct Lean import succeeded after every pair. These are three successful **overlapping process schedules** on one small APFS fixture. The `run_cmd` markers and sampled process tree show both builds active, but no barrier proves that their individual artifact write syscalls overlapped. This is not a general shared-writer safety proof.

The failure controls found a stronger integrity boundary. The cache was placed on a separate, 128 MiB scratch APFS disk image so Lake's hard-link attempt could not cross volumes and its source-defined binary write fallback ran. A file-size limit halfway through one targeted object left a real partial file for each of `.olean` (2,448/4,896 bytes), `.ilean` (404/809), and `.c` (764/1,529). Lake exited on signal 25 and fresh no-build setup rejected the absent map. An ordinary retry **without removing the partial object exited 0 and published a map while the object bytes remained wrong**. Another fresh no-build setup then exited 0. Direct Lean import exited on signal 11 for the partial `.olean`; it succeeded for the partial `.ilean` and `.c` in this simple import, although exact object-hash checks rejected both. Explicitly deleting the partial object and map, rebuilding, and rechecking from a fresh consumer restored byte equality with the golden cache and a successful direct Lean import in all three cases.

This is a pinned local component experiment, not a power-loss, native ext4/Windows, Mathlib-scale, or Anneal generated-workspace result. It does not establish that Lake itself produced a corrupted content-address name: the size limit deliberately interrupted its write fallback. It does establish that, at this pin and on this path, a present partial object can be accepted on retry without content revalidation before a successful output map is exposed.

## Subject, fixture and procedure

Executed on macOS arm64 with Lake SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` and Lean SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The installed `Lake/Build/Common.lean` source had SHA-256 `4ce4b9ce5ad8b55335719928c56ec5a057e2d1b749e54022bca0c95c553d8ea3`: its `Cache.saveArtifact` first tries a hard link, then `writeBinFileIfNew` on a non-`alreadyExists` hard-link failure; if the cache path already exists, it skips writing that object. The experiment uses that path, not an injected replacement of Lake code.

The fixture is a tiny `probe_dep` package with `Dep.lean` defining `depValue := 7` and a `probe_consumer` importing `Dep`. A conditional `run_cmd` writes a marker and pauses 1.5 seconds to make paired process execution overlap. A direct independent `lean --json` process imports the cached `Dep.olean`, proves `depValue + 1 = 8`, and evaluates the expression. Source and package files are retained in `support/fixture/`; the complete command, process, cache and result record is `support/results.json`.

The script checks at least 20 GiB free host disk and 35% reported free memory before work. It creates an isolated 128 MiB scratch APFS disk image under an absent conversation-specific Meta/Data path, verifies a different device ID from the producer files, and detaches and deletes the image in a `finally` block. At most two tiny Lake consumers run simultaneously; their sampled process-tree summed RSS is capped at 3,800,000 KiB, scratch file bytes at 256 MiB, and each process run at 30 seconds. The highest sampled pair RSS was 3,557,536 KiB, below the cap. Summed RSS double-counts shared mappings and is not unique physical RAM. The retained acquisition had 47% initially reported free memory and 44% after completion.

For each interruption case, a local producer was built with artifact caching disabled. The cache was seeded with the *other* two golden objects, leaving only the chosen extension absent. `RLIMIT_FSIZE` was applied to the Lake process at half the chosen object's size; the separate APFS volume forced the fallback byte write. The 74 retained records include launches, exits, streams and fresh-consumer checks. `support/artifacts/partial-*.bin` preserves the actual truncated object bytes. `support/artifacts/partial-present-cache-*/` preserves the false-hit cache after ordinary retry; `support/artifacts/repaired-cache-*/` preserves the clean result. `support/check.py` independently validates these saved bytes and observations without rerunning Lake.

## Same-key and interruption results

| Trial | Observed result | Oracle |
| --- | --- | --- |
| Three two-process same-key misses | Both process markers appeared; all six Lake exits 0. Pair peaks were 3,557,536, 3,516,256, and 3,484,976 KiB sampled summed RSS. Each cache map and all three object hashes equaled the golden cache. | Fresh private no-build setup and fresh direct Lean import exited 0 after every pair. |
| `.olean` write limit 2,448 bytes | Lake exited `-25`; partial object 2,448/4,896 bytes. Initial fresh no-build exited 3. Retry with object still present exited 0 and retained wrong hash; subsequent fresh no-build exited 0. | Direct Lean import of the partial OLean exited `-11`. Delete object/map, rebuild: exact golden cache hashes and fresh import exit 0. |
| `.ilean` write limit 404 bytes | Same failure/retry sequence; partial 404/809 bytes remained under its expected cache name. | Fresh direct import exited 0 despite wrong ILean object hash. Exact hash gate rejected it; deletion/rebuild restored golden bytes. |
| `.c` write limit 764 bytes | Same failure/retry sequence; partial 764/1,529 bytes remained under its expected cache name. | Fresh direct import exited 0 despite wrong C object hash. Exact hash gate rejected it; deletion/rebuild restored golden bytes. |

The artifact names were `7b7a31f2adb2306a.olean`, `256fdbc46043cf30.ilean`, and `19804e4afa920628.c`. Their *file* SHA-256 values, the shorter Lake content-address names, every map hash and the partial bytes are distinct fields in `support/results.json`; do not equate the filename token with SHA-256. The golden cache was a single-writer output on the same scratch volume. The pair result's full cache inventory matched it, including the output-map filename and bytes, so all three pairs reached the same key and result in the observed schedules.

## Exact residuals for #3731

| Item | Contribution here | Remaining distinguishing work |
| --- | --- | --- |
| I089 | Fresh tiny producer/consumer cache with exact artifact family. | Actual Anneal prepared archive from empty home/cache, first-goal writes and read-only dependency enforcement. |
| I090 | Same `probe_dep` key across copied private roots. | Package naming/version/order/collision matrix and a formal consumer package identity. |
| I091 | Fresh no-build setup checks after failure and repair. | Hidden server `setup-file` choice for current or unsaved document and exact worker environment. |
| I092 | No-build rejected absent map, then accepted a map pointing at wrong object bytes. | Full no-build/no-cache contract across artifact/config families and interactive server operations. |
| I093 | Local Lake configuration held constant. | Lean/TOML configuration variants, dynamic inputs and package graph changes. |
| I094 | One pinned Lake revision. | A compatible upgraded Lake tuple with old findings retained. |
| I095 | Cache map/object hashes and fresh consumer outcomes show reuse in a small case. | Trace actual read/write process activity and effective parallelism at larger sizes. |
| I096 | Controlled `LAKE_CACHE_DIR`, `LAKE_ARTIFACT_CACHE`, home and binary paths. | CLI/editor/MCP/CI selector and configuration-discovery variants. |
| I097 | Present wrong bytes under the expected object pathname produced a cache false hit. | Source/model/tool/flag/path key ablations and independent integrity policy across all artifact types. |
| I098 | OLean/ILean/C object family compared individually; a wrong ILean/C object escaped the selected direct-import oracle. | Valid but incompatible cross-generation families, native/plugin artifacts and server operation matrix. |
| I099 | Fresh selected theorem import succeeded after full-byte repair. | Full clean versus prepared declarations, assumptions, diagnostics and tactic-state equivalence. |
| I100 | Source and input held fixed. | mtime, trace, source order and normalization perturbations. |
| I101 | Private copied roots consumed the same cache key. | Relocation of a producer-removed generated Anneal archive, retained workers and native/setup paths. |
| I102 | Actual cross-volume binary write interruption for each of OLean/ILean/C; retry false hit; three same-key process-pair schedules; exact recovery after deletion. | Causally forced artifact syscall collision, map write plus object failure under two writers, power-loss durability and all restoration phases. |
| I103 | None beyond exact local cache bytes. | Same-label archive install replacement and consumed-byte attestation. |
| I104 | Cache was local, with no download. | Enforced network denial and producer/consumer filesystem attempt tracing. |
| I108 | Bounded paired builds finished without deadlock; process and disk guards recorded. | Cross-component lock-order graph with paused publication/restart/GC and failure recovery. |
| I109 | Real per-process file-size exhaustion and successful explicit repair; an initial RSS guard stopped an over-budget calibration. | Memory/disk/fd/process exhaustion, orphan cleanup and Anneal last-good state recovery. |
| I151 | Two private writable producer roots shared a single same-key cache for three pairs. | Deliberately conflicting *shared writable package build tree* writers and crash schedules; cache sharing and build-tree sharing remain separate subjects. |

No row is claimed complete by this package. In particular, the three successful pairs cannot prove arbitrary same-key publication safety. The partial-object retry is a concrete counterexample to interpreting Lake exit 0 or no-build setup 0 as byte-integrity evidence under an interrupted writer.

## Evidence and replay

Run `python3 support/check.py` to validate the retained result, partial files and cache trees; it reports three matched pairs, three genuine partial writes, false-hit and repair oracles. To reacquire on the pinned host, run `python3 support/probe.py --work /absolute/absent/owned/path` from this package. The script replaces only its own `support/results.json` and `support/artifacts/`; copy the package first to retain this acquisition. It never installs or downloads tools, and its detached scratch image is deleted after each run. A new host, filesystem or Lake revision is a new subject: record its hashes and outcomes instead of silently carrying forward this pin's conclusion.
