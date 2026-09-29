# Lake preparation, cache integrity, and frozen-consumer execution probe

## Summary

At Lean/Lake `v4.30.0-rc2`, a small built producer remained usable after relocation to a different path depth, removal of the original path, and removal of write permissions. Four independent Lake consumers then built against a separately frozen, prebuilt producer without changing its file inventory. A source/control-only workspace plus an isolated eight-file Lake artifact cache also fetched its two modules, including under `--no-build`; however `lake env lean --json` did not find the imported module in that cache-writable layout, while `setup-file` returned the cache-resident OLean path.

A missing cached OLean was rejected as out of date by `--no-build` and `setup-file`. Replacing the *present* content-addressed OLean with invalid bytes made both Lake operations report success. A direct Lean loader control over the same bytes rejected that object with `invalid header`. Thus these Lake preparation statuses are not an independent byte-integrity or elaboration verdict. The observations are specific to the tiny local fixture and operation flags below.

## Applicability

Execution used local `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` and `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, corresponding to `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. Host: macOS Darwin 25.6.0, arm64, 8 GiB physical memory; the scratch filesystem was APFS. Runs used `ELAN_TOOLCHAIN=leanprover/lean4:v4.30.0-rc2`, `LEAN_NUM_THREADS=1`, and `MATHLIB_NO_CACHE_ON_UPDATE=1`. The no-cache cells set `LAKE_CACHE_DIR=''` and `LAKE_ARTIFACT_CACHE=false`; cache cells set an isolated absolute `LAKE_CACHE_DIR` and `LAKE_ARTIFACT_CACHE=true`. Each Lake call had a 25-second timeout; direct Lean controls had a 10-second timeout. No remote dependency, Mathlib tree, native plugin, dynamic library, or actual Anneal generated model was used.

The fixture's producer package `probe_dep` defines `depValue : Nat := 7` in `Dep.lean`. A consumer imports `Dep`, proves `depValue + 1 = 8` by `decide`, and evaluates the expression. Each consumer has a complete manifest with `"dir": "../producer"` before its first Lake command. The script and sanitized exact command/result log are in [`support/probe.py`](support/probe.py) and [`support/results.json`](support/results.json). The script SHA-256 is `29e8cff5aca8aabd5ebcc9769c264e082353b9ecb4546a04c73984a041049db6`.

The architectural hypothesis was that a prepared environment could be represented by source/control state plus immutable artifacts, with separate operation-specific placement and validation requirements. Relocation and cache reconstruction would support it; a missing module, stale path, or corrupt cached object accepted as a valid Lean environment would falsify any stronger single `prepared=true` interpretation. The design implication is to key preparation and validation by operation and artifact identity, and to keep content-integrity and actual Lean elaboration checks separate from a Lake fetch/setup status.

## Findings

### Relocation with original path absent

The initial `lake --keep-toolchain --no-cache build Generated` exited 0 and printed `8`. The complete producer/consumer directory was copied from `original/` to `other/depth/relocated/`; then `original/` was renamed so its former absolute path did not exist. The relocated producer was made read-only. From the relocated consumer:

| Operation | Exit | Observation |
| --- | ---: | --- |
| `--no-cache --no-build build Dep` | 0 | All targets up to date under ordinary hash freshness. |
| `--no-cache --old --no-build build Dep` | 0 | All targets up to date in old mode too. |
| `--no-cache --no-build setup-file Generated.lean` | 0 | `importArts.Dep` identified the relocated producer OLean. |
| `--no-cache env lean --json Generated.lean` | 0 | Information diagnostic evaluated to `8`. |

The read-only producer's recursive SHA-256, size, mode, and nanosecond-mtime inventory was identical before and after those calls. This confirms one relative-layout relocation with the original path absent; it does not imply arbitrary manifest topology or path-bearing native artifacts are relocatable. Basis: **execution**.

### Cache-only reconstruction separates Lake setup from batch placement

A separate source/control fixture was built with `LAKE_ARTIFACT_CACHE=true` into an isolated cache containing six content-addressed artifacts and two output mappings. A fresh producer and consumer with the same source, lakefiles, toolchain file, and complete relative consumer manifest began with no `.lake` state. `--no-build build Dep` exited 0 and logged `Fetched Dep`; ordinary `build Generated` exited 0 and logged `Fetched Dep` and `Fetched Generated`. `--no-build setup-file Generated.lean` exited 0 and returned `importArts.Dep` at the cache artifact path. The cache still had the same eight files after these operations.

In this cache-writable configuration, `lake env lean --json Generated.lean` exited 1 with `unknown module prefix 'Dep'`: the conventional `Dep.olean` filename was absent from its search paths. The clean direct-Lean loader control below succeeded when given a symlink bearing that filename. Thus an artifact-cache fetch and a file-specific setup result did not provide the batch `lake env lean` search-path placement in this fixture. A consumer of `setup-file` can use its explicit artifact paths; a batch invocation needs its own placement/search-path contract. Basis: **execution**. This is not a statement that every Lake cache configuration behaves the same way.

### Missing versus corrupted local cache object

Two copies of the eight-file cache were changed independently. In one, the producer OLean object named by `outputs/probe_dep/*.json` was deleted; in the other, that same named object was replaced with `not an olean\n`. Both retained the mapping and all other objects. Each control used a fresh source/control-only workspace.

| Cache object | `--no-build build Dep` | `--no-build setup-file Generated.lean` | Direct Lean loader via `Dep.olean` symlink |
| --- | --- | --- | --- |
| Intact | exit 0, fetched | exit 0, returned artifact path | exit 0, evaluated `8` |
| Missing | exit 3, artifact-not-found and out-of-date warning | exit 3 | exit 1, unknown module prefix |
| Present with invalid bytes | exit 0, fetched | exit 0, returned artifact path | exit 1, `invalid header` |

The direct loader control deliberately mapped each cache object's bytes to the conventional `Dep.olean` filename through an isolated symlink directory and set `LEAN_PATH` to that directory. It isolates byte validity from the cache-writable `lake env lean` placement issue. Lake's acceptance of the present invalid object is an observed local-cache integrity gap for this exact path, not evidence that Lean accepts it or that remote downloads skip integrity checks. The missing-object behavior shows a useful negative control: failure is explicit rather than a false clean result. Basis: **execution**.

### Small frozen-producer consumer sweep

For each count 1, 2, and 4, a primer consumer built the producer in that exact directory and was removed. The producer was then frozen and a new set of distinct writable consumer directories was created. All consumers started simultaneously in separate Lake processes, ran `--no-cache build Generated`, exited 0, and printed `8`; the producer inventory stayed identical. Observed group wall times were 0.584, 0.654, and 0.832 seconds respectively. Each consumer's logical file payload was about 119.9 KiB; the frozen producer payload was about 105.3 KiB. These are one-run small-fixture observations, not a throughput curve or a high-worker memory model. Basis: **execution**.

## Boundaries

- The new evidence partially informs #3731 I092, I098, I101, I102, I114, and I150. It supplies one small relocation/cache/consumer operation matrix. I102 still needs interrupted writers/restorers and remote/download/extraction cases; I114 needs repeated cold/warm resource measurements and higher counts under budgets. I150 still needs `lake serve`, InfoView/RPC, native artifacts, plugins, and a complete per-operation identity. This report does not execute shared writable build-tree conflicts (I151), retention sweeps (I146), MCP/server topology (I153), or fixture-contamination sentinels (I154).
- Cache corruption was deliberate local tampering. No cryptographic collision, malicious remote service, or power-loss crash was tested. The direct Lean symlink was a loader control, not Lake's ordinary restoration behavior.
- `--no-cache` controls Lake's build cache, and `--offline` was not tested here. The fixture has only local path dependencies; no network-denial harness was used. No claim of general offline operation follows.
- The four-consumer cell had separate writable consumer directories and one frozen producer. It says nothing about safe concurrent writers to one package build directory; the prior corpus's two-writer probe and Lake source report remain relevant.
- Logical file payload is not allocated blocks, bytes written, peak temporary space, proportional physical memory, or process count. The 8 GiB host and tiny serial module graph justified the bounded 1/2/4 sweep only.
- Lake success and a theorem in this synthetic Lean module do not validate Anneal's Rust-to-Lean source correspondence, generated obligation coverage, or trust record.

## Evidence

`support/probe.py` constructs every fixture, records SHA-256 inventories, invokes the exact binaries with bounded timeouts, and writes `results.json`. The retained `support/results.json` includes every command's arguments, exit status, duration, stdout, stderr, cache inventories, and per-consumer payload size. Absolute home/project roots in the copied log are replaced by `$WORK`, `$LEAN_BIN`, and `$LEAN_LIB`; the raw run remains in the conversation-owned Meta/Data scratch directory. Evidence role throughout the findings is **execution** on the stated local binary and filesystem. The existing corpus's [Lake cache concurrency probe](../lake-cache-concurrency-execution-probe-v4-30-0-rc2/REPORT.md), [server preparation analysis](../lake-server-preparation-v4-30-0-rc2/REPORT.md), and [artifact publication analysis](../lake-artifact-cache-publication-restoration-v4-30-0-rc2/REPORT.md) provide separate prior context; their broader source conclusions are not re-proven by this fixture.

## Revalidation

Supply the pinned local `lake` and `lean` binaries, and run:

```console
python3 support/probe.py --lake /absolute/path/to/lake --lean /absolute/path/to/lean --work /new/empty/path/work --out /new/path/output
```

Confirm the binary SHA-256 values first. Compare `results.json` by command labels and semantic outcomes, not path-bearing JSON bytes or exact wall times. Keep the work root on an owned filesystem and do not reuse an existing `--work` path. To extend this result, first add operation-specific batch placement and real `lake serve`/file-worker controls; then use a separate owned fixture for shared-writer interruption and native/Mathlib artifact classes.
