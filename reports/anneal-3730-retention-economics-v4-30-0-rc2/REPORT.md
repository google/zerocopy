# Tiny Lake generation retention, reconstruction, and owned-cleanup probe

## Summary

Sixteen tiny, distinct Lean/Lake generations were built sequentially at `v4.30.0-rc2`. Retaining only a 14-byte value record per generation was cheapest but required rebuilding the source/control workspace for a query; retaining generated Lean and Lake control files still required a build; retaining compiled `.lake` state allowed `--no-build` preparation. For one old and one current generation, all three tiers reconstructed the expected theorem and batch evaluation in fresh processes. The compiled tier shortened the observed preparation step from about 0.8 seconds to 0.4 seconds, while the subsequent batch query remained about 0.5 seconds. These are tiny local-fixture costs, not Anneal/Mathlib-scale estimates.

One already-running Lean reader had imported generation 1 before its directory was deleted. It still evaluated `depValue` as 1 after deletion; a fresh process using the same now-absent import path failed with `unknown module prefix 'Dep'`. The current generation 16 sentinel remained intact. A separate simulated stage-cleanup policy removed dead-owner and incomplete stage directories but preserved a live-owner stage and the active-generation sentinel. These controls show why resident state, reconstructible disk state, and cleanup ownership must be treated separately. They do not prove a Lake or Anneal garbage collector safe.

## Applicability

Execution used `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, release `v4.30.0-rc2`, on macOS Darwin 25.6.0, arm64, APFS, 8 GiB RAM. Binary SHA-256: `lake` `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; `lean` `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The retained script is [`support/probe.py`](support/probe.py), SHA-256 `ce6b6101921085926e75b41ebbab51dd7ffe299ee06f3066cdc4737056eb53de`, and the command/inventory transcript is [`support/results.json`](support/results.json).

The synthetic source input is a JSON record `{"value": N}`. The harness deterministically materializes a local `Dep.lean` definition and consumer `Generated.lean` theorem for N, with lakefiles, toolchain files, and a complete relative manifest. This is a stand-in for source-to-generated-Lean projection: it does not execute Rust, Charon, Aeneas, actual Anneal projection, or preserve real source provenance. All 16 generations differ in definition/theorem value and have separate directories. Generation 1 source/producer OLean SHA-256 are `1dbb79b5f4e40ea57371b62be0976fd55b2be4c6cfe3a26f4824956293c8ea90` / `ecdb4514c5412e92ebd565183a67fd5a02ed5d690c54bb030f45d1ec1d8b0814`; generation 16 hashes are `4e5f0d4737c14dae59de1227fe13fcb9eef4cc8242a5fca22dec2efeec3caa5a` / `be00ba303555926fd6e03cdf1c038cbcb059651a363f65708f4f140e26d15ebc`. Every generation's hashes are in the transcript.

Lake calls set `ELAN_TOOLCHAIN=leanprover/lean4:v4.30.0-rc2`, `LEAN_NUM_THREADS=1`, `LAKE_CACHE_DIR=''`, `LAKE_ARTIFACT_CACHE=false`, and `MATHLIB_NO_CACHE_ON_UPDATE=1`; they invoke the pinned absolute binary with `--keep-toolchain --no-cache`. The import graph is serial and builds are sequential. At most one live Lean reader and two tiny stage-owner sleeper processes existed at once; no more than one Lean worker was launched concurrently. Lake commands had 15-second timeouts; the live reader had a 5-second wait/finish bound. Disk free before the run was about 51 GiB.

The tested hypothesis was that durable historical queries require either retained artifacts or reproducible reconstruction inputs; an already-loaded worker can answer after disk retirement, but a new worker cannot import a deleted generation. Confirmation would be a correct old/current query from each retained tier and explicit fresh-process failure after deletion. A wrong-value query, old import aliasing the current artifact, silent cleanup of the active sentinel, or a claimed durable handle without recoverable bytes would falsify the proposed retention contract. The design implication is to tie handles to explicit retained state or refuse expired handles, with ownership-aware reclamation.

## Findings

### Retention sweep and disk bill

The harness built all 16 generations once, then materialized three retained tiers. **Source-only** kept just `source.json` and relied on the harness to regenerate Lean and control files. **Generated** kept source plus producer/consumer Lean files, lakefiles, toolchain files, and the relative manifest, but excluded `.lake`. **Compiled** kept those files plus `.lake` configuration and build products. Counts refer to retaining the most recent 1, 2, 4, 8, or 16 generations. Totals count file payload, APFS `st_blocks` allocation, and file entries within these retained directories; they exclude the pinned Lean toolchain and the harness's baseline/reconstruction scratch copies.

| Retained count | Source-only logical / blocks / files | Generated logical / blocks / files | Compiled logical / blocks / files |
| ---: | ---: | ---: | ---: |
| 1 | 14 B / 4 KiB / 1 | 758 B / 32 KiB / 8 | 224,337 B / 316 KiB / 28 |
| 2 | 28 B / 8 KiB / 2 | 1,516 B / 64 KiB / 16 | 448,674 B / 632 KiB / 56 |
| 4 | 56 B / 16 KiB / 4 | 3,032 B / 128 KiB / 32 | 897,348 B / 1,264 KiB / 112 |
| 8 | 111 B / 32 KiB / 8 | 6,061 B / 256 KiB / 64 | 1,794,674 B / 2,528 KiB / 224 |
| 16 | 215 B / 64 KiB / 16 | 12,101 B / 512 KiB / 128 | 3,589,946 B / 5,056 KiB / 448 |

The near-linear compiled-state growth follows directly from these independent tiny directories. It does not include shared toolchain/cache bytes, temporary peak, filesystem compression/clones, or actual Anneal/Mathlib modules. Basis: **execution**.

A clean replay of the preserved harness matched all 30 labelled command exits, all 16 source/OLean SHA-256 pairs, file counts, and allocated-block totals. Its compiled logical-byte totals were 119 bytes larger per generation because path-bearing Lake trace/setup text contained the longer replay work-root name. The replay is retained as a separate transcript; raw compiled-tree byte totals are path-sensitive even when the semantic OLean hashes agree.

### Fresh reconstruction of old and current generations

For generation 1 (historical) and generation 16 (current), the harness reconstructed each tier under a fresh path and started fresh Lake/Lean processes. Source-only regenerated all Lean/control files from the value record; generated copied those already-materialized files; compiled copied the full tree, then ran `--no-build build Dep`. Every preparation and subsequent `lake env lean --json Generated.lean` exited 0; the JSON information diagnostic evaluated to the selected generation value and the theorem was accepted. All three tiers produced the same producer OLean SHA-256 for a given generation.

| Generation | Source-only prepare + query | Generated prepare + query | Compiled no-build prepare + query |
| ---: | ---: | ---: | ---: |
| 1 | 0.830 + 0.487 s | 0.803 + 0.478 s | 0.407 + 0.482 s |
| 16 | 0.791 + 0.473 s | 0.792 + 0.485 s | 0.404 + 0.470 s |

Source materialization/copy time was separately recorded at 0.0008–0.0075 seconds in this tiny fixture. The table shows one fresh run per tier/value, not a stable latency distribution or warm-server comparison. It gives a narrow reconstruction control: old definitions were not silently answered using generation 16. Basis: **execution**.

### Resident reader versus fresh reader after retirement

The harness copied compiled generation 1 into an owned live directory, started one direct `lean --json` process with its producer OLean on `LEAN_PATH`, and waited for a marker written after `import Dep`. The proof document then slept 1.5 seconds. While it slept, the generation 1 directory was removed. The process exited 0 and evaluated 1; a new direct Lean process with the same document and now-absent import path exited 1 with `unknown module prefix 'Dep'`. A separate compiled generation 16 directory's `ACTIVE-SENTINEL` content stayed unchanged.

The single live reader's sampled macOS `ps` RSS at the pause was 1,181,152 KiB. RSS is process resident memory, not unique physical footprint. The file-open/import event happened before deletion, so this control demonstrates already-loaded state only; it does not test a server's later file-worker import, new document, RPC session, or memory-mapped artifact access after retirement. A safe collector must account for those later reads before using this observation to delete data. Basis: **execution**.

The clean replay repeated the live/fresh contrast: the imported reader exited 0, the new reader exited 1, the active sentinel remained unchanged, and the sampled resident size was 1,180,768 KiB.

### Simulated interrupted-stage cleanup and handle expiration

Under the same owned scratch root, the harness created three stage directories with `partial.olean` sentinels: one attributed to a live sleeper process, one to a killed sleeper, and one with no owner. A small cleanup model checked process liveness and removed `orphan` and `incomplete`, preserved `active`, and left the current generation 16 sentinel unchanged. This is a model of ownership and an executable negative control against deleting the current generation, not Lake or Anneal's actual cleanup implementation. PID liveness alone is insufficient for a robust production lease because PIDs can be reused and a process can lose ownership while still alive. Basis: **execution** for the model outcome; **derived** for the lease caution.

The harness also records a simple bounded-handle policy that retains only generations 13–16: handles 13 and 16 are `served`, while handle 1 is `refused-expired`. That policy choice is distinct from the full 16-generation archive used for reconstruction above. It makes the expiry behavior explicit instead of implying that a revision handle is durable merely because it once existed. This is a **model**, not implemented Anneal behavior or an actual MCP query.

## Boundaries

- The new evidence partially informs #3731 I113, I116, I121, I122, and I146. I116 needs a sustained edit/query soak and worker lifecycle measurements; this report starts only one short-lived reader. I121 needs later artifact opens, active server file workers, pending queries, scratch forks, and a real GC/lease implementation. I122 needs repeated crash/restart cycles, persistent owner identity beyond PID, and resource reclamation in a real workspace manager. I146 needs real source/projection/generated outputs, historical goals against old imports, retained server comparisons, 1/2/4/8/16 *worker* memory, and representative project sizes. I113 needs bytes written and peak temporary space, shared-page-aware physical footprint, and full pipeline attribution.
- The source-only generator is intentionally trivial. Its tiny JSON input and deterministic text emission do not estimate Charon/Aeneas projection costs or validate Rust/Lean source correspondence. The theorem checks only a synthetic equality.
- The process that succeeded after deletion imported its `.olean` first. A fresh process failed afterward. This does not establish the precise safe reclamation point for a Lean server with deferred imports or native plugins, nor other-platform open-file/rename semantics.
- The cleanup and handle-policy parts are agent-owned models. Their success is not evidence that the current Anneal V1 implementation has this lifecycle or that a future V2 implementation is safe. No files outside the owned fixture were retired.
- This run measured one process's RSS and retained-tree disk allocation. It did not measure `phys_footprint`, CPU, end-to-end interactive goal latency, page cache, or Mathlib/plugin memory. No throughput or high-worker concurrency conclusion follows.

## Evidence

[`support/probe.py`](support/probe.py) is the complete runnable harness; [`support/results.json`](support/results.json) and [`support/replay-results.json`](support/replay-results.json) preserve every command's arguments, exit, duration, stdout/stderr, each generation's source/OLean SHA-256, tier/count disk bills, old/current reconstruction results, reader outcome and RSS, stage cleanup, and handle-policy model. Home/toolchain roots in the retained logs are replaced by `$WORK`, `$LEAN_BIN`, and `$LEAN_LIB`; the raw runs are held in the conversation-owned Meta/Data directory. This report's main empirical role is **execution** on the exact local Lean/Lake pin. Existing [Lean server memory](../lean-server-memory-and-protocol-concurrency-v4-30-0-rc2/REPORT.md) and [V1 disk amplification](../anneal-v1-integration-test-disk-amplification-f98458e/REPORT.md) reports provide distinct larger-scope context; their findings were not repeated here.

## Revalidation

Use the pinned binaries and a new owned work root:

```console
python3 support/probe.py --lake /absolute/path/to/lake --lean /absolute/path/to/lean --work /new/empty/path/work --out /new/path/output
```

Compare the 16 build exits, SHA-256 identities, tier/count storage bills, two old/current reconstruction values, live/fresh reader contrast, and active-sentinel preservation. Keep the work root disposable: the harness removes only its own copied generation and model stage directories. Repeat on another filesystem or with `lake serve`/real Anneal imports before using these results to set a production retention or cleanup policy.
