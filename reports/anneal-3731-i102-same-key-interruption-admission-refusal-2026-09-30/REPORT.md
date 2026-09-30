# I102 same-key interruption attempt stopped at fresh memory admission

## Summary

A guarded local retry for [#3731 I102](https://github.com/google/zerocopy/issues/3731) stopped before any artifact or output-map interruption. One private Lake `build Dep` prebuild with artifact caching disabled completed and exited 0. Reclaimable RAM was 30.8668% at that launch, then 25.6100% at the next fresh admission, below the experiment's strict greater-than-30% threshold. The runner denied `prebuild-b` and launched no second Lake process. No cross-volume cache image was created, no same-key cache writer ran, and no interruption or recovery result was acquired.

## Applicability

The one completed command used installed Lake/Lean 4.30.0-rc2 on macOS with the binary SHA-256 values in [REPORT.json](REPORT.json). The small private fixture was copied from the earlier [same-key writer report](../anneal-3730-lake-same-key-artifact-writers-2026-09-29/REPORT.md). It includes two intended producer/consumer roots and a small golden cache reference. Only root `a` was prebuilt; root `b` was copied but never used by a process. The probe was intended to compare interrupted `.olean` and output-map publication followed by a second root's same-key recovery. Its code and staged fixture define that planned method, while [results.json](results.json) records only what actually ran.

## Findings

The completed `prebuild-a` command was `lake --keep-toolchain --no-ansi build Dep` from private root `a`'s consumer, with `LAKE_ARTIFACT_CACHE=false`, `LAKE_NO_NET=1`, private home/cache, one Lean thread and no `LEAN_PATH`. It exited 0 in 7.1935 seconds. Its raw stdout/stderr and output SHA-256 values are retained in [raw/](raw/). The sampled process group reached 1,813,424 KiB summed RSS; estimated reclaimable RAM reached a low of 24.0709% during the run, above the runner's 20% runtime kill threshold. No runtime guard fired.

The second admission measured 25.6100% reclaimable RAM and 18,499,035,136 free disk bytes. The strict fresh RAM threshold failed, so the runner recorded `RuntimeError('prebuild-b:fresh_admission_denied')` and `status: stopped`. `results.json` contains exactly one run, two admissions and an empty `cases` object. The process cap, disk cap, and interruption code therefore supply no artifact/map observation. The preserved [work tree](work/) contains the first prebuild outputs and unexecuted root `b`; it does not represent a recovered cache.

## Boundaries

The first Lake exit 0 only confirms that this tiny local prebuild completed with caching disabled. It says nothing about same-key cache publication, torn artifacts or maps, process termination at a write boundary, subsequent recovery, power-loss durability, or Anneal's selected publication design. The v67 I102 residual, product gate, and next prerequisite remain unchanged. No v68 audit/crosswalk is warranted from a resource refusal with no relevant cache cell.

## Evidence

The executed [probe.py](probe.py) checks pinned binary hashes, takes a fresh `vm_stat`/disk admission before each Lake process, samples process-group RSS and free memory, and saves raw streams and structured results. [results.json](results.json) is the final `stopped` record. The [fixture](fixture/) and [work tree](work/) retain the exact staged inputs and first prebuild outputs. The offline [check.py](check.py) verifies the one-run/two-admission boundary and raw output hashes without launching Lake.

## Revalidation

Run `python3 -B check.py` from this package. A new interruption attempt should begin in a fresh private directory on a host with enough headroom to keep every sequential Lake launch above the strict 30% admission threshold. It must preserve separate artifact and map failure records, verify cache bytes against the golden reference after each recovery step, and keep any product-level claim tied to the actual Anneal pipeline. This attempt gives no reason to change Codex setup or the I102 research prompt beyond scheduling the pending experiment with adequate RAM.
