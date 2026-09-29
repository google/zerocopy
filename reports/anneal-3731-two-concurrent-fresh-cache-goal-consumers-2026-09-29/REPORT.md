# Two simultaneous fresh Lake cache consumers reached the same first goal

## Summary

One tiny Lake producer/consumer fixture was built into a private artifact cache. Two independent, source-only package roots then concurrently ran `lake -v --no-build build Generated` against that read-only cache. Both fetched `Dep` and `Generated`, exited 0, and received artifacts with the seed's SHA-256 identities. Each subsequently passed a direct batch theorem/value check and returned the same non-null first goal from its own `lake --no-cache serve` process. The cache and original seed tree file inventories, including hashes and modification times, were identical before and after the two consumers. **Basis: execution**, retained in `support/results.json`.

This adds a paired first-goal result to the [sequential fresh-cache consumer matrix](../anneal-3731-lake-fresh-cache-consumer-matrix-2026-09-29/REPORT.md) and adds simultaneous cache fetches to its selected goal control. A prior [cache-publication report](../anneal-3730-lake-cache-publication-atomicity-2026-09-29/REPORT.md) used two private writable consumers but did not query a live goal. This is one successful two-consumer schedule, not a concurrency guarantee or a result on the actual Anneal archive. It informs #3731 I089/F13 and corresponding #3730 F13 only at the tiny fixture level.

## Applicability and fixture

The run used the already installed local `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) binaries. Lake SHA-256 was `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; Lean SHA-256 was `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The local `probe_dep` package defines `depValue : Nat := 7`; `probe_consumer` imports it and proves `generatedEq : depValue + 1 = 8` using `decide`. The generated source also emits `trace_state`, `#print axioms generatedEq`, and `#eval depValue + 1`. Each package has a pinned `lean-toolchain` and the consumer has a complete relative-path manifest. There are no external dependencies, plugins, native outputs, Mathlib, or generated Rust models.

The seed command was `lake -v build Generated` with `LAKE_ARTIFACT_CACHE=true` and a private `LAKE_CACHE_DIR`. Its output reported `Built Dep`, `Built Generated`, the goal `⊢ depValue + 1 = 8`, no axioms for `generatedEq`, and value `8`. The two independent consumer roots contained only seven source/config files each before their first call. The probe set seeded cache files to mode `0444` and directories to `0555` before both consumers shared it; each had a separate writable producer/config/build tree and isolated home/XDG cache. Consumer calls omitted `LAKE_ARTIFACT_CACHE`, used `LAKE_NO_NET=1`, `LEAN_NUM_THREADS=1`, and a `sandbox-exec` profile with `deny network*` and explicit denial of writes into the shared cache. The profile's network denial was configured; this run did not make an attempted-connect control.

## Findings

| Control | Consumer A | Consumer B |
| --- | --- | --- |
| Fresh `--no-build` Lake action | Exit 0; `Fetched Dep`, `Fetched Generated` | Exit 0; `Fetched Dep`, `Fetched Generated` |
| Direct `lake --no-cache env lean --json Generated.lean` | Exit 0; goal trace, no-axioms result, value `8` | Exit 0; byte-identical batch JSON output |
| Fresh `lake --no-cache serve` | Exit 0; diagnostic wait succeeded; `$/lean/plainGoal` returned `⊢ depValue + 1 = 8` | Same result and clean exit |
| Original seed and shared cache | Unchanged file/hash/mtime inventories across both consumers | Same joint observation |

The two no-build intervals overlapped, as did the two later server intervals; each server opened its own `Generated.lean`. Both fetched OLean hashes matched the seed and cache: `Dep.olean` `cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b` and `Generated.olean` `e807370f82380c588dad12a60d8e2475ac82fc5232cffbbf68a8b1a7dbef9401`. The fresh private producer and consumer trees gained expected artifacts and metadata; their initial source/config hashes remained unchanged. Each server's published diagnostics contained only informational messages, then it shut down cleanly. **Basis: execution and retained SHA-256 inventories**.

## Resource controls and rejected wrapper attempt

The successful run admitted at **24.57% estimated free system memory** and 46,262,894,592 free disk bytes, exceeding the preset 23% memory and 15 GiB disk gates. During the concurrent cell, the monitor sampled 24 times; the lowest estimated free memory was **19.92%**, summed descendant RSS peaked at **2,789,392 KiB**, and at most eight descendant processes were seen. The sampled 12% free-memory floor, 4,500,000 KiB summed-RSS cap, 75-second cell cap, and 30-second per-call cap did **not** trigger an abort. Summed RSS may count shared pages more than once; sampling can miss shorter peaks. The seed build had its own 30-second call timeout but was not under the concurrent cell's RSS sampler.

An earlier exploratory wrapper attempt is retained separately in `support/rejected-wrapper-results.json`. Its constructed `sandbox-exec` profile was malformed; both wrappers exited 65 with `sandbox-exec: illegal argument`, and attempted server initialization ended in `BrokenPipeError`. This was a **harness failure before Lake consumers ran** and provides no evidence about Lake cache or server behavior. The corrected run used a separate valid top-level profile denial expression. Only the successful corrected two-consumer run supports the findings above.

## Boundaries

- The actual content-identified Anneal V2 archive, generated consumer, complete dependency graph, and representative goals were absent. This tiny two-module fixture cannot close I089, I092, or I099 at production scope, or prove F13 for the actual archive.
- This is one simultaneous two-consumer schedule. No four-consumer expansion, randomized schedule search, conflicting source versions, writer collision, or shared writable package-tree test was run. Cache consumption and I151 mutable-tree writer safety are distinct.
- The seed build's messages and the two consumer batch/live outputs agree on the selected goal and theorem result. They do not establish complete clean-versus-prepared equivalence, generated-model consistency, navigation equivalence, or Rust-to-Lean correspondence.
- The before/after inventories establish no **net** file, hash, or modification-time change in the shared cache and original seed tree. They do not rule out transient writes, reads or writes outside these trees, or behavior under an immutable mount. The permission and sandbox restrictions are controls, not syscall traces.
- The direct batch and live server calls followed each consumer's no-build fetch. They therefore used its newly materialized private artifacts; this result does not show a server consuming directly from a bare cache without Lake preparation.

## Evidence and revalidation

`support/probe.py` creates the fixture, seed, two fresh roots, bounded offline commands, barrier-synchronized fetch/server intervals, process/resource monitor, and inventories. `support/results.json` retains command labels, exits, streams, goal responses, tool identities, preflight/guard readings, and before/after SHA-256 inventories with local paths normalized to `$WORK` and `$TOOLCHAIN`. `support/rejected-wrapper-results.json` preserves the preliminary profile error as a separate harness record. `support/check.py` is a read-only Python checker for the retained results. Run `python3 -B support/check.py` from this package without invoking Lake. The checker verifies source and artifact identities, command/exits and cache-fetch labels, overlapping intervals, matching batch/live goal results, initial source-only roots, unchanged shared cache and seed tree, guard limits, and the rejected wrapper's failure class. Its run from the package path exited 0 and printed `Two concurrent fresh Lake cache consumers: preserved evidence passed`.

For an actual Anneal resolution, identify and preserve the requested archive and matching generated consumer, then run the same bounded fresh-consumer and live-goal controls against that content, including explicit write tracing and a clean build comparison. This report does not substitute the tiny fixture for those missing inputs.
