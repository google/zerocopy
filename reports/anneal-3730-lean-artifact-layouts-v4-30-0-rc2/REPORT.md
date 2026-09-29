# Tiny Lean/Lake proof layout tradeoffs under shared helpers

## Summary

Three disposable module layouts used the same two claims and helper against the same model at Lean/Lake `v4.30.0-rc2`. A per-annotation approximation used two proof modules and two live file workers; per-file and per-artifact approximations used one proof module and one worker. After editing only the first claim, the split layout rebuilt `AnnOne` and its aggregate consumer while `AnnTwo`'s OLean stayed byte-identical; the combined layouts rebuilt their entire proof-bearing module and aggregate consumer. A failed first claim still allowed a fresh `AnnTwo` batch check in the split layout. The aggregate consumer failed in every layout until the bad claim was repaired.

Two complete runs at model sizes one and 128 yielded the same artifact hashes and structural outcomes. The split layout had higher measured summed worker RSS and more sequential Lake target launches in this tiny fixture. A separate visibility control confirmed that a split second annotation cannot refer to the first claim without importing its module; an explicit import or same-file order made that reference valid. These are Lean/Lake fixture results, not measurements of Anneal annotation projection or a general best layout.

## Applicability

The directly executed subjects are Lean and Lake from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) on arm64 macOS, binary hashes in `REPORT.json`. Python 3.14.7 and the standard library generated and drove the fixture. Each cell is a local Lake package with no external dependency, Mathlib, plugin, native extension, Rust input, Aeneas output, or actual Anneal source. `LEAN_NUM_THREADS=1`, `LAKE_ARTIFACT_CACHE=false`, and sequential target commands avoided concurrent Lean compilers. At most one direct Lean server ran at once; a 1.5-GiB summed-RSS guard was armed on its process tree.

The same declarations appear in each layout: `modelValue : Nat := 7`, a helper proving `n + 1 = 8` from `h : n = modelValue`, and `claimOne`/`claimTwo` using `exact helper n h`. A fixed `Aggregate.lean` consumer imports both claims and checks their intended types. Each model also has either one or 128 inert `pad` definitions, so model size changes without changing the claims. The three approximations are:

| Layout label | Module graph | Proof-bearing open files |
| --- | --- | --- |
| Per annotation | `Model → Shared → AnnOne, AnnTwo → Aggregate` | `AnnOne`, `AnnTwo` |
| Per file | `Model → File → Aggregate`; helper and both claims share `File` | `File` |
| Per artifact | `Artifact → Aggregate`; model, helper, and both claims share `Artifact` | `Artifact` |

An “annotation” here is one ordinary Lean module standing in for a future projected Rust annotation. It is not an executed parser, source map, or generated-file ownership policy. All commands and source hashes are in [`support/raw-run1.json`](support/raw-run1.json) and [`support/raw.json`](support/raw.json); the latter is run 2.

## Findings

### Module, worker, and import costs

Each Lake module was declared as a target and built in import order. One cold, one no-change warm, and one single-proof-edit build sequence ran per cell and per repetition. The table shows two-run ranges; milliseconds are sums of sequential target invocations, including Lake startup each time. RSS is the sum of macOS `ps` per-process resident sizes at the loaded server point, not unique physical memory.

| Model pads | Layout | Modules / live file workers | Cold sequence | Warm sequence | One-proof edit sequence | Summed RSS |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | Per annotation | 5 / 2 | 2708–3255 ms | 2090–2091 ms | 2291–2300 ms | 917–920 MB |
| 1 | Per file | 3 / 1 | 1612–1614 ms | 1248–1249 ms | 1448–1449 ms | 496 MB |
| 1 | Per artifact | 2 / 1 | 1079–1091 ms | 831–832 ms | 1023–1031 ms | 499 MB |
| 128 | Per annotation | 5 / 2 | 2672–2680 ms | 2094–2096 ms | 2282–2289 ms | 926–931 MB |
| 128 | Per file | 3 / 1 | 1607–1612 ms | 1246–1251 ms | 1441–1447 ms | 496 MB |
| 128 | Per artifact | 2 / 1 | 1073–1078 ms | 828–831 ms | 1024–1027 ms | 516 MB |

The per-annotation server had one watchdog and two workers; the other layouts had one watchdog and one worker. All six servers exited 0 and their post-stop process-tree RSS samples were zero. Two runs are enough to show this fixture's structural repeatability, not to estimate a latency distribution. The measured build ordering penalizes extra modules with extra Lake CLI startups; a scheduler that builds multiple independent targets in one invocation could change the timing ranking. Basis: **execution**, with the exact values and process rows in [`support/comparison.json`](support/comparison.json) and the raw transcripts.

The direct fresh proof-file batch checks summed to 342–344 ms for two per-annotation modules versus 180–181 ms for per-file, 181–182 ms for the one-pad artifact, and 214 ms for the 128-pad artifact. The aggregate consumer's fresh import check was 164–166 ms in all six cells. Thus the wider split caused more separate proof-file checks, but a single importer did not show a measurable layout advantage in this tiny precompiled graph. The 128-pad artifact enlarged its source and proof-bearing OLean, while split `Model.olean` grew from 5,704 to 132,400 bytes and the per-annotation proof OLeans stayed byte-identical. This is a bounded import-cost observation, not a production-scale cost curve. Basis: **execution**.

### Incremental reuse and failure isolation

The edit changed only the first `exact helper n h` to `exact (helper n h)`, keeping its theorem statement and meaning. Comparing OLean modification times and SHA-256 after the Lake sequence showed `AnnOne.olean` and `Aggregate.olean` changed in the split layout; `AnnTwo.olean`, `Shared.olean`, and `Model.olean` did not. In per-file, `File.olean` and `Aggregate.olean` changed while `Model.olean` stayed; in per-artifact, `Artifact.olean` and `Aggregate.olean` changed. Both repetitions had identical pre-edit OLean hashes for every cell and the same changed-module sets. The split layout therefore preserved an independently compiled sibling artifact for this edit. It did not make the whole aggregate claim cheaper under the measured sequential build procedure. Basis: **execution**.

Replacing the first proof with `exact ?_` made the edited proof-bearing module's Lake target fail in all layouts. In the split layout, `AnnTwo.lean` still passed a fresh direct batch check against the unchanged `Shared`/`Model` artifacts. The per-file and per-artifact layouts had no separate sibling proof module to check independently. None of these failures authorizes treating a previously compiled aggregate artifact as current: the new aggregate generation was incomplete. This is a narrow failure-isolation distinction, not a claim that a partially failed project is verified. Basis: **execution**.

### Semantic restriction from splitting

The separate [`support/semantic.py`](support/semantic.py) control compiled a shared helper and `AnnOne`. `AnnTwoWithoutImport.lean` then tried to prove its claim with `claimOne` while importing only `Shared`; Lean exited 1 with `Unknown identifier claimOne`. Adding `import AnnOne` made the same proof exit 0, and putting both claims in source order in one `Combined.lean` also exited 0. This illustrates the dependency/visibility cost of a per-annotation module boundary. A real generator would have to preserve author-intended sharing, order, namespaces, options, and allowed import edges. The earlier [`document context`](../anneal-3730-document-context-v4-30-0-rc2/REPORT.md) report already showed a declaration-order and wrapper-context pitfall; this control isolates one simpler cross-annotation reference. Basis: **execution**.

## Boundaries

- **Not examined:** actual embedded Rust annotations, Charon/Aeneas generated modules, user-owned proof files, source maps, multiple Rust compilation subjects, or generated model size beyond 128 trivial definitions. No layout is adopted here.
- **Not established:** a universal time or memory optimum. The build procedure invokes Lake once per module in import order to serialize compilers, and only two repetitions were run. Summed RSS double-counts shared pages; peak RSS between samples and unique footprint were not measured.
- **Not examined:** parallel Lake scheduling, larger Mathlib imports, options/plugins, annotation moves/renames, local notation/instances, mutually dependent proofs, nontrivial theorem searches, or more than two proof workers. The earlier cycle and wrapper probes remain separate evidence.
- **Not established:** that an unchanged proof OLean means a current project-wide claim after a sibling failure. The aggregate consumer is the fixed acceptance point and its new build failed in the negative control.
- **Known setup correction:** the first cold attempt declared only `Aggregate` as a Lake library target; Lake did not build `AnnOne` and returned an unknown import error. [`support/setup-attempt.json`](support/setup-attempt.json) preserves that failed attempt. The completed fixture declares each local module as a target and builds targets sequentially.

## Evidence

- Main executable [`support/probe.py`](support/probe.py), SHA-256 `4a603f56ae82d91d95060b05df5d09aff1225264774ffe0b183ed796871eeea0`; full normalized protocol, commands, artifact inventories, and process rows: [`support/raw-run1.json`](support/raw-run1.json), SHA-256 `ff1b0b47ee854bba72ee1328b7a44b275fb40a6c6bbe755c6bc4a2655498e90a`, and [`support/raw.json`](support/raw.json), SHA-256 `5094cd4c96e81d38d8bd6742a58264e296c77e3c517b3b6f7bc2b00cffcaec82`.
- Structural and timing comparison: [`support/summarize.py`](support/summarize.py) and [`support/compare.py`](support/compare.py). The latter asserts same module counts, proof-edit change sets, failure outcomes, worker counts, and pre-edit OLean hashes across both runs, then writes [`support/comparison.json`](support/comparison.json), SHA-256 `02a67438b3738568a7e0553cc9497a92800465f4b75492e27868bde45d1c9e6b`.
- Visibility control: [`support/semantic.py`](support/semantic.py), SHA-256 `f9b979dcd167e8621cf58d3bad0a4f457caf2ab56bc1b4d26c78e4baa0997981`; raw [`support/semantic-results.json`](support/semantic-results.json), SHA-256 `46238feae509edee827e1eafd51d7f840ebf9d09b050376d75ea91c63d06988e`. [`support/work/`](support/work/) and [`support/semantic-work/`](support/semantic-work/) retain the source and final local artifacts; the main work tree ends in deliberate failure-injection state and is regenerated on replay.
- Primary agenda: [google/zerocopy issue #3731](https://github.com/google/zerocopy/issues/3731), I035. Prior generated-file and multi-workspace limits are in [`lean-generated-file-interactive-workflows`](../lean-generated-file-interactive-workflows-v4-30-0-rc2/REPORT.md) and [`lean-server-multi-workspace-isolation`](../lean-server-multi-workspace-isolation-v4-30-0-rc2/REPORT.md). Those reports supplied scope, not these execution outcomes.

## Revalidation

In a fresh copy, set `LEAN_BIN` and `LAKE_BIN` to the pinned local binaries and run `python3 support/probe.py` twice, preserving the first `raw.json` and `summary.json` as `raw-run1.json` and `summary-run1.json`. After each run execute `python3 support/summarize.py`; then run `python3 support/compare.py`. Run `python3 support/semantic.py` once. Confirm complete target builds, fixed aggregate claims before the injected failure, two versus one worker, changed OLean sets after the one-proof edit, independent `AnnTwo` batch success after `AnnOne` fails, and the no-import/with-import visibility outcomes. On another backend or real Anneal projection, keep the proposition, helper, model, and oracle constant while varying only the layout; retest larger models and resource/semantic dimensions before choosing a product layout.
