# Post-publication #3731 I107–I159 residual audit and Lake configuration control

## Summary

The live #3731 wording for all **53 investigations I107–I159** matches the published v23 ledger. This audit retains **49 partial, two complete at disposable-prototype scope (I137–I138), and two conditional (I141, I143)** classifications. The [per-ID table](support/row-decisions.csv) records each exact question, cited packages, evidence assessment, cached-only decision, and remaining gate. None of these rows establishes current Anneal V2 product acceptance.

One cached-only availability conclusion was too broad for a bounded component of I126: cached Lean/Lake and the local macOS sandbox allowed a direct Lake configuration execution/denial control. A `run_cmd` in `lakefile.lean` wrote an owned marker outside the Lake workspace when allowed. Denying writes to that outside directory caused the same dynamic configuration to fail with `operation not permitted`, while a static configuration built under the same sandbox. I126 remains partial because this targeted control does not establish full containment, resource limits, native-extension behavior, or an Anneal trust-entry policy. The denial diagnostic included the absolute owned marker path, adding a narrow I127 evidence-handling observation; it is not a private-source leakage test. The separate I076 same-name Charon witness also strengthens I145's name-only identity counterexample, but is not the requested full identity ablation. No other distinct remaining cached-only experiment was identified in the scoped review.

## Applicability

The audit point is published `reference@9d2426519c7eaaf58b13b109a2f4c16d84c51616`, the v23 investigation ledger (SHA-256 `df8517ecf396a7fd1ee230afa95a67c0ed5929edb48dc7b571949c74466a234a`), and the [live #3731 issue body](https://github.com/google/zerocopy/issues/3731) plus its [scope-extension comment](https://github.com/google/zerocopy/issues/3731#issuecomment-5884299718), fetched from GitHub's public API on 2026-09-29. The body was updated `2026-09-29T05:39:11Z`, the comment `2026-09-29T05:32:10Z`; their full SHA-256 values and URLs are retained in [`support/issue-source.json`](support/issue-source.json). The 53 retained scope lines have SHA-256 `86ffa5e21acb87b8cca546e2081663173188c3b029085414429422bff287ae5a`. Each title, method tag, and requested scope matches v23 exactly.

The new probe used pinned Lean/Lake `4.30.0-rc2` on macOS arm64, `sandbox-exec`, one Lean thread, `LAKE_NO_NET=1`, no Lake artifact cache, and a 30-second timeout per case. Work, marker, and private home were owned scratch paths under `~/Codex/Meta/Data/20260929-lean-report-review/`. No dependency was fetched or installed. The retained transcript normalizes that scratch root to `$WORK`; the reported stream hashes are of the original captured streams. The execution did not access credentials, external services, or private source.

## Row-by-row decision

[`support/row-decisions.csv`](support/row-decisions.csv) is the complete 53-row audit. It preserves v23 status, explains what each citation already demonstrates, and states the exact residual after this review. The [125-package inventory](support/cited-package-inventory.csv) records every cited report package's `REPORT.md` and `REPORT.json` hashes at the audit point. Its hashes are historical observations; the checker requires the named packages to exist but does not assume other reports cannot subsequently be corrected.

| Rows | Residual boundary |
| --- | --- |
| I107–I112 | Prior Cargo ownership, OS lock, FD limit, Lean restart/edit-storm, and LSP controls exercise bounded components. Anneal's shared-build ownership, lock graph, failure classification, durable reconstruction, scheduling, and event reconciliation require implemented owners. |
| I113–I125 | Prior byte inventories, worker/resource controls, Lake artifact/lease tests, filesystem portability, and plugin reversibility cover selected cells. Full product write attribution, representative workload, lifecycle, archive, and cross-platform policy remain. |
| I126–I127 | The new Lake configuration and denial control closes one execution/targeted-denial cell. Native extensions, comprehensive containment/resource limits, trust authorization, and private-source evidence hygiene remain. |
| I128–I136 | Selected authority, trust, oracle, comparator, model, publication, and tuple controls exist. Product interfaces, integrated state transitions, broader trust mapping, and independent-host validation remain. |
| I137–I144 | I137–I138 meet their explicitly narrow disposable-prototype questions. I141 and I143 are conditional; study, remote target, economic, topology, and adopted-design decisions need the stated prerequisites. |
| I145–I159 | Prior seven-file identity manifests, retention/pruning, translator, writer, MCP, shell, upgrade, and falsification controls cover components. The new I076 sibling-crate witness shows crate/function names alone are insufficient for I145; a complete cross-layer identity ablation and implemented Anneal service still remain. |

These groups are navigation aids. The CSV supplies the individual evidence and gate for each ID. In particular, I147's prior equal-mtime and comment-only source controls, I151's shared-tree writer controls, and I158's two pinned compatible tuples are already recorded; repeating them without a new product or tuple would not close those rows. The local availability inventory is scoped to the named local-tools tree, `PATH`, and this host; it is not a claim that no suitable asset exists elsewhere.

## I126 and I127: Lake configuration execution boundary

The retained [`dynamic-lakefile.lean`](support/inputs/dynamic-lakefile.lean) uses `run_cmd` to read `I126_MARKER_PATH` and write `lake config executed\n`. The [static control](support/inputs/static-lakefile.lean) declares the same package and library without `run_cmd`. All three commands built the same `Dep.lean` with `lake --keep-toolchain --no-cache build Dep`.

| Case | Outside write allowed? | Exit | Marker | Observation |
| --- | --- | ---: | --- | --- |
| Dynamic configuration | Yes | 0 | Exact expected bytes | Build completed. |
| Dynamic configuration | No | 1 | Absent | `operation not permitted`; diagnostic names the outside marker path. |
| Static configuration | No | 0 | Absent | Build completed under the same write and network denials. |

The sandbox profile allowed default operations and denied `file-write*` only beneath that case's owned `outside` directory plus `network*`. This is a **targeted denial control**, not a broad execution sandbox or a demonstration of safe untrusted-project opening. It shows why Lake configuration belongs in I126's execution inventory and why a denied side effect can surface an absolute path in evidence. The raw diagnostic contained only this owned scratch path; [`results.json`](support/results.json) stores it as `$WORK/...`. I127 still requires representative private-source, environment, credential, path, protocol, and generated-file handling through the real evidence pipeline.

## Boundaries and evidence

- The probe exercised Lake configuration only. Cargo build-script, proc-macro, and Lean `run_cmd` markers are prior cited controls. Native extensions, memory/process/time containment, and user authorization were not tested here.
- The static control establishes that the observed denial is tied to the dynamic configuration's marker write for this fixture. It does not prove all dynamic configurations are unsafe or all static configurations are harmless.
- The [availability inventory](support/availability.json) records two local Lean pins, cached Charon/Aeneas, host capacity, and the absence of a built Anneal omnibus archive in the named local-tools search. It cannot establish global absence or independent-host behavior.
- [`support/probe.py`](support/probe.py) is the bounded replay; [`support/results.json`](support/results.json) retains command arguments, profiles, normalized streams, original stream hashes, input/tool hashes, exits, timings, and marker outcomes. [`support/check.py`](support/check.py) checks the retained scope, all 53 row decisions, 125 citation paths, fixtures, and three outcomes without launching tools.

## Revalidation

Run `python3 support/check.py` from this package for an offline check. To replay the Lake control, use a **new absent owned** work directory and run `python3 support/probe.py --work /absolute/owned/path`; the script requires at least 2 GiB free, writes only beneath that work directory and this package's `support/results.json`, and stops each command after 30 seconds. Copy the package first if the retained results must remain byte-identical.

The remaining work for each investigation is the `remaining_gate` in the row table. Product-gated rows require the named Anneal owner/interface, representative workload, later compatible tuple, independent host, or study decision before their v23 classification can be promoted.
