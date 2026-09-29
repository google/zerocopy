# Independent #3730 crosswalk audit and native Lean plugin trust control

## Summary

At published `reference@9d2426519c7eaaf58b13b109a2f4c16d84c51616`, I re-read the live [#3730 body](https://github.com/google/zerocopy/issues/3730), its [consolidation comment](https://github.com/google/zerocopy/issues/3730#issuecomment-5884380373), the linked [#3731 crosswalk comment](https://github.com/google/zerocopy/issues/3731#issuecomment-5884299718), v24, and the cited report corpus. The [per-suggestion decision table](support/row-decisions.csv) compares **all 174 original requested blocks** with their **345 exact #3731 destination links** and 111 cited packages. I found no justified status promotion or demotion: **three complete at explicitly narrow fixture scope, 162 partial, five not-run at their distinguishing method, and four conditional**. The complete suggestions are C04, C13, and N11; their component findings do not imply integrated Anneal V2 acceptance.

One additional bounded local control was feasible. A retained Lean 4.30.0-rc2 native plugin initializer wrote an owned outside-workspace marker when permitted under a network-denied sandbox. Targeted macOS write denial caused Lean to exit 1 with `operation not permitted` and no marker; a no-plugin proof under the same denial exited 0. This narrows #3731 I126's native-extension execution residual and directly informs #3730 G09's trust boundary. It does **not** implement MCP read/mutate tiers, user authorization, general containment, or resource policy, so **G09 stays partial**. The denied error again included an owned absolute path, corroborating I127's prior path-exposure observation without adding a private-source leakage test.

## Scope and row decisions

The live #3730 body SHA-256 was `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` (closed, updated `2026-09-29T05:40:03Z`). Its consolidation-comment SHA-256 was `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e` (updated `2026-09-29T05:39:32Z`). The linked #3731 crosswalk-comment SHA-256 was `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488` (updated `2026-09-29T05:32:10Z`). These raw hashes match v24's live snapshot. The three exact texts are retained as [`live-issue-body.md`](support/live-issue-body.md), [`live-issue-comment.md`](support/live-issue-comment.md), and [`live-3731-crosswalk-comment.md`](support/live-3731-crosswalk-comment.md). #3730 was closed as a consolidated backlog, not as completed research.

[`row-decisions.csv`](support/row-decisions.csv) is the individual audit: original heading and complete request text/hash; consolidation title and destination IDs; v24 and reviewed status; whether the **entire** original request is supported; source-package citations; new-evidence relation; local availability decision; and remaining gate/prerequisite. The [111-package inventory](support/cited-package-inventory.csv) records report-file hashes at this audit point. The checker verifies every heading, request block, title, destination, status, citation path, and new control. The table is the authoritative per-ID detail; the groupings below summarize the main gates.

| Suggestion rows | Full-scope disposition |
| --- | --- |
| A–D, E04–E12 | Source, Charon, Aeneas, Lean, and model controls are bounded. End-to-end source/projection/generation ownership and matched backend behavior require implemented Anneal interfaces. D07 has a direct I076 sibling-crate LLBC witness; it does not establish a collision-rejecting publisher. |
| E01–E03, L10 | Optional same-process Aeneas work remains conditional: no local OCaml/Dune/opam or callable same-process runtime was found. The installed one-shot CLI does not answer reset or concurrent library-call questions. |
| F01–F20 | Tiny prepared Lake consumers and cache controls exist. F03 needs a later-than-4.30 compatible Lean/Lake pin; F04 needs the actual built omnibus archive. The other archive/identity/load/resource methods retain their specific product or platform gates. |
| G–H, K, L | Toy wire clients, direct Lean, and synthetic projection controls do not supply an Anneal editor/MCP broker, authenticated provenance, or real two-client adapter comparison. G03, G15, and L09 remain not-run at their specified method. G09 gains the native-plugin execution/denial control only. |
| I–J | Selected fresh-oracle and small resource fixtures exist. Full generated-project acceptance, actual Anneal machine status, representative 1/2/4/8/... scaling, and human-facing controls remain. |
| M–O | Two cached translator tuples, falsification components, and candidate architecture documents exist. Later compatible upgrades, matched service alternatives, adopted policy, and integrated batch/live equivalence remain. N11 alone has the original *falsification* answered by selected stale/error/admission/missing-obligation counterexamples. |

The three complete calls were checked against their original methods and retained transcripts: **C04** compared the two Lake launch paths on the same pinned import-refresh fixture (with direct Lean as an extra control); **C13** queried before/after later file errors and separated local goals from batch failure; **N11** falsified “no goals means agent success” with stale imports, later errors, admissions, and absent obligations. The last is complete as a falsification question even though full Rust obligation/trust acceptance remains open under other IDs. No broader complete call was inferred from a destination's status.

The four post-publication investigation mappings were checked separately. I005 and I127 have **no direct #3730 suggestion destination** in the live crosswalk. I076 directly maps to D07 and supplies a narrow name-only-key counterexample to ten suggestions that map to I145: A01, A02, A08, C01, F05, G01, G02, G12, L01, and O03. I126 directly maps to G09. The I076/I145 relation is cross-cutting evidence, not execution of each suggestion's handle, API, cache, or response-envelope method. V24 keeps all twelve affected suggestions partial. The new plugin control changes only G09's exact residual description; its status and prerequisite remain.

## Native plugin trial

The input dylib is an exact byte copy of the retained `plugin-v1.dylib` from [`anneal-3730-plugin-reversal-worker-order-2026-09-29`](../anneal-3730-plugin-reversal-worker-order-2026-09-29/REPORT.md), SHA-256 `3f4a1cb3a67a0027f0c90e819afc20d009ddb921cb7f4c0e0095db074e085aa4`. Its retained [`Plugin.lean`](support/inputs/Plugin.lean) initializer reads only `PLUGIN_MARKER` and writes the constant `plugin-v1`; static symbol inspection found `initialize_plugin__probe_Plugin`. The same dylib bytes were copied into each isolated owned workspace under the loader-required basename `plugin__probe_Plugin.dylib`. The proof was a single `example : True := by trivial`.

All three cases used `sandbox-exec` with `deny network*`, a minimal environment with a private `HOME`/`TMPDIR`, one Lean thread, 15-second wall timeout, 10-second CPU limit, 256-FD limit, and 16-MiB file-size limit. Only the owned `outside` directory differed in write permission. Every process exited normally as a process (no timeout or forced cleanup), in under 0.5 seconds; no external service or non-local dependency was used.

| Case | Plugin? | Outside write denied? | Lean exit | Marker |
| --- | --- | --- | ---: | --- |
| `plugin-allow` | Yes | No | 0 | Exact `plugin-v1` bytes |
| `plugin-deny` | Yes | Yes | 1 | Absent; stderr names the denied owned path |
| `plain-deny` | No | Yes | 0 | Absent |

The raw six stdout/stderr streams are under [`support/raw-streams/`](support/raw-streams/), with their SHA-256s in [`results.json`](support/results.json). The denied raw stream contains an absolute path under the conversation-owned Meta scratch directory; the result summary renders it as `$WORK`. This is a targeted file-write denial only. It cannot establish broad filesystem isolation, network isolation of every possible native action, native ABI safety, or authorization to execute untrusted projects.

An initial **excluded setup attempt** invoked the same retained bytes as `plugin-v1.dylib`. Lean looked for `initialize_plugin-v1`, reported that initializer missing, and wrote no marker in either plugin case. It says nothing about sandbox denial. [`excluded-basename-attempt.json`](support/excluded-basename-attempt.json) records those exits and the correction; the three-case result above uses the correct basename and is the only native-extension finding.

## Revalidation and limits

Run `python3 -B support/check.py` from this package. It checks the retained issue text, all 174 row decisions/345 links, 111 citation paths, input and stream hashes, three process outcomes, resource limits, and the excluded setup attempt without launching toolchains. To replay the native control, copy the package if its retained results must remain unchanged and run `python3 support/probe.py --work /new/absent/owned/path`. The script requires at least 2 GiB free in that parent, writes only to the new work tree and its own result/stream files, and never fetches or installs anything.

Local availability is a scoped observation of the named local tool tree, `PATH`, Python imports, and this host. It is not global proof that a later toolchain, archive, MCP adapter, independent filesystem, or human evaluation cannot be supplied. The per-ID table records what would be needed for every remaining suggestion. No existing package, CATALOG, issue, product data, or credential was modified or accessed by this audit.
