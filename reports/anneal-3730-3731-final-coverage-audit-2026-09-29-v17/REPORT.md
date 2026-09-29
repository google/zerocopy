# #3730/#3731 coverage audit v17: post-v16 evidence and dependency gates

## Scope and result

This audit fetched the public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and scope comments at **2026-09-29 16:57:41 UTC** and inspected `reference` at `2c45d74f7176d15a417f9a78a60afaf66eb2fdf2`. All four issue text hashes still match v16. The snapshot contains **159 distinct I001–I159 investigations and 174 distinct #3730 suggestions**. The [investigation ledger](support/investigation-final-v17.csv), [suggestion ledger](support/3730-crosswalk-final-v17.csv), and [333-item challenge](support/row-challenge-v17.json) record each item's exact remaining delta, new evidence, file links, gate categories, and next prerequisite. No partial or conditional row was promoted merely because a narrower component control passed.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 2 | 153 | 1 | 3 |
| #3730 suggestions | 4 | 161 | 5 | 4 |

The narrow complete items remain I046/I049 and C03/C04/C13/N11. I072 still lacks a real Lean MCP adapter/two-client Anneal run. F03/F04/G03/G15/L09 remain unrun at their requested full scope. The corpus is **not 100% complete**, even though #3730 was closed when fetched.

## Evidence added since v16

Only two report packages were published after the v16 audit at `335cf976`: the [unprivileged Lake file-event observer](../anneal-3730-lake-unprivileged-file-event-observability-2026-09-29/REPORT.md) and the [independent review of five original reports](../anneal-3730-five-original-packages-rereview-2026-09-29/REPORT.md). The [post-v16 package review](support/post-v16-package-review.csv) and [10-file hash inventory](support/post-v16-file-inventory.csv) record the exact published content. Both packages have passing offline checkers and valid reference metadata.

The Lake observer makes **I095/F10** more specific: it positively captured an 88-byte `lakefile.olean` read and selected source/trace/hash opens on a warm replay, plus a temporary-to-final OLean rename during a build. This is real process evidence beyond action labels and net file deltas. The interposed functions miss direct syscalls, `pread`, `mmap`, library-internal operations, and access outside its private root; absence of events is not a complete no-read/no-write/no-child proof. A prepared Anneal archive and representative parallel consumers remain untested.

For **I104/F16**, the [earlier prepared-contract experiment](../anneal-3730-lake-prepared-contract-2026-09-29/REPORT.md) had already run relocated no-build, setup, and batch checks under `sandbox-exec` `(deny network*)` and observed `Operation not permitted` from a loopback-connect control. The v16 residual's wording obscured that executed denial. The new observer adds selected private-root file-call evidence, but it does **not** trace network attempts, all filesystem attempts, producer closure, or an actual Anneal archive. The v17 rows correct that distinction and remain partial.

The five-report review corrected one duplicate finite identity mutation and strengthened retained Lean diagnostic assertions. Those changes improve the validity of existing evidence without extending it to an Anneal V2 implementation. Rows aligned with the finite model link the review package as a correction, with unchanged status and remaining product scope.

## Local resources and remaining inputs

The [inventory](support/local-tool-inventory.json) verifies the locally compiled Charon and Aeneas binaries, an older retained pair, their source trees, cached Lean/Lake 4.29.0 and 4.30.0-rc2 executables, and the Nix 2.35.2 profile. The source revisions and binary SHA-256 values are recorded there. The host has **8 GiB physical RAM** and approximately **51.6 GB free** on the working filesystem at inventory time. `ocaml`, `dune`, and `opam` were absent from `PATH`, this local tool root's executable inventory, and the Nix store's `*/bin` search. No dependency was installed or downloaded. A later compatible Lean/Lake tuple, real Lean MCP adapter, and built Anneal omnibus archive remain absent from this checkout.

The v17 row challenge revisited every open item's v16 exact delta against those resources and the two post-v16 packages. A proposed repeat of macOS `sandbox-exec` denial was rejected because the prepared-contract report already records the same control and errno; it would not add a distinct fact. The current snapshot exposes no **newly available distinct cached-only experiment** beyond the published observer. This is limited to the scoped local pins and current issues; it does not close the research agenda. The row ledger identifies the necessary next inputs: an implemented Anneal V2 owner/archive/adapter for integrated guarantees; approved OCaml/Dune/opam or supplied same-process Aeneas runtime for library-route tests; a later compatible toolchain or independent host for upgrade and external replication; permitted complete tracing or suitable independent filesystems for platform claims; sufficient guarded resources for representative parallel jobs; and a frozen interface with consenting participants for human studies. Remote durability remains conditional on a measured local need and a separate environment decision.

## Validation

Run `python3 support/check.py` from this package. It rebuilds the LF CSV/JSON outputs twice with byte-identical hashes; verifies all 333 row decisions, the saved live issue hashes, 159/174 unique IDs, exact status counts, both post-v16 packages' reference metadata, and both offline package checkers. `support/validation-v17.json` pins the inputs, output hashes, issue hashes, source commit, and package inventory. The builder is offline and does not alter the published reports or install dependencies. `CATALOG.json` is generated separately by the reference publication tool after package validation.
