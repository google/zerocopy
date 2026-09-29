# #3730/#3731 evidence audit v6: R18–R20 and remaining boundaries

## Scope and status

At the preserved public issue snapshot of **2026-09-29T10:57:07Z**, [#3730](https://github.com/google/zerocopy/issues/3730) is closed and [#3731](https://github.com/google/zerocopy/issues/3731) is open. Their bodies and single comments remain byte-identical to v5: #3730 body SHA-256 `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0`, comment `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 body `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88`, scope-extension comment `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`. The builder verifies exactly **159 distinct I001–I159 investigations**, **174 #3730 suggestions**, and the destination mapping for every suggestion.

All three R18–R20 suites proposed in v5 are complete. There are **68 substantive #3730 report packages**: 65 already accounted for in v5 and the three reviewed here. The builder validates all 68 with `reference._load_report`, inspects and hashes every file in the new packages (126 files, 591,294 bytes), and appends procedure, limit and file-level citations to each affected row. The three new packages' offline checkers passed. This is an evidence audit, not a claim that the Anneal V2 product or the full issue scope has been implemented.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations (159) | 2 | 147 | 7 | 3 |
| #3730 suggestions (174) | 4 | 143 | 23 | 4 |

No status changed in v6. R18 strengthens **I060**, but a direct two-file Lean rename is still partial against the requested Rust-hosted projection and editor transaction. I046 and I049 remain the only complete investigations at their narrow direct-Lean pinned scope; C03, C04, C13 and N11 remain the only complete suggestions. `support/investigation-final-v6.csv` and `support/3730-crosswalk-final-v6.csv` give every row's exact evidence and remaining delta.

## Three new packages

| Suite and report | Direct result | Binding limit |
| --- | --- | --- |
| R18 [`anneal-3730-lean-lsp-multifile-actions-hints-2026-09-29`](../anneal-3730-lean-lsp-multifile-actions-hints-2026-09-29/REPORT.md) | Direct Lean LSP returned a two-file rename, cross-file references, nonempty versioned import quick fix, signature help and inlay hint. Returned rename/action/inlay edits were applied in isolated branches and fresh-batch-checked. `support/transcript.json`, `support/applied-results.json` and `support/applied/` preserve exact messages and sources. | No real Anneal source map or editor transaction. The completion edit was selected by the client; stale preimage/version checks were harness policy. |
| R19 [`anneal-3730-lake-dynamic-config-identity-2026-09-29`](../anneal-3730-lake-dynamic-config-identity-2026-09-29/REPORT.md) | Five clean Lean/TOML configuration cells, an adversarial environment-reading Lean configuration, byte-preserving source/trace mtime shifts, a same-mtime source-byte edit, valid wrong trace/setup generations and exact setup/local OLean consumers under no-build, batch and fresh direct server. `support/results.json` and `support/artifacts/` preserve bytes and mtimes. | One tiny pinned graph. The config-time source writer reads an undeclared environment input; it is a contract challenge, not a Lake promise. Direct servers were forcibly stopped after diagnostics. |
| R20 [`anneal-3730-cross-tool-active-cancellation-barriers-2026-09-29`](../anneal-3730-cross-tool-active-cancellation-barriers-2026-09-29/REPORT.md) | Active FIFO barriers stopped Charon and Aeneas with incomplete output sets; Lean elaboration blocked a Lake child after module A. Process groups were killed, private retries completed, and fresh Lean oracles passed. A completed old Aeneas job was rejected by experiment-side generation authority after a new real cross-tool job advanced. `support/results.json` and retained work artifacts preserve causal markers and outputs. | Selected CLI phases and private destinations. Authority/fence is experimental Python, not Anneal; no general orphan, same-process API, or complete transactional publication proof. |

`support/new-package-review-v6.csv` records the specific procedure, reviewed IDs, boundary and primary files for each new report. `support/new-file-inventory-v6.csv` lists every new file's size and SHA-256. `support/r18-r20-disposition-v6.csv` connects each planned v5 suite to its completed package. The audit validates retained evidence but does not rerun the original toolchains.

## Remaining local experiments and gates

The previously planned R18–R20 set is exhausted. Two further bounded component experiments remain feasible with already cached tools and are specified in `support/remaining-local-experiments-v6.csv`:

1. **R21:** combine valid native/plugin/setup/OLean generations in one small Lake consumer and a Lake-discovered fresh server, recording exact loaded bytes and initializer identity. This could extend I089–I104/I120/I125/I150 but cannot establish an Anneal archive or general ABI safety.
2. **R22:** use active CLI barriers to compare graceful SIGINT/SIGTERM escalation against SIGKILL, with observed pipe/lock state, descendants and retries. This could extend I073–I080/I105/I134 but cannot supply an Anneal scheduler.

These local controls will still leave product integration, human study, platform and dependency gaps. The seven gate groups in `support/gated-work-v6.csv` retain explicit unblock conditions: a compatible same-process OCaml Aeneas API or user-approved nonlocal dependency scope; real human participants for I141; selected additional OS/filesystem; selected external editor/MCP adapters; an actual Anneal V2 Rust-hosted projection and shared workspace/batch-live engine; and product decisions for remote durability and architecture adoption. Small direct-tool fixtures cannot settle those rows by repetition.

## Rebuild and validation

Run `python3 reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v6/support/build_audit.py` from this checkout. The offline builder checks issue hashes, exact 159/174 heading/crosswalk map, validates all 68 packages, asserts precisely the three new R18–R20 packages relative to v5, and regenerates only this package's CSV/JSON ledgers. Two rebuilds produce byte-identical outputs at the frozen snapshot. `reference._load_report` validates this package's `REPORT.md` and `REPORT.json`; neither check independently reruns the 68 original experiments.
