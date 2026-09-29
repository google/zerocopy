# #3730/#3731 evidence audit v5: R14–R17 and remaining work

## Scope and decision

At the preserved public issue snapshot of **2026-09-29T10:41:15Z**, [#3730](https://github.com/google/zerocopy/issues/3730) is closed and [#3731](https://github.com/google/zerocopy/issues/3731) is open. Both issue bodies and their single comments have the same SHA-256 values as v4: #3730 body `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0`, comment `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 body `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88`, scope-extension comment `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`. The issue snapshot and builder verify exactly **159 distinct I001–I159 investigations and 174 #3730 crosswalk suggestions**, including every destination ID mapping.

All four bounded R14–R17 experiments proposed in v4 are now complete report packages. The corpus has **65 substantive #3730 packages**: 61 previously accounted for and four new. The v5 builder validates all 65 with `reference._load_report`, inspects and hashes every file in the four new packages (107 files, 2,102,644 bytes), and adds exact methods, boundaries and file citations to the affected rows. Each new package's retained offline checker also passed. This ledger describes research evidence and residuals; it does not claim a complete Anneal V2 implementation or 100% resolution.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations (159) | 2 | 147 | 7 | 3 |
| #3730 suggestions (174) | 4 | 143 | 23 | 4 |

I046 and I049 remain complete only for their requested direct-Lean pinned component scopes. C03, C04, C13 and N11 remain the only complete #3730 suggestions. **I060 moved from not run to partial** because R14 executed and applied a same-file Lean rename `WorkspaceEdit`, then fresh-batch-checked the result. The requested cross-file/Rust-hosted projection and Rust-symbol protection were not exercised. No #3730 suggestion changed status: the related B11/B12 rows were already partial after R13. The two full ledgers are `support/investigation-final-v5.csv` and `support/3730-crosswalk-final-v5.csv`; every row has a specific remaining delta.

## Four new reports and exact method boundaries

| Suite and report | Executed evidence | Binding residual |
| --- | --- | --- |
| R14 [`anneal-3730-lean-lsp-navigation-edit-operations-2026-09-29`](../anneal-3730-lean-lsp-navigation-edit-operations-2026-09-29/REPORT.md) | Direct pinned Lean LSP definition, references, rename, semantic tokens, completion resolve and empty code-action response. Applied the actual same-file rename, separately labelled a client completion fallback, and fresh batch checked. `support/transcript.json`, `support/Applied.lean` and `support/projection-replay.json` retain the wire/edit/model evidence. | No real Rust projection, cross-file edit, nonempty server code action, server-authored completion edit or editor save/watch cycle. The replay map is illustrative. |
| R15 [`anneal-3730-lake-key-artifact-family-matrix-2026-09-29`](../anneal-3730-lake-key-artifact-family-matrix-2026-09-29/REPORT.md) | Six source/path/option/manifest input variants and four valid but mismatched local OLean/ILean/C/setup files. Compared Lake no-build/setup, setup-returned cache artifact, fresh local batch/server imports, and two valid plugin initializer generations. `support/results.json` and retained `support/artifacts/` have exact hashes/bytes. | One tiny pinned Lake graph. Lake setup selected the baseline cache OLean, not the overwritten local file; direct servers were forcibly stopped after diagnostics. No Anneal archive, power loss or combined native/setup family guarantee. |
| R16 [`anneal-3730-lean-multiminute-restart-resource-soak-2026-09-29`](../anneal-3730-lean-multiminute-restart-resource-soak-2026-09-29/REPORT.md) | Guarded 188.97-second direct Lean 1/2/4 file-worker ramp plus conflicting-import cell; 69 versioned edit/goal checks, reopen/restart/RPC reference lifecycle, client request-ID collision pilot and resource samples. `support/transcript.json` and `support/pilot-id-collision.json` retain protocol/process evidence. | One watchdog at a time, tiny imports, three minutes; no hours-long leak rate, unique tree physical memory, Mathlib or Anneal/MCP topology. |
| R17 [`anneal-3730-cross-tool-stage-cancellation-cleanup-2026-09-29`](../anneal-3730-cross-tool-stage-cancellation-cleanup-2026-09-29/REPORT.md) | Eight private process-group stop/kill/retry trials across Cargo, Charon, Aeneas, Lake and Lean; delayed Cargo/Charon/Lake child snapshots and successful retries. Separate synthetic fence rejected eight late CLI digest payloads. `support/results.json`, `support/fence-results.json` and retained output artifacts preserve results. | Independent CLI fixtures, not one Rust→Lean pipeline. Aeneas/Lean stopped at launch, delayed controls used wall-clock timing, and no real Anneal scheduler executed the fence. |

`support/new-package-review-v5.csv` records each procedure, cited IDs, boundary and primary evidence files. `support/new-file-inventory-v5.csv` lists SHA-256, size and inspection type for every file in the four packages. `support/r14-r17-disposition-v5.csv` reconciles each planned v4 suite to its completed report. The original packages contain their own replay and offline verification instructions; this audit does not rerun toolchains.

## Further bounded local experiments

The previously planned R14–R17 set is exhausted, but residuals reveal further component experiments possible with already installed tools. Three concrete next suites are in `support/remaining-local-experiments-v5.csv`:

1. **R18:** direct Lean LSP two-file rename and nonempty code-action controls, signature help, inlay hints and completion edit shapes. This could extend I030/I059–I063, still without a Rust-hosted Anneal projection.
2. **R19:** tiny Lake TOML versus Lean dynamic configuration, mtime/trace and setup-family key perturbations with exact consumed-byte checks. This could extend I089–I104/I108–I109 at one pin, still without a real prepared Anneal archive or universal key proof.
3. **R20:** active Aeneas/Lean and more precise Charon/Lake phase cancellation with deterministic barriers, descendant cleanup and retries. This could extend I073–I080/I105/I134, still without an Anneal scheduler.

These are **not** a finite route to closing the 147 partial rows. A new product implementation, meaningful workloads and selected external environments are prerequisites for many remaining integration claims; additional small component experiments can clarify contracts but cannot substitute for those trials.

## Nonlocal and implementation gates

`support/gated-work-v5.csv` preserves seven gate groups and their unblock conditions. The installed one-shot Aeneas CLI does not expose the same-process OCaml library reset or measured in-memory handoff; that requires a compatible prebuilt API or a user-approved nonlocal dependency decision. I141 has a study protocol but zero human participants/outcomes. Filesystem behavior beyond local APFS and cached Ubuntu overlayfs requires a selected target platform. Volar/Razor/editor clients and a Lean MCP adapter are unavailable here. The checkout still lacks a complete Anneal V2 Rust-hosted projection, editor/MCP bridge, shared workspace authority and integrated batch/live engine, so product-wide source ownership, cancellation, cache, isolation, and proof acceptance must be rerun against a real implementation. Remote durability and architecture adoption remain conditional design choices.

## Rebuild and validation

Run `python3 reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v5/support/build_audit.py` from this checkout. It is offline, checks the preserved issue hashes, exact issue heading and crosswalk counts/maps, validates all 65 report packages, asserts the exact four-package delta from v4, and regenerates only this package's CSV/JSON ledger outputs. Two rebuilds yield byte-identical outputs for the frozen snapshot. `reference._load_report` validates this package's `REPORT.md` and `REPORT.json`; this is metadata validation, not a rerun or independent replication of the 65 original experiments.
