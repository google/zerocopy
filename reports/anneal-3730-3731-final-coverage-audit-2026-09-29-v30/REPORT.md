# #3730/#3731 coverage audit v30: cancellation, installed tools and concurrent fresh consumers

## Summary

Three finalized component reports sharpen **five partial rows** in the published [v29 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-29-v29/REPORT.md): investigations **I080, I089 and I094**, plus #3730 suggestions **D06 and F13**. All 333 IDs, 345 #3730→#3731 destination links, inherited request text, statuses and gate categories remain unchanged. The [investigation matrix](support/investigation-final-v30.csv), [suggestion crosswalk](support/3730-crosswalk-final-v30.csv) and [333-row challenge](support/row-challenge-v30.json) append an exact v30 residual, prerequisite and scope assessment to each row.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

The [I080 cancellation/recovery report](../anneal-3731-i080-incremental-on-shared-target-cancel-recovery-2026-09-29/REPORT.md) runs one edited-source, incremental-on shared Cargo target cancellation and retry. The [I094 inventory](../anneal-3731-i094-installed-lean-lake-inventory-2026-09-29/REPORT.md) bounds the installed Lean/Lake upgrade candidates without executing a later version. The [two-consumer Lake report](../anneal-3731-two-concurrent-fresh-cache-goal-consumers-2026-09-29/REPORT.md) adds simultaneous fresh cache fetches and first goals under a read-only shared cache. None runs an Anneal V2 service, actual omnibus archive or a later Lean/Lake ownership comparison.

## Applicability

The baseline is published `reference@40b3024d5a3c73357abb6e90f10fcaf713768cd4` and its v29 ledger. The cancellation probe uses Charon 0.1.210 with nightly-2026-05-31 Cargo/rustc on a tiny two-crate fixture, equal-length A/B roots and one warmed writable target. The Lake consumer probe uses the pinned `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) on a tiny local two-package fixture. The inventory inspected the installed Elan tool bundle, a name-filtered local Nix-store slice, Aeneas Lean pins and the usual home Elan directory. Each source report records exact tool identities, commands, guards and evidence limits.

The public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and comments were fetched again on 2026-09-29 and retained verbatim in the [v30 snapshot](support/live-issue-snapshot-v30.json). #3730 was closed and #3731 open, each with one comment. All four bodies matched v29 and the frozen v22 request snapshot byte-for-byte. #3730 body/comment SHA-256 values are `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values are `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Source report | Investigation | Direct #3730 suggestion | Measured slice |
| --- | --- | --- | --- |
| Incremental-on shared target cancellation | I080 | D06 | Edited A reached a build-script marker; B overlapped and logged a build-directory lock wait; A was SIGTERM-canceled with no LLBC, B completed baseline LLBC and same-target A retry completed edited LLBC, each matching selected cold-oracle bodies. |
| Installed Lean/Lake inventory | I094 | None | No later compatible tuple appeared in the bounded installed locations: bundled 4.29 and 4.30-rc2, one matching 4.30-rc2 Nix-store tuple and Aeneas pins at 4.30-rc2. |
| Two concurrent fresh cache consumers | I089 | F13 | Two source-only roots simultaneously fetched from one seeded read-only artifact cache, passed matched batch checks and returned the same non-null first goal; shared cache and original seed inventories were unchanged. |

All five mapped rows remain **partial**. I080/D06 still need representative stages, repeated cancellation, descendant/lock tracing and an Anneal-owned last-good publication transaction. I094 still needs a deliberately selected later compatible Lean/Lake tuple and a controlled ownership/read-only comparison; local absence does not establish global unavailability. I089/F13 still need the actual content-identified Anneal archive, generated consumers, enforced read-only dependencies with write tracing, representative imports and many-consumer resource scaling. The [row challenge](support/row-challenge-v30.json) retains each exact residual and next prerequisite.

### Deliberate exclusions and unchanged rows

Fourteen adjacent rows receive specific context-only explanations and keep their v29 residual, prerequisite and evidence fields: **D03, F03, M01, F02, F04, F08, F20, I04, I092, I099, I114, I139, I078 and I105**. D03's Cargo subject-selection contract was not newly attested by the canceled target retry. F03/M01 require execution on a later compatible Lean/Lake tuple; this inventory ran none. F02/F04 require a real Anneal archive. F08 and I04 ask for product readiness or cold interactive acceptance beyond a successful tiny goal. F20, I092 and I099 need broader artifact/rebuild/equivalence controls. I114/I139 need representative scale or product acceptance. I078/I105 require pipeline cancellation and transactional recovery beyond one Charon retry. Each exclusion is recorded individually in the ledger.

Each of the other **314 unchanged rows** names its own inherited gate and states that none of these three reports directly exercises it. Thus five direct + 14 context-only + 314 other unchanged = 333. No finite component result changes a status or gate.

## Boundaries

- The I080 marker proves entry into edited A's build script; the logged wait does not timestamp Cargo lock ownership or release. Selected output checks cover five local bodies, not all LLBC fields or generated build-script provenance. Empty selected process groups at one post-run sample do not exclude escaped descendants or later leaks.
- I094's inventory excludes uninspected installation paths, unrelated projects and remote release availability. No comparison of Lake ownership or read-only behavior between versions was run.
- The Lake fixture used two consumers, separate writable producer/build trees and a permission/sandbox protected shared cache. Before/after inventories detect no net file/hash/mtime changes in the cache or original seed, not transient writes or writes elsewhere. The valid run followed a separately retained malformed sandbox wrapper attempt, which provides no Lake result.
- The public issue snapshot establishes request scope at its fetch time. It does not alter the issues or resolve their product-level requests.

## Evidence

- [source-package-inventory-v30.csv](support/source-package-inventory-v30.csv) records SHA-256 for every retained file in published v29 and the three finalized reports. [validation-v30.json](support/validation-v30.json) records input/generated hashes, row/link counts, direct/context IDs, unchanged status/gate counts and source packages.
- The [offline builder](support/build_audit.py) derives all v30 rows from v29 and the preserved live issue text. The [self-checker](support/check.py) compares every inherited field across 333 rows and both matrices, verifies the 159 investigation titles and 174 suggestion/destination mappings against the live text, validates all evidence paths and source hashes, and runs v29 plus the three new source checkers.
- Published v29's row-challenge SHA-256 is `75b9f10d80d54430a0a3872c7915587ee6a6b0e44dc26b0f9bdedae2a1c853ed`. The inherited Anneal source revision is `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`; none of these probes runs it as an end-to-end verification service.

## Revalidation

Run `python3 -B support/check.py` from this package or an unchanged copy of the reference tree. It checks retained evidence without starting Charon, Cargo, Lake, Lean or Anneal. If issue text or source packages later change, preserve v30's exact snapshot and hashes and add a later audit revision.
