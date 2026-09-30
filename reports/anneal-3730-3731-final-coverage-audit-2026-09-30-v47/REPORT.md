# #3730/#3731 coverage audit v47: sequential Charon destination reuse

## Summary

One [sequential Charon destination report](../anneal-3731-i076-sequential-shared-destination-2026-09-30/REPORT.md) adds bounded profile/cfg output evidence to the published [v46 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v46/REPORT.md). Only **I020 and I076** receive revised residual descriptions. **D07** receives bounded context while its residual stays unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links**, issue fields and row order are preserved. Every status, gate and next prerequisite remains unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `24eb9c0b5896c54d24884755f68dfe5b8b077d20`. This audit derives from its v46 row ledger and copies its retained [issue snapshot](support/live-issue-snapshot-v47.json) exactly. The inherited snapshot records #3730 closed and #3731 open and had been freshly fetched for v46. **No additional issue fetch was performed for v47**; this audit asserts exact inheritance, not a new live-state observation.

The new source package ran the pinned Charon 0.1.210/Cargo/rustc binaries identified by SHA-256 in that report. It used one unchanged Rust library and separate release/cfg controls, then two serial orders at initially absent shared LLBC destinations. The checked-in V2 slug equality remains source-level evidence from an earlier package; no V2 CLI, publisher or proof consumer was exercised in the new cell.

## Findings

| Row | New bounded evidence | Remaining decision |
| --- | --- | --- |
| I020 | Release and cfg Charon requests with distinct selected model literals both exited 0 at the same destination; each serial order's final output contained the later subject's selected literals. This replaces the old residual's “no observed overwrite” wording for Charon. | The V2 root selector, slug helper, extraction request, publication and proof-context selector still need to be integrated and tested. |
| I076 | Two serial orders directly narrow Charon destination ownership for profile/cfg variants; a second success changed the selected model at that path. | Complete compilation-unit identity, concurrent producer ordering, collision rejection and Anneal publisher behavior remain open. |
| D07 (context) | The profile/cfg matrix gains a serial shared-destination Charon cell in both orders. | The v46 residual is preserved because Anneal invalidation, dependency fanout, concurrent producers and proof consumers remain open. |

The source report's six commands each exited 0 and emitted parseable LLBC without `has_errors`. In both orders, the second snapshot has the later subject's selected `profile_value`/`config_value` literals (`11/23` or `7/29`). The two output paths were initially absent, source-file hashes agree in all six LLBCs, the shared pair uses exactly one path, and recorded command intervals do not overlap. **Basis: execution through the source package, inherited and derived row mapping in this audit.**

## Boundaries

I020, I076 and D07 remain **partial** at the **product** gate. D07's residual is unchanged. No new result changes an issue checkbox, status, gate or prerequisite. Sequential Charon destination replacement is not evidence that Anneal currently publishes the same path, fails to reject collisions, selects a stale model, or permits a wrong-subject proof. It does not settle concurrent-write atomicity or ordering. The issue snapshot is inherited, so this report does not assert that public issue text remained unchanged after the v46 fetch.

## Evidence

[source-package-inventory-v47.csv](support/source-package-inventory-v47.csv) hashes every retained file in the v46 parent audit and the exact new Charon report. [validation-v47.json](support/validation-v47.json) records parent tip, inherited issue-snapshot relation, input/generated hashes, counts, changed IDs and source packages. The [builder](support/build_audit.py) derives each v47 row from v46, checks issue headings and destination mappings, and writes the ledgers. The [checker](support/check.py) verifies inheritance, the two changed residuals, unchanged D07 residual, metadata, source hashes, inventory and the Charon source-package checker. It does not rerun Charon.

## Revalidation

Run `python3 -B support/check.py` from this package, then `python3 tools/reference.py check` from the corpus root. This validates retained evidence and the candidate catalog/structure without acquiring a new experiment or issue snapshot. A new live issue comparison requires a fresh public fetch. The next product work remains the inherited Anneal compilation-unit key, output ownership, invalidation and proof-consumer controls.
