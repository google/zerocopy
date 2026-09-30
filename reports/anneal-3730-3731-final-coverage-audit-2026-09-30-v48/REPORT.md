# #3730/#3731 coverage audit v48: concurrent Charon destination cell

## Summary

One [concurrent Charon destination report](../anneal-3731-i076-concurrent-shared-destination-2026-09-30/REPORT.md) adds a bounded simultaneous-producer outcome to the published [v47 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v47/REPORT.md). Only **I020 and I076** receive revised residuals; **D07** receives context with its residual unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links**, issue fields and row order are preserved. Every status, gate and next prerequisite remains unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `c22836d6c4f2b8c8b37ae7626795412afc695b01`. This audit derives from its v47 row ledger and copies its retained [issue snapshot](support/live-issue-snapshot-v48.json) exactly. That inherited snapshot records #3730 closed and #3731 open. **No new public issue fetch was performed for v48.**

The new source package reused v47's exact profile/cfg fixture and separate controls, with matching source and binary hashes. It ran one guarded concurrent pair of Charon `cargo` requests into one initially absent LLBC path with private Cargo targets. It did not invoke the checked-in V2 CLI, Anneal publisher or proof consumer.

## Findings

| Row | New bounded evidence | Remaining decision |
| --- | --- | --- |
| I020 | Both release and cfg Charon process groups were sampled live simultaneously; both commands exited 0. After both settled, the shared LLBC parsed cleanly and contained release `11/23` selected literals rather than cfg `7/29`. | Connect V2 root/slug selection to an Anneal extraction request and proof-context subject selector; reject wrong-subject results. |
| I076 | One concurrent profile/cfg destination cell produced one complete selected model without a reported command error. | The file was inspected only after both processes settled. Write order, in-flight atomicity, repeated schedules, collision rejection, complete unit identity and Anneal output ownership remain open. |
| D07 (context) | The compilation-subject matrix gains one actual simultaneous Charon producer pair. | Its v47 residual remains unchanged because Anneal invalidation, dependency fanout, publisher arbitration and proof consumers remain open. |

The retained [source result](../anneal-3731-i076-concurrent-shared-destination-2026-09-30/support/results.json) includes six samples, five of which show nonzero RSS for both PID groups. Each verbose stderr has one `charon-driver rustc` line with the expected release/cfg discriminator. Both processes exited 0, and the final 5,592-byte LLBC was parseable with `has_errors: false` and the unchanged source hash. **Basis: execution in the source package, inherited and derived row mapping in this audit.**

## Boundaries

I020, I076 and D07 remain **partial** at the **product** gate. D07's residual is unchanged. The final release-model output does not identify the last file writer or prove atomic replacement: no in-flight snapshot, write syscall trace, repeated schedule or consumer read was captured. No result changes an issue checkbox, status, gate or prerequisite. The inherited issue snapshot does not establish public issue state after the v47 fetch.

## Evidence

[source-package-inventory-v48.csv](support/source-package-inventory-v48.csv) hashes all retained files in the v47 audit and the exact new Charon report. [validation-v48.json](support/validation-v48.json) records the parent tip, inherited issue snapshot, input/generated hashes, counts, changed IDs and source packages. The [builder](support/build_audit.py) derives the v48 rows from v47 and checks the issue headings and destination mappings. The [checker](support/check.py) verifies inheritance, the two changed residuals, unchanged D07 residual, metadata, source hashes, inventory and the Charon source-package checker. It does not rerun Charon.

## Revalidation

Run `python3 -B support/check.py` from this package, then `python3 tools/reference.py check` from the corpus root. A new live issue comparison requires a fresh public fetch. The product prerequisites remain the inherited compilation-unit key, output ownership, invalidation and proof-consumer controls.
