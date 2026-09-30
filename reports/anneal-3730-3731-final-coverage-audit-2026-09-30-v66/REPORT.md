# #3730/#3731 coverage audit v66: preseeded manifest server readiness

## Summary

This audit inherits all 333 rows from the published [v65 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v65/REPORT.md) at current reference parent `57155f6541e478f201ae47d8a27da2f3d448df5e`. The new [I092 three-manifest server report](../anneal-3731-i092-preseeded-manifest-server-readiness-2026-09-30/REPORT.md) adds a valid live-goal control and two invalid-manifest `didOpen` controls. The invalid cells produced Lake setup diagnostics and `null` goals after bounded waits but did not reach final processing-empty quiescence. I092 receives one direct appended residual; F07 and F08 receive bounded context while their residuals remain unchanged. No status, gate, or prerequisite changes.

## Applicability

The experiment is a tiny private Lean/Lake 4.30.0-rc2 fixture. It does not use the actual Anneal archive or product launcher. The v65 public GitHub REST snapshot is copied byte-for-byte under [support/](support/) for stable issue text and crosswalk validation; no fresh issue read was made for v66. Its issue state should therefore be interpreted as the v65 observation, not a new September 30 status check.

## Findings

The inherited ledger still has 159 investigations and 174 suggestions, with 345 #3730→#3731 links. All 333 IDs, original request text, status, gate category, and next prerequisite fields are preserved. Only I092's `v66_specific_remaining_delta` changes from its v65 value, by appending the new controlled observations and the eight-second readiness limit. F07's fail-closed product path and F08's readiness product path gain links to the report as bounded context. Their inherited residuals remain unchanged. The generated [row challenge](support/row-challenge-v66.json), [investigation ledger](support/investigation-final-v66.csv), and [suggestion crosswalk](support/3730-crosswalk-final-v66.csv) state the assessment for each row.

## Boundaries

The invalid-manifest `plainGoal` results are `null` after an eight-second diagnostic wait, without a final quiescence observation. They do not establish permanent goal absence, general fail-closed behavior, or product readiness. The original preseeded artifacts and source are one local two-package fixture. The inherited F07/F08 product gates remain in place until the actual Anneal prepared consumer and broader malformed/missing/stale artifact cases are exercised.

## Evidence

The [source inventory](support/source-package-inventory-v66.csv) hashes the v65 ledger package and every file in the new report package, including raw server transcripts. [validation-v66.json](support/validation-v66.json) records parent identity, input/generated hashes, row counts and the exact changed ID sets. [build_audit.py](support/build_audit.py) derives the v66 append-only fields; [check.py](support/check.py) checks all inherited fields, source hashes, issue text mapping and the new source report's offline checker.

## Revalidation

From this report's `support/` directory, run `python3 -B check.py`. From the reference root, run `python3 tools/reference.py check` after regenerating `CATALOG.json`. Publication requires independent review and a single candidate commit whose parent is the observed reference tip; this package is presently a local candidate.
