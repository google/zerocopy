# #3730/#3731 coverage audit v67: bounded source/spec synthesis

## Summary

This audit inherits the published [v66 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v66/REPORT.md) at reference parent `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. The new [41-package source/spec synthesis](../anneal-3731-source-spec-synthesis-2026-09-30/REPORT.md) maps bounded design evidence to 19 of 23 triaged #3731 investigations. I057, I059, I061 and I062 gain no new ID-specific source evidence. Exact inherited destinations give 48 #3730 suggestions related source context. No row changes status, gate, residual or next prerequisite; no source analysis is promoted to product validation.

## Lineage clarification

The v66 report called `57155f6541e478f201ae47d8a27da2f3d448df5e` its “current reference parent.” That was its **v65 ledger source commit**, not its final published Git parent. Git shows v66 commit `ebcdcadb63fefd1e6c0f46cb2030270ae3232837` has parent `0c504d98f5abafcbbd1460738e6d753378a6460e`; that parent had added the J024 LCF source report after `57155f654`. The v66 audit's public issue snapshot and row basis remained the older v65 snapshot, so v66 did not assess J024. This audit records the correction without altering v66 and includes J024 among its 41 source packages. The carried [issue snapshot](support/live-issue-snapshot-v67.json) is still the v65 observation; no new GitHub issue read was made.

## Findings

The [row challenge](support/row-challenge-v67.json) preserves all 333 v66 rows and every prior field. The [investigation ledger](support/investigation-final-v67.csv) retains all 159 I001–I159 rows; the [suggestion crosswalk](support/3730-crosswalk-final-v67.csv) retains all 174 suggestions and 345 exact #3730→#3731 destination links. Status counts, gate categories, original request text, residuals and prerequisites are unchanged. New v67 fields distinguish source/spec design context from no new evidence. The four no-new investigations have empty new-evidence lists. A #3730 suggestion receives context only if at least one of its inherited destination IDs is among the 19 mapped investigations. The 48 such suggestion rows cite the synthesis as **context through a destination**, not a run of that suggestion.

The source synthesis distinguishes useful mechanisms and contradictions: RLS versus compiler-backed editor services; fine-grained query graphs versus opaque tool dependencies; immutable realized state versus mutable publication and lifetime roots; LCF-style checked proof authority versus SMT oracle acceptance; and event hints versus authoritative state rereads. These narrow design questions for I001, I002, I005, I007, I009–I011, I015, I020, I056, I058, I060, I063, I064, I096, I144, I145, I157 and I159. Product and representative workload prerequisites inherited from v66 remain in force.

## Evidence and limits

The [source package inventory](support/source-package-inventory-v67.csv) hashes the full v66 audit package and the new synthesis package. The latter's [source census](../anneal-3731-source-spec-synthesis-2026-09-30/support/source-census.json) hashes every file in all 41 source reports. [Validation](support/validation-v67.json) records actual parent and published-v66 lineage, inherited input hashes, generated output hashes, counts and exact mapped/no-new/context ID sets. The offline [builder](support/build_audit.py) derives v67 fields from v66 and the source map; [checker](support/check.py) validates preservation and both source-package checks.

These are published-source, paper and pinned-code observations. They do not execute the Anneal V2 engine, editor projection, server, proof acceptance path, or alternate architecture on matched workload. They establish neither product completion nor a universally minimal schema. The v65 issue snapshot remains historical. Any future rebase or remote advance requires rebuilding validation and inventory against the actual commit parent, then regenerating the catalog and checking that report lineage language agrees with Git. A bounded invalid-server `result: null` with missing quiescence must remain labeled as such.

## Revalidation

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the reference root. This is an uncommitted publication candidate; no issue text was edited.
