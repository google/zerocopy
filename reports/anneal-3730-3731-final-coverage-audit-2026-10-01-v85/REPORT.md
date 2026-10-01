# #3730/#3731 coverage audit v85: published source inventory and R121 probe

## Summary

At published `reference@f6287f7169c5185623c32c3f6922aa40f59644a0`, the frozen #3731 ledger still has **159 investigations**. The related #3730 crosswalk retains **174 suggestions and 345 links**, its challenge has **333 rows**, and the version inventory has **581 rows**. The latest 361-row newer-version crosswalk has **356 exact-claim source reviews, five contextual or paired-component source reviews, and zero unmapped rows**. The separate 83-row source audit covers all **72 source-revision** and **11 prior-comparison** inventory rows, with **21 changed, 55 unchanged, and seven unavailable** results at their mapped source scope. The single R121 malformed Rust-comment fixture gave the same compile status and diagnostic under its original rustc 1.98.1, nightly 2026-05-31, and newer nightly 2026-09-17.

These are source and fixture results at stated revisions. They do **not** mean that all pinned-version runtime behaviors were rechecked or that all requested Anneal V2 product behavior exists. I re-read both live issue pages on 2026-10-01: #3731 remains open and describes 159 consolidated investigations; #3730 is closed as not planned. The inherited issue ledgers remain byte-identical and neither issue was edited.

## Applicability

This is a dated reconciliation of the published [v84 coverage audit](../anneal-3730-3731-final-coverage-audit-2026-09-30-v84/REPORT.md), the [v85 residual source audit](../anneal-3730-3731-residual-38-source-audit-2026-09-30-v85/REPORT.md), the [R121 runtime comparison](../anneal-3731-r121-rust-version-runtime-2026-09-30/REPORT.md), and the [83-row source audit](../anneal-3731-version-source-audit-83-2026-10-01/REPORT.md). Their publication commits are, respectively, `6fe9f8ed36f1bfb474afe091a9799ee29016f667`, `d565370c695a188531bbfdfdd1c5556bc832f1ab`, `b7e455374bce8b656204a81571643808e60c7aea`, and `f6287f7169c5185623c32c3f6922aa40f59644a0`. Each is an ancestor of the frozen reference HEAD. The [manifest](support/validation-v85.json) records the chain and exact report/package hashes.

The 581-row inventory is the frozen classification at `reference@ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. It selects 361 `newer_version_recheck` rows, 72 `source_revision_recheck`, 11 `prior_comparison`, 136 `incidental_or_citation`, and one `no_newer_release` row. The two published version audits address the 361 and 83 selected rows at the source-evidence level; they do not reclassify the 136 contextual reports or R578's no-newer-release case. R443 remains static Lean AArch64 `leantar` evidence without helper execution.

## Findings

### The inherited issue ledger is byte-identical

The [159-row investigation ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v84/support/investigation-final-v80.csv), [174-row suggestion crosswalk](../anneal-3730-3731-final-coverage-audit-2026-09-30-v84/support/3730-crosswalk-final-v80.csv), [333-row challenge](../anneal-3730-3731-final-coverage-audit-2026-09-30-v84/support/row-challenge-v80.json), [inherited issue snapshot](../anneal-3730-3731-final-coverage-audit-2026-09-30-v84/support/live-issue-snapshot-v80.json), and [581-row version inventory](../anneal-3730-3731-final-coverage-audit-2026-09-30-v84/support/version-inventory-ebcdcad-581.csv) are byte-identical to v84. The 345 suggestion links are inherited from that frozen crosswalk and its earlier validation. No status, gate, prerequisite, investigation text, or issue checkbox was changed for this audit.

### The newer-version source crosswalk advances from v84

The [published v85 newer-version crosswalk](../anneal-3730-3731-residual-38-source-audit-2026-09-30-v85/support/newer-version-crosswalk-v85.csv) and [38-row applicability matrix](../anneal-3730-3731-residual-38-source-audit-2026-09-30-v85/support/claim-applicability-matrix-v85.csv) are byte-identical to the published residual audit. They replace v84's 323 exact / 38 contextual classification with **356 exact / five contextual / zero unmapped** across the same 361 IDs and 11 cohorts. The five contextual IDs are R120, R121, R139, R150, and R236. A source diff, including one in a paired component, is evidence about source text; it does not establish a changed runtime result.

### The remaining 83 version rows now have a scoped source audit

The published [83-row status matrix](../anneal-3731-version-source-audit-83-2026-10-01/status-83.csv) binds every `source_revision_recheck` and `prior_comparison` inventory ID to its original report, pinned identities, selected newer source, exact Git object evidence or published review, and an explicit gap. Its **21 changed / 55 unchanged / seven unavailable** counts are scoped to mapped source objects or selected source-review clauses. Its seven unavailable full-claim comparisons remain open at source level, especially historical Lean 4.29/4.30 runtime contrasts and the TypeScript target. Every target runtime in that audit is marked unexecuted, and Anneal product behavior is unassessed.

### R121 adds one exact-target runtime control

The published R121 package reused the unchanged invented `//%` scanner and the same baseline/malformed Rust source bytes. The exact 2026-09-17 nightly was run alongside the original rustc 1.98.1 and 2026-05-31 nightly. All three accepted the baseline, rejected the malformed source with the same unclosed-delimiter diagnostic, and the scanner retained the same complete annotation projection. This narrows one rustc-parser uncertainty for **that fixture**. It does not test compiler-backed annotation attachment, actual Anneal parser behavior, other malformed Rust inputs, or newer Lean/Aeneas behavior. R121 therefore remains contextual in the 361-row source crosswalk.

## Boundaries

The 159-row and 174-suggestion ledgers are inherited, not regenerated from the live page. The read-only [live issue observation](support/live-issue-observation-2026-10-01.json) records visible status/title and the consolidation statement; it is a narrow status/body excerpt, not a full fresh issue export. No issue fields, comments, or checkboxes were edited. No new build, Lean server session, Charon/Aeneas translation, archive extraction, or Anneal V2 end-to-end run was performed for this audit. The R121 result is the only newly incorporated exact-target compiler execution and applies to one small fixture.

Source-review coverage is not a completion percentage for the architectural research backlog. The 159 investigations retain their specific evidence limits and product prerequisites in the frozen ledger. The 83-row audit explicitly distinguishes a moving upstream default branch from a selected release or earlier review snapshot; a current ref observation does not retroactively make an older selected source comparison a current runtime test.

## Evidence

The [validation manifest](support/validation-v85.json) hashes the inherited ledger and crosswalk files at their authoritative published locations, records the four-commit ancestry, and names the two new report hashes, 83-row status hash, and live issue excerpt hash. The [150-file package inventory](support/source-package-inventory-v85.csv) freezes all tracked files in the v84 audit, v85 residual audit, R121 report, and 83-row source report. Its SHA-256 is `9f9873af06f963e0269071727783e34e3218c2446f868957e3b92328d0669c3a`. The manifest SHA-256 is `bef49b55bcf3a2b5d42cb2bc593699a61d96a128f0b879b852c270ce9fc6e48e`. The separate live issue observation is read-only and deliberately records only the visible facts relevant to reconciling the current 159-item scope.

The [checker](support/check.py) validates referenced published bytes, the 159/174/333/581/361/38 row counts, 356/5/0 crosswalk partition, exact five contextual IDs, the 72/11 split, 21/55/7 source statuses, three-compiler R121 fixture result, all 150 published package file hashes, and commit ancestry. The 345-link figure is preserved by the byte-identical suggestion crosswalk and inherited prior audit validation; it is not a newly recomputed issue query.

## Revalidation

From the published checkout, run `python3 -B support/check.py` from this package directory, then `python3 -B tools/reference.py check` at the reference root. For a detached copy of this package, set `ZEROCOPY_REFERENCE_ROOT` to a local `reference` checkout before running the checker. It checks frozen hashes and report ancestry; it does not refresh upstream refs or run the original experiments. To advance a still-open behavior question, run its retained fixture under the specific newer toolchain and record input, environment, executable identities, output, and source provenance in a separate report.
