# #3730/#3731 coverage audit v86: Lean diagnostic source delta

## Dated result

At `reference@46b7576360aec884a259666c5bb67d8a87ce48da` on 2026-10-01, the published [v85 coverage audit](../anneal-3730-3731-final-coverage-audit-2026-10-01-v85/REPORT.md) remains the full crosswalk. Its inherited ledger has **159 investigations**, **174 suggestions**, **345 suggestion links**, **333 challenge rows**, and a **581-row version inventory**. This addendum changes none of those rows or any issue checkbox.

The newly published [Lean diagnostic source delta](../lean-incremental-diagnostics-430rc2-to-4341-source-delta-2026-10-01/REPORT.md), committed at `46b7576360aec884a259666c5bb67d8a87ce48da`, compares exact Lean 4.30.0-rc2 and 4.34.1 source. Lean 4.34.1 adds a client opt-in `lean.incrementalDiagnosticSupport` capability and `isIncremental` diagnostic notification semantics: a replacement publication can be followed by append updates for the same document version. The pinned 4.30.0-rc2 path publishes full arrays. This is **source evidence of a version difference**, not an observed 4.34 server transcript or Anneal product result.

The planned runtime A/B was **not executed**. Its fresh resource admission measured **25.7875% estimated reclaimable RAM** and **12,654,592,000 free disk bytes**. Disk exceeded the 10 GiB floor, but RAM did not exceed the required 30% threshold; **no Lean server was launched**. The exact machine-readable [admission snapshot](support/runtime-admission.json) records the page counts, estimator inputs, thresholds, and no-launch decision. The [source report](../lean-incremental-diagnostics-430rc2-to-4341-source-delta-2026-10-01/REPORT.md) retains the two small future open/edit fixtures. A new guarded run, including client capability absent/false/true controls and raw ordered diagnostic notifications, remains pending.

## Issue and coverage state

I re-read the public issue pages on 2026-10-01. [#3731](https://github.com/google/zerocopy/issues/3731) is **Open** and states that #3730's scope is consolidated into 159 investigations, including I145–I159 and the 174-entry crosswalk. [#3730](https://github.com/google/zerocopy/issues/3730) is **Closed as not planned**. The small [read-only observation](support/issue-observation-2026-10-01.json) records the visible titles, states, and relevant #3731 excerpt. It is not a fresh byte-for-byte extraction of the full issue bodies. Neither issue was edited.

The v85 [validation manifest](../anneal-3730-3731-final-coverage-audit-2026-10-01-v85/support/validation-v85.json) remains the authority for the inherited 159/174/345/333/581 counts and its 361-row newer-version and 83-row source-review partitions. The Lean source delta supplements one pinned component behavior; it does not mean that all version-specific runtime behavior was rechecked, that all 159 investigations have empirical results, or that Anneal V2 product prerequisites are complete. No completion percentage is inferred here.

## Provenance and revalidation

The [delta manifest](support/delta.json) binds the v85 and Lean packages to their exact publication commits, Git tree IDs, report SHA-256 values, the live issue observation, and the denied admission facts. The v85 publication commit is `6d02a803cbe2e26a1b7881d98245f7eb48e2b309`; the Lean source-delta publication and current observed HEAD are `46b7576360aec884a259666c5bb67d8a87ce48da`. The [checker](support/check.py) checks the committed bytes and inherited counts without downloading software or launching a server.

From this package run `python3 -B support/check.py --reference-root /path/to/reference`; `REFERENCE_ROOT` is also accepted. The checker needs a local `reference` checkout at or after the Lean source-delta commit. The admission snapshot substantiates the decision not to launch, not a performance conclusion. A later successful runtime comparison needs its own resource snapshot, binary hashes, wire transcripts, and report.
