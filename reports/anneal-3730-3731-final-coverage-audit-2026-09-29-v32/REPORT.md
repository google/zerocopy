# #3730/#3731 coverage audit v32: changed Lean source with identical rebuilt OLean

## Summary

The finalized [syntax-equivalent rebuild report](../anneal-3731-i147-syntax-equivalent-rebuild-2026-09-29/REPORT.md) adds direct, bounded evidence to **#3731 I147** and **#3730 C06**. Its equal-length noncomment edit rebuilt a local Lean module to a byte-identical OLean while source, ILean and Lake trace bytes changed. All 333 row IDs and 345 suggestion destinations in published [v31](../anneal-3730-3731-final-coverage-audit-2026-09-29-v31/REPORT.md) remain, as do every inherited request field, status, gate category and next prerequisite. Both changed rows remain **partial**.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

The [investigation matrix](support/investigation-final-v32.csv), [suggestion crosswalk](support/3730-crosswalk-final-v32.csv) and [333-row challenge](support/row-challenge-v32.json) append v32 fields to every row. Exactly two residuals change; the other 331 explicitly retain their v31 residual and prerequisite.

## Applicability

The baseline is published `reference@e26a9414ab48844eeb95b91ee8b743046c8a8982` and its v31 ledger. The new component executed pinned `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) in a private one-module Lake project with direct Lean server and fresh batch controls. The source report identifies exact source, OLean, ILean, trace and binary hashes. It did not execute the Anneal V2 product or an Anneal archive.

Public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and comments were fetched again at `2026-09-30T00:42:45.450444+00:00` and retained verbatim in the [v32 snapshot](support/live-issue-snapshot-v32.json). #3730 was closed and #3731 open, each with one comment. Body and comment bytes match v31. #3730 body/comment SHA-256 values are `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values are `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Row | Direct observation | Remaining scope |
| --- | --- | --- |
| I147 | `def selected : Nat := 7` changed to equal-length `def selected:Nat := 0x7`; Lake rebuilt `Dep` and changed its OLean mtime, while the baseline and rebuilt 4,616-byte OLean files had identical SHA-256 `c363ec99438400519e766fea241aaee6b7bafc2d593f5db9fd740bb5b7e69f62`. Source, ILean and trace hashes differed. Resident, newly opened, reopened and fresh-server queries plus fresh batch agreed on value 7. | Broader timestamps, options/native/setup identity and Anneal freshness policy. |
| C06 | The same changed-source, identical-rebuilt-OLean observation directly exercises the suggestion's component contrast. | Actual Anneal producer identity, complete environment provenance and publication policy. |

The source report's longer parenthesized full Lake/server attempt preserved the proof/value controls but yielded an OLean differing by two bytes. Its separate direct-compiler screen found other syntax variants with different OLean bytes; those variants did not run through the full server control. These are **negative byte-identity controls**, not more successful same-artifact cells or a general semantic equivalence rule. C05's changed-artifact/unchanged-source question, E10's external-model question, and all other rows retain their v31 assessment. **Basis: execution** in the source report and item-by-item derivation in this audit.

### Unchanged rows

For each of the other **331 rows**, the appended v32 assessment states that this syntax-level local rebuild does not directly exercise its remaining request. Its v31 residual, prerequisite, status, gate and evidence fields are preserved verbatim. Neither a component proof result nor byte-identical OLean promotes a full Anneal row to complete.

## Boundaries

- This is one private Lake module and a direct Lean server. It does not test an Anneal-generated proof, archive, consumer ownership contract or integrated worker refresh rule.
- OLean byte equality does not imply equal source provenance, ILean, trace, native setup, options or complete imported environment. The measured ILean and trace changed.
- The resident and fresh goal/value controls agree for this selected definition. They do not prove that all equivalent syntax edits have identical artifacts or that every worker refresh path is safe.
- The public issue snapshot preserves the request scope at fetch time. No issue state or product decision was changed.

## Evidence

- [source-package-inventory-v32.csv](support/source-package-inventory-v32.csv) hashes every retained file in published v31 and the new syntax report. [validation-v32.json](support/validation-v32.json) records input and generated hashes, counts and exact direct IDs.
- The [builder](support/build_audit.py) derives v32 from v31 and verifies 159 investigation titles, 174 suggestion destinations and 345 links against the refreshed public text. The [checker](support/check.py) checks every inherited field and row, source hashes, issue snapshot and both source package checkers; it also calls `reference._load_report` on v31, the source report and this audit.
- The source report's [transcript](../anneal-3731-i147-syntax-equivalent-rebuild-2026-09-29/support/transcript.json), retained OLean/ILean/trace specimens and checker bind the claimed same-artifact cell and its negative controls. Its metadata and checker also passed from a relocated copy during this audit's validation.
- Published v31's row-challenge SHA-256 is `9c1b9741f9d5f4a92fa899ed2ad79d6a9f23177963ec4412e0f5df9b5189603d`. The inherited Anneal source revision remains `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`.

## Revalidation

Run `python3 -B support/check.py` from this package. It checks retained evidence without launching Lean, Lake, Charon, Aeneas or Anneal. Reacquiring the source experiment is a separate observation and requires its report's pinned-tool and resource guards.
