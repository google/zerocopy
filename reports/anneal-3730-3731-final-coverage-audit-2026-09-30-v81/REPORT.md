# #3730/#3731 coverage audit v81: frozen newer-version inventory

## Scope and result

This compact audit reconciles the frozen `reference@ebcdcad` [581-row inventory](support/version-inventory-ebcdcad-581.csv) against source-review matrices available at candidate parent `d16440e5a6e12e004a3849938cc75202da82bb6f`. Exactly **361** rows have classification `newer_version_recheck`, across 11 cohorts. [The row crosswalk](support/newer-version-crosswalk-v81.csv) identifies each inventory ID, original report path, exact source matrix, relation and coverage status. R578 is separately classified `no_newer_release` and is outside this 361-row set.

| Coverage status | Rows |
| --- | ---: |
| Exact-claim source review | 319 |
| Contextual or paired-component source coverage only | 39 |
| No mapped newer source review | 3 |

The Aeneas compatible-bundle matrix distinguishes `direct_or_full_bundle`, `paired_component`, and `context_only`. This audit carries those labels into the crosswalk. Other frozen-cohort matrices identify exact selected inventory rows in the Charon, Lean/Lake, Rust/Cargo, and mathlib source reviews. A row's appearance in a matrix is **not** itself a newer runtime result. R443's separate Lean AArch64 leantar report supplies static architecture evidence only; neither helper was executed. The Lean previous-comparison matrix is retained as additional source context where present.

## Explicit gaps and limits

- **R348** (Cargo compilation-subject identity), **R349** (Cargo feature resolution and metadata), and **R352** (Cargo unit graphs and rustc invocations) have no mapped newer source-review matrix or executed recheck.
- **R350** has paired-Charon source context in the Aeneas matrix, but no Cargo-specific claim revalidation. Its status is contextual/paired-component only.
- Several mixed-stack rows have contextual or paired-component coverage without an exact claim review. Their individual matrix relations are explicit in the crosswalk.
- These reviews are source and release inspections. This inventory audit performs no new build, install, fixture run, runtime comparison, or production integration. It cannot retire an at-pin workaround or promote a #3730/#3731 disposition on that basis.

## Inherited issue state and preservation

The [v80 audit](../anneal-3730-3731-final-coverage-audit-2026-09-30-v80/REPORT.md) remains the issue-ledger base. This package copies its [159 investigation rows](support/investigation-final-v80.csv), [174 suggestion rows and 345 destination links](support/3730-crosswalk-final-v80.csv), [333-row challenge and all inherited fields](support/row-challenge-v80.json), and [issue snapshot](support/live-issue-snapshot-v80.json) byte for byte. Their existing statuses, residuals and prerequisites remain unchanged. No GitHub issue was fetched or modified.

The [validation manifest](support/validation-v81.json) records frozen input and inherited byte hashes. Run `python3 -B support/check.py` in this package, then `python3 -B tools/reference.py check` at the reference root. This is an uncommitted candidate, with no publication action.
