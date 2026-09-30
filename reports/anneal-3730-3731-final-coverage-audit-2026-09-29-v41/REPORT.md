# #3730/#3731 coverage audit v41: Aeneas lexical declaration blocks

## Summary

The [retained Aeneas declaration-block report](../anneal-3731-aeneas-declaration-block-diff-2026-09-29/REPORT.md) adds bounded direct evidence to **#3731 I083 and I084** in published [v40](../anneal-3730-3731-final-coverage-audit-2026-09-29-v40/REPORT.md). It compares head-through-body text of 83 lexically delimited generated Lean blocks across seven retained Aeneas generations. Six base-versus-mutation contrasts distinguish changed, unchanged, added and removed block text and moved declaration-head lines, while the original published report compared whole-file bytes and inventoried heads. These name-matched slices do not authenticate Rust-item→Lean-declaration identity or prove semantic equivalence or safe reuse.

All **333 row IDs**, **345 suggestion destinations**, inherited request fields and row order are preserved. Only **I083 and I084** have changed residuals. Both remain **partial**, and all gates and next prerequisites are carried forward unchanged. **E11 is context only**: its crosswalk points to I083, but this offline text comparison does not implement a restricted finer-grained Aeneas prototype or reusable producer API. E11 and the other 330 rows retain their v40 residuals.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@1332bf21478d8418403d306a7884b653cd735eea` and its v40 ledger. The source report reanalyzes exact Rust, LLBC and Lean bytes retained by the earlier one-shot CLI Aeneas identity-manifest probe. Its original producer used pinned Charon 0.1.210 and Aeneas nightly-2026.06.03. This comparison used guarded offline Python only; it did not run Charon, Aeneas, Cargo, rustc, Lean, Lake, Anneal, a server or network request.

The [v41 issue snapshot](support/live-issue-snapshot-v41.json) is byte-identical to v40's retained public issue text, originally fetched at `2026-09-30T01:30:04.750897+00:00`; it was not fetched again. #3730 body/comment SHA-256 values remain `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values remain `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct I083 mapping

A function-body edit changes the lexical `step` block while the caller `use_step` remains textually equal. A type-shape edit changes `Wrap` and its `Bump` method, while `use_bump` stays textually equal. A trait-implementation edit changes that method only; a recursive-group edit changes `even` while its caller `odd` stays textually equal. Helper insertion adds one block with 12 prior blocks equal, and deletion removes `step`/`use_step` with ten remaining blocks equal. This decomposes whole-file differences into textual block observations in one tiny fixture. It does not establish producer-supported item-level reuse, a sound dependency closure, semantic equivalence or an Anneal cache. I083's product gate and next prerequisite remain unchanged. **Basis: execution** of the source package's retained-data comparator.

### Direct I084 mapping

The same comparison records exact name-matched block hashes and declaration-head line movement. Helper insertion adds `helper`, leaves the old 12 head-through-body slices byte-equal and moves five head lines. Deletion removes two names, leaves ten slices byte-equal and moves three head lines. Function, type, trait-implementation and recursive edits change one, two, one and one common block respectively. The lexical names and comments are hints, not an authenticated compiler mapping; the result does not establish arbitrary generated-name/signature stability, annotation migration or Lean elaboration behavior. Existing v40 namespace-move evidence remains separate and unchanged. I084's product gate and next prerequisite remain. **Basis: execution** of the same retained-data comparator.

### E11 context and unchanged rows

E11 maps to I083 in the #3730 crosswalk, but its restricted-prototype request requires a real reusable producer API or measured trusted adapter and product economics. The current report runs no cache or same-process Aeneas call. Its residual, status, gate, prerequisite and evidence fields are unchanged. The other **330 rows** likewise retain their v40 residuals and prerequisites. All 159 investigation titles, 174 suggestion rows and 345 destinations still match the retained issue text.

## Boundaries

- The fixture-scoped delimiter starts at each generated declaration head and stops before a following source comment, declaration head or lexical `end`, excluding trailing blank separators. It omits preceding attributes/comments, imports, namespace and mutual wrappers, options and proof context. Equal block text therefore does not mean equal whole-file bytes or equal Lean elaboration.
- The copied source manifest provides heads and coarse source-comment hints, not authenticated Rust→Charon→Aeneas→Lean declaration identity. Common lexical names are comparison keys only.
- No module move, broad name/signature corpus, real finer-grained cache, dependency-graph proof, semantic oracle, Anneal integration or same-process producer behavior was tested.

## Evidence and revalidation

- [source-package-inventory-v41.csv](support/source-package-inventory-v41.csv) hashes every retained file in published v40 and the new declaration-block source package. [validation-v41.json](support/validation-v41.json) records the published baseline, input and generated hashes, two direct IDs, and row/link counts.
- The [builder](support/build_audit.py) derives every v41 row from v40 and checks issue titles and suggestion destinations against the retained snapshot. The [checker](support/check.py) verifies inheritance, unchanged residuals, inventory hashes, both source checkers and metadata loading.
- The source report's [comparison record](../anneal-3731-aeneas-declaration-block-diff-2026-09-29/support/comparison.json), copied seven Rust/LLBC input pairs, 21 raw Lean outputs, original source results and checker bind 83 lexical slices and six contrasts. Its guarded Python run sampled minimum 25.1751% reclaimable memory, peak measured self RSS 22,708,224 bytes and elapsed 0.0730 seconds.
- Published v40's row-challenge SHA-256 is recorded in this report's metadata and verified by the checker.

Run `python3 -B support/check.py` for offline revalidation. Reacquiring the source analysis requires exact retained source hashes and a fresh >20% reclaimable-memory preflight under its 64 MiB RSS and five-second caps. Product-path questions require separate guarded producer experiments.
