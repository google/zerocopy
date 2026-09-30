# #3730/#3731 coverage audit v43: nested Lake goal positions

## Summary

The [nested Lake constructor/`have` report](../anneal-3731-lake-nested-constructor-goal-positions-v4-30-0-rc2/REPORT.md) adds bounded direct evidence to **#3731 I043** and **#3730 C02** in published [v42](../anneal-3730-3731-final-coverage-audit-2026-09-29-v42/REPORT.md). One pinned imported proof exposed an outer conjunction, two goals after `constructor`, an inner equality goal, the resumed left goal with a new `hz` hypothesis, and the right `True` goal. Plain and rich APIs agreed on goal counts and displayed contexts at 13 exact positions; a fresh batch process accepted the same source text and reported no theorem axioms. This is one successful nested proofstate fixture, with no restart, reconnect, or Anneal source projection.

All **333 row IDs**, **345 suggestion destinations**, inherited request fields and row order are preserved. Only **I043 and C02** have changed residuals. Both remain **partial** at the **product** gate. Every status, gate and next prerequisite is carried forward unchanged; the other 331 rows retain their v42 residuals.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@29ea19d9dccef4f046d0b53eed0e8dc20b9c9ae7` and its v42 ledger. The source component used installed `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` Lean/Lake 4.30.0-rc2 on macOS arm64. A local Lake dependency defined `depValue := 7`; the proof imported it, ran `constructor`, then used an inner `have hz := by exact h` in the left bullet and `trivial` in the right bullet. The exact proof file opened by the server matched the on-disk source. A separate fresh batch file had identical source bytes and the same prepared import, under a different filename. All queries used one server, one document version and one RPC session.

The [v43 issue snapshot](support/live-issue-snapshot-v43.json) is byte-identical to v42's retained public issue text, originally fetched at `2026-09-30T01:30:04.750897+00:00`; it was **not fetched again**. #3730 body/comment SHA-256 values remain `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values remain `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct I043/C02 mapping

| Row | Direct observation | Remaining scope |
| --- | --- | --- |
| I043 | Thirteen paired positions in a Lake-imported constructor/two-bullet/inner-`have` proof selected the outer conjunction, two post-constructor goals, the inner equality, the outer left goal with `hz`, the right `True` goal, three empty lists and EOF null. Plain/rich counts and displayed contexts matched. Build/setup and fresh same-text batch succeeded. | This is one successful disk-identical nested grid. Combinator branches, whitespace changes, term-proof positions, unsaved nested/error combinations, worker restart/reconnect, RPC reconnect, rich reference lifetime, late/stale responses, exact-version/import fencing and Anneal launcher/source-map integration remain open. |
| C02 | Rich target, case name and hypothesis display matched plain goals at all 13 positions, including two positions with both left and right goals. This extends the separate v42 Lake unsaved macro/error pairs with a branched nested proof. | Rich object dereference/expiry, reference use after worker or RPC reconnect, broader protocol transcript/lifecycle behavior, term/combinator/whitespace positions, and actual generated/projected Anneal proof transport remain open. |

The v42 source's 20 matched pairs covered a separate Lake unsaved macro/error fixture; the new source covers one successful nested proof. An earlier valid-only Lake fixture sampled a nested `have` with one-goal positions, while a direct Lean grid sampled constructor bullets. The new cell combines a compiled local import, two-goal selection and both APIs in a single Lake process. It does not collapse those distinct launch and edit conditions into one product result. **Basis: execution**, source `support/results.json` and checked source bytes; **derived** for the scope distinction across fixtures.

### Unchanged rows

The other **331 rows**, including I079, I075 and I076, preserve their v42 residuals, prerequisites, statuses, gates and evidence fields. Their v43 assessments state that this nested Lake component does not directly exercise their remaining request. All 159 investigation titles, 174 suggestion rows and 345 destinations still match the retained issue text.

## Boundaries

- The source probe retains ordered JSON-RPC requests and replies for this one run. It does not test worker or RPC reconnect, rich reference dereference/expiry, late/stale responses, cancellation, simultaneous clients or a full protocol lifecycle contract.
- The proof is hand-written Lean. It has no Anneal launcher, generated/projected proof document, Rust source map, editor/MCP transport or complete product obligation set. I043 and C02 remain partial at the product gate.
- The 13 positions sample this constructor/bullet/inner-`have` proof only. They do not settle general nested selection rules, combinator branches, whitespace changes, term-proof queries or unsaved nested/error behavior.
- The source preflight measured 25.74% reclaimable memory and 24,636,727,296 free disk bytes; 27 samples over 5.79 seconds observed at most 808,208 KiB process-group RSS. Samples cannot exclude a shorter transient peak. The v43 issue text was inherited, not refreshed.

## Evidence

- [source-package-inventory-v43.csv](support/source-package-inventory-v43.csv) hashes every retained file in published v42 and the reviewed nested Lake source package. [validation-v43.json](support/validation-v43.json) records their hashes, the exact changed IDs and all row/link counts.
- The [builder](support/build_audit.py) derives every v43 row from v42 and checks titles and suggestion destinations against the retained issue text. The [checker](support/check.py) verifies inherited fields, unchanged residuals, source inventory hashes, both source checkers and metadata loading.
- The [source results](../anneal-3731-lake-nested-constructor-goal-positions-v4-30-0-rc2/support/results.json), fixture bytes, fresh batch output, 26 position requests and replies, diagnostics and process cleanup bind the 13 observations.
- Published v42's row-challenge SHA-256 is `ef8779ed218dbe7f8a77c278e0960ccb2e1ed3d59d6c3b02f732b291cbcc6db4`.

## Revalidation

Run `python3 -B support/check.py` from this package to check the retained evidence without starting Lean, Lake or Anneal. Reacquiring the nested source cell requires the pinned binaries, a new absent private work path and its resource gates. The product I043/C02 question still requires paired position queries through the actual version-fenced Anneal launcher and generated source map, with the remaining term, combinator, whitespace, edit/error and reconnect controls plus fresh batch verification of the complete obligation set.
