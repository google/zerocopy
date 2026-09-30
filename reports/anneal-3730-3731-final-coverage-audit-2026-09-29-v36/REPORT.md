# #3730/#3731 coverage audit v36: Lake unsaved macro and error positions

## Summary

The [Lake unsaved macro/error report](../anneal-3731-lake-unsaved-macro-error-positions-v4-30-0-rc2/REPORT.md) adds direct, bounded evidence to **#3731 I043** and **#3730 C02** in published [v35](../anneal-3730-3731-final-coverage-audit-2026-09-29-v35/REPORT.md). One pinned Lake server opened a valid imported proof, then received unresolved, syntax-error, and restored full-text versions without changing the proof file on disk. At five exact positions in each version, plain and rich goal queries agreed on seven one-goal, seven empty-list, and six null categories. The syntax-error version returned *no goals* at one macro-body position while a fresh batch process rejected the same source text. These are local selection results, not whole-file acceptance.

All 333 row IDs, 345 suggestion destinations, inherited request fields and row order are preserved. Only I043 and C02 have changed residuals. Their statuses remain **partial**, their gate remains **product**, and every prerequisite is carried forward unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@db2686d050caf5870e60118c80df713638cdd42d` and its v35 ledger. The source component ran installed `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` Lean/Lake 4.30.0-rc2 on macOS arm64. A local Lake dependency supplied `depValue`; the proof used one tactic macro expanding to `exact`. Separate batch files contained the exact solved, unresolved, and syntax-error buffer text under the same prepared import, although their filenames differed from the open proof URI. The source report preserves the wire transcript, diagnostics, source and binary identities, and resource observations. It did not run the Anneal launcher or a generated Rust-to-Lean source map.

The public #3730/#3731 issue bodies and comments in [the v36 snapshot](support/live-issue-snapshot-v36.json) are byte-identical to v35's retained snapshot, fetched at `2026-09-30T01:30:04.750897+00:00`. They were **not fetched again for v36**. The audit uses their preserved text to check all titles and suggestion destinations. #3730 body/comment SHA-256 values remain `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values remain `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Row | Direct observation | Remaining scope |
| --- | --- | --- |
| I043 | One Lake-imported same-URI run queried 20 paired positions across solved macro, unresolved macro, syntax-error and restored versions. Plain/rich categories and displayed context matched; fresh batch exits were 0/1/1 and live error counts were 0/2/1/0. An empty goal list at the syntax-error macro body did not imply batch success. | The combined cell did not test nested goals/tactics, combinators, whitespace changes, term proofs, worker restart/reconnect, or RPC reconnect. Actual Anneal generated/projected proof, source map, launcher, exact-version/import fence and transport remain open. |
| C02 | The same 20 paired rich-versus-plain queries extend the prior seven-pair valid Lake fixture and separate direct Lean recovery grid to a Lake-imported unsaved macro/error combination. Rich hypothesis/target display matched each nonempty plain goal. | Rich object dereference/expiry and reference use after worker or RPC reconnect remain open, as do nested/combinator/whitespace/term positions and Anneal generated/projected proof integration. |

The new component does not erase the earlier distinct controls. The v35 valid-only Lake report covers nested tactics and a within-`simpa` target change; direct Lean reports cover unsaved error/recovery and a simple macro under different launch conditions. The current matrix combines one local import, unsaved macro/error edits, and both goal APIs in one Lake server. **Basis: execution** in the source report and its retained wire/batch evidence; **derived** for the distinction between local goal availability and whole-file success.

### Unchanged rows

The other **331 rows** preserve their v35 residual, prerequisite, status, gate and evidence fields. Their new v36 assessment says this Lake component does not directly exercise their remaining request. All 159 investigation titles, 174 #3730 suggestion rows and 345 destinations still match the retained issue text.

## Boundaries

- One flat, single-goal tactic macro and five fixed positions were queried per version. Nested goals/tactics, combinators, whitespace changes and term-proof positions were not part of this combined Lake/unsaved cell.
- One worker and one RPC connection served the run. Worker restart/reconnect, RPC reconnect, rich reference dereference/expiry and use after reconnect were not tested.
- This is a hand-written Lean fixture. It has no Anneal launcher, generated/projected proof, Rust source map or integrated editor/MCP path. I043 and C02 remain partial at the product gate.
- The v36 issue snapshot reuses v35 bytes; it does not attest issue state after the retained fetch time. No issue or product state was changed.

## Evidence

- [source-package-inventory-v36.csv](support/source-package-inventory-v36.csv) hashes every retained file in published v35 and the corrected Lake source package, including its `REPORT.md`. [validation-v36.json](support/validation-v36.json) records input and generated hashes, exact direct IDs, and row/link counts.
- The [builder](support/build_audit.py) derives every v36 row directly from v35 and checks all 159 investigation titles, 174 suggestion destinations and 345 links against the retained public issue text. The [checker](support/check.py) checks inherited fields, unchanged residuals, inventory hashes, both source checkers and metadata loading for v35, the Lake source and v36.
- The source report's [results](../anneal-3731-lake-unsaved-macro-error-positions-v4-30-0-rc2/support/results.json), fixture bytes, ordered protocol events, batch outputs and checker bind the 20 paired observations. The source report's resource preflight was 22.41% reclaimable memory and 36,792,500,224 free disk bytes; 40 RSS samples over 8.8 seconds observed at most 830,720 KiB across the probe/server process groups. The sampled maximum does not exclude a shorter transient peak.
- Published v35's row-challenge SHA-256 is `29b22c253ef7070922cb27072cc064e8a56144f5cf7e6a3e302a8b7ee1997818`.

## Revalidation

Run `python3 -B support/check.py` from this package. It verifies retained evidence without starting Lean, Lake or Anneal. Reacquiring the Lake source cell is separate and subject to its pinned binaries and resource guards. The product-level I043/C02 question requires paired position queries through the actual Anneal launcher and generated source map, with the remaining nested, combinator, whitespace, term-proof and reconnect controls plus fresh batch verification.
