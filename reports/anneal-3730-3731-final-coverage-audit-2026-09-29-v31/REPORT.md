# #3730/#3731 coverage audit v31: client goal attribution and five-function Lake replay

## Summary

Two finalized execution reports sharpen **four partial rows** in the published [v30 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-29-v30/REPORT.md): investigation **I041** and suggestions **C01, C09**, plus investigation **I148**. A third finalized report records a malformed-manifest probe **refused before execution** at its resource gate; it adds context only and changes no residual. All 333 IDs, 345 #3730→#3731 destination links, inherited request text, statuses and gate categories remain unchanged. The [investigation matrix](support/investigation-final-v31.csv), [suggestion crosswalk](support/3730-crosswalk-final-v31.csv) and [333-row challenge](support/row-challenge-v31.json) append a v31 residual, prerequisite and scope assessment to every row.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

The [goal-envelope replay](../lean-goal-envelope-replay-2026-09-29/REPORT.md) executes a client attribution policy over three previously retained late Lean goal traces, with synthetic adversarial controls. The [five-function Lake replay](../anneal-3731-i148-five-function-lake-replay-2026-09-29/REPORT.md) measures same-path generated-source replay and a one-function positive invalidation control. The [manifest preflight refusal](../anneal-3731-lake-malformed-manifest-preflight-refusal-2026-09-29/REPORT.md) preserves why the selected Lake cell did not run. None executes an Anneal V2 adapter, publication path or actual prepared archive.

## Applicability

The baseline is published `reference@3b549cb1eddebc54896a106c5c94ede6c2c134e5` and its v30 ledger. The goal replay models the recorded `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) server responses; its incarnation names and reordered scenarios are client-assigned model inputs, not extra Lean observations. The Lake replay uses the pinned Charon/Aeneas/Lean/Lake tuple and the prior error-free five-function corpus in one sequential fixed-path consumer. The refusal report has no Lake execution subject beyond its intended pinned setup. Exact fixtures, commands, hashes, timing and limits remain in each source package.

The public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and comments were fetched again at `2026-09-30T00:12:49.939359+00:00` and retained verbatim in the [v31 snapshot](support/live-issue-snapshot-v31.json). #3730 was closed and #3731 open, each with one comment. All four bodies matched v30 and the frozen v22 request snapshot byte-for-byte. #3730 body/comment SHA-256 values are `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values are `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Source report | Direct investigation | Direct #3730 suggestions | Measured slice |
| --- | --- | --- | --- |
| Offline client goal-envelope replay | I041 | C01, C09 | In three retained late-goal traces, an exact client-side submission envelope keeps the V2 `⊢ False` reply current and classifies the later V1 `⊢ True` reply as stale or explicitly historical. Seven synthetic controls per run vary arrival order, source, position, URI and incarnation/request-ID reuse. C09's overlap is at one position. |
| Five-function fixed-path Lake replay | I148 | None | A warm four-module Lake consumer replays after four sequential byte-identical Aeneas output replacements. A Rust `add_one` `x + 1`→`x + 2` mutant changes one generated `Funs.lean` line; Lake rebuilds Funs and dependents while replaying Types, then replays all modules on a no-write pass. |

All four direct rows remain **partial**. I041/C01/C09 still require a real Anneal adapter with authenticated source/import and worker-incarnation identity, live multi-position edits, cancellation and response routing. The replay model's tuple omits import generation and its restart collision is synthetic. I148 still requires Anneal's actual generator and publication path, representative workload, nontrivial proof obligations and source/model provenance; its retained theorems are equality-to-self checks, not Rust refinement. The per-row residual and next prerequisite preserve those limits.

### Context-only evidence and unchanged rows

Fourteen adjacent rows have explicit context-only assessments while their v30 residuals, prerequisites and evidence fields stay unchanged: **E06, E07, F20, I045, I048, I145, I134, I079, I084, I132, I044, I092, F07 and F08**. The I148 source package itself labels E06/E07/F20 `context_only_partial` in its checked `support/summary.json`: Lake replay adds no new generated-source determinism contrast for E06, no semantic-sameness oracle for E07, and no actual Anneal archive/whole-chain accounting for F20. I045/I048/I145/I134/I044 require real worker, import, concurrency or rich-reference behavior beyond the plain-goal model. I079/I084/I132 need provenance or semantic comparators.

The malformed-manifest cell was **not run**. Its preflight measured **25.09%** estimated free memory against a **30%** minimum, so there was no fixture mutation, Lake command, batch control, diagnostic wait or first-goal response. I092/F07/F08 therefore retain their prior residuals; v31 records the refusal as context, not a fail-closed Lake result. The corrected refusal `REPORT.json` SHA-256 is `4728a2ce32a427d6f7e6e619da26dd88f2c4e648b3d57e6421abdeeefb71d15a`.

Each of the other **315 unchanged rows** names its own inherited gate and states that none of these three reports directly exercises it. Thus four direct + 14 context-only + 315 other unchanged = 333. No finite component or refused cell changes a status or gate.

## Boundaries

- Goal-envelope replay processes copied wire records offline. Only the recorded arrival case follows Lean's actual receive order; reorder, same-version mutation and restart cases are synthetic policy tests. A client-assigned incarnation token is not a Lean-authenticated worker ID, and a locally available goal is not a verification verdict.
- The Lake replay is one sequential consumer over the five-function fixture. Byte-identical replacements preserve local trace/OLean hashes and mtimes; the real function mutant changes Funs and downstream traces, though some downstream OLean bytes remain equal despite `Built` labels. This does not establish general LLBC semantic equivalence or Anneal cache-key correctness.
- The refused malformed-manifest cell has no behavioral outcome. Its intended `lake-manifest.json` mutation (`{\n`) was not made, and no retry is represented in this report.
- The public issue snapshot attests request scope at fetch time. It does not alter issue state or reclassify any full request as satisfied.

## Evidence

- [source-package-inventory-v31.csv](support/source-package-inventory-v31.csv) records SHA-256 for every retained file in published v30 and the three new packages. [validation-v31.json](support/validation-v31.json) records input/generated hashes, row/link counts, direct/context IDs, unchanged status/gate counts and source package identities.
- The [offline builder](support/build_audit.py) derives all v31 rows from v30 and preserved live issue text. The [self-checker](support/check.py) compares every inherited field across 333 rows and both matrices, checks 159 investigation titles and 174 suggestion/destination mappings against the live text, validates evidence paths and source hashes, and runs v30 plus all three new source checkers.
- All three new source checkers also passed from relocated copies under `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/coverage-v31/relocated/`. The Lake replay checker was relocated with its adjacent prior I148 corpus because it verifies those retained inputs. All three source `REPORT.json` files passed `reference._load_report` after the refusal metadata correction.
- Published v30's row-challenge SHA-256 is `4eec3f7ecf2bc0e42f33c6d04ae55667c68082195ec026c30c59d0bccd65bd38`. The inherited Anneal source revision remains `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`; none of these reports executes it as an end-to-end service.

## Revalidation

Run `python3 -B support/check.py` from this package or an unchanged copy of the reference tree. It checks retained evidence without starting Lean, Lake, Charon, Aeneas or Anneal. Preserve the exact issue snapshot and source hashes if a later revision adds execution evidence from the refused manifest cell or a production adapter.
