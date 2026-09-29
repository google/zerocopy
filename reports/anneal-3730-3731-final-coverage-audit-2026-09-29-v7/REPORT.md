# #3730/#3731 evidence audit v7: R21–R22 and remaining boundaries

## Scope and status

At the public GitHub API snapshot of **2026-09-29T11:09:11Z**, [#3730](https://github.com/google/zerocopy/issues/3730) was closed and [#3731](https://github.com/google/zerocopy/issues/3731) open. The body and single comment of each issue were byte-identical to v6: #3730 body SHA-256 `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0`, comment `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 body `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88`, scope-extension comment `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`. The builder verifies **159 distinct I001–I159 rows**, **174 distinct #3730 suggestions**, and every crosswalk destination against that snapshot.

Both R21–R22 suites proposed in v6 are complete. The snapshot contains **70 completed substantive #3730 report packages**: 68 from v6 and the two reviewed here. The builder validates every package with `reference._load_report`; it inspected and hashed all 121 files (1,585,017 bytes) in R21/R22. Their offline evidence checkers passed. The two **R23/R24** directories had only work in progress at this cutoff and are excluded from status claims and package counts. The builder freezes this package set so later completion cannot retroactively change the v7 result.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations (159) | 2 | 147 | 7 | 3 |
| #3730 suggestions (174) | 4 | 143 | 23 | 4 |

Statuses do not change in v7. R21 and R22 strengthen selected component evidence without fulfilling the full requested scope of any partial row. I046 and I049 remain the only complete investigations at their narrow pinned direct-Lean scope; C03, C04, C13 and N11 remain the only complete suggestions. `support/investigation-final-v7.csv` and `support/3730-crosswalk-final-v7.csv` list exact evidence and residuals for every row, including mapped suggestion-level residuals. A status of partial is evidence, not a finding that the proposed V2 design works.

## Two newly completed packages

| Suite and report | Observed result | Binding limit |
| --- | --- | --- |
| R21 [`anneal-3730-lake-plugin-combined-family-mix-2026-09-29`](../anneal-3730-lake-plugin-combined-family-mix-2026-09-29/REPORT.md) | A pinned Lake two-package consumer combined v1 source/OLean/ILean/proof with valid v2 plugin dylib, generated C and setup option. `setup-file` named the mixed import/plugin paths and option. Fresh `lake serve` returned no goals, value 7 and the v2 plugin initializer marker; artifact hashes were unchanged. Clean v1/v2 controls and direct batch agreed with their selected values. | One tiny same-pin macOS fixture, no actual Anneal archive; the copied v2 C was not consumed; value/hash and initializer are bounded loaded-byte oracles, not a syscall-level trace or general native ABI guarantee. |
| R22 [`anneal-3730-cli-graceful-cancel-signals-2026-09-29`](../anneal-3730-cli-graceful-cancel-signals-2026-09-29/REPORT.md) | Seven active-gate cases exercised SIGINT/SIGTERM first signals and SIGKILL controls across Charon partial JSON/Postcard, Aeneas Types/Funs and Lake/Lean blocked elaboration. Immediate process-group, `lsof`/pipe and selected advisory-lock snapshots were recorded; same-directory retries and fresh consumers passed. A synthetic SIGINT-ignoring supervisor exercised escalation. | Selected CLI phases and sampled process/lock state; no Anneal scheduler, complete output transaction, sustained orphan proof or general Aeneas SIGINT conclusion. |

`support/new-package-review-v7.csv` states the exact procedure, affected rows, evidence files and boundary for each package. `support/new-file-inventory-v7.csv` hashes every file. `support/r21-r22-disposition-v7.csv` connects the v6 plan to completed packages. R21 is mapped to I089–I104/I120/I125/I150 with explicitly bounded contributions; R22 is mapped only to I078/I080/I105/I134, because its report specifically says it did not test the remaining I073–I080 dimensions. The row ledger keeps those distinctions.

## Remaining local work and gates

R21 and R22 exhaust the v6 planned list. Two further locally executable bounded suites were **dispatched but unfinished at this cutoff**: R23 tests provisional proof work against an explicitly last-good Rust model after source/extraction/signature failures (I023), and R24 tests scratch tactic attempts, subject/proof compare-and-swap and fresh verification (I070). They are recorded in `support/remaining-local-experiments-v7.csv`; this report does not infer their outcomes. They can provide component/prototype evidence, not a human-comprehension result or a production Anneal workflow.

Seven gate groups remain in `support/gated-work-v7.csv`: same-process/in-memory Aeneas experiments need a compatible OCaml API/dependency scope; I141 requires actual consenting human participants and a frozen UI; selected remote durability needs a chosen target and threshold; other filesystem/platform coverage needs a target environment; external editor/MCP adapter comparisons need selected clients; an actual Anneal V2 Rust-hosted projection, shared workspace and integrated batch/live engine must exist for product-level rows; and final architecture selection needs a design decision. The remaining not-run I028/I061/I063/I072/I086 and broad partial rows are principally tied to those integration, client or dependency boundaries. The ledger preserves each exact delta rather than promoting simulated or component evidence to product completion.

## Rebuild and validation

Run `python3 reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v7/support/build_audit.py` from the checkout. It rechecks issue hashes and counts from the frozen public snapshot, validates the 70 snapshot packages, checks that R21/R22 were the exact v6 planned suites, and regenerates only this package's CSV/JSON outputs. It does not rerun the original toolchains or refetch GitHub. Two offline rebuilds produced byte-identical outputs. `reference._load_report` validates this package's `REPORT.md` and `REPORT.json`; the package remains unstaged and unpublished here.
