# #3730/#3731 coverage audit v19: real-artifact publication gates

## Scope and status

This audit fetched public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) at **2026-09-29 17:54:26 UTC** and inspected `reference` at `5f4c846fa5dddc19b649305d86d612bf142ce606`, plus the completed [real-artifact publication experiment](../anneal-3731-real-generation-publication-v4-30-0-rc2/REPORT.md). The four issue body/comment hashes are unchanged from v18. The [investigation ledger](support/investigation-final-v19.csv), [suggestion crosswalk](support/3730-crosswalk-final-v19.csv), and [333-item challenge](support/row-challenge-v19.json) retain every I001–I159 investigation and all 174 #3730 suggestions, with exact v19 residuals, linked evidence and next prerequisites.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 4 | 161 | 5 | 4 |

**I051, A03 and E04 remain partial.** The new report closes a disposable component experiment with real generated artifacts; their remaining requested claims concern an actual Anneal publisher, readers, cache/setup/native families, and broader races. I137/I138 retain the narrow disposable-prototype completion established in v18. This is not 100% issue coverage.

## New evidence and exact limits

The publication package retains seven-file A/B families: one real Charon LLBC, three Aeneas Lean sources, and three compiled Lean `.olean` files per generation. It checked exact manifests and fresh old/new proof outcomes. A fixture-owned writer copied B privately and paused after each file; a reader saw complete A at every preparation gate and complete B after the selected symlink changed. A Lean server pinned to A still returned its A goal after B selected, correctly labeled noncurrent. `SIGKILL` before the pointer change left A selected; `SIGKILL` afterward left B selected. These are process-kill readbacks on one macOS filesystem, not power-loss durability.

The in-place control wrote the same B files directly over A. Four intermediate inventories were mixed and had no generation ID. Fresh Lean accepted the old proof under each mixed family because the old compiled function artifact remained, even after LLBC and source had changed. The new proof first passed when the B compiled function artifact completed the B family. `Current.olean` stayed byte-identical while `Current/Funs.olean` changed. The [23-file inventory](support/new-file-inventory-v19.csv) and [package review](support/new-package-review-v19.csv) record exact retained hashes; the package's offline checker passed.

This narrows **I051** through a real family and per-write gates but does not establish Anneal's generation ownership, coordination with Lake setup/cache/native products, parallel publisher ordering, output shrink, garbage collection, or filesystem durability. **A03** gains a concrete mixed-family proof-label hazard and staged control but still needs the full product race matrix. **E04** gains an exact staged-versus-in-place comparison but still needs actual transactional generated-tree replacement. Other linked rows about retained readers, fresh oracles, manifests and source/artifact mismatch have specific residuals in the ledger; their status is unchanged.

## Remaining inputs and follow-up challenge

The [gate table](support/unrun-conditional-inputs-v19.csv) preserves exact blockers/inputs for all 13 not-run or conditional rows. A [read-only resource recheck](support/resource-recheck.json) found the 14 cached source/binary pins unchanged, no `ocaml`/`dune`/`opam` on `PATH`, and 8 GiB host RAM. No dependency was installed or downloaded. The two newest prototype packages provide real generated-model and publication component fixtures, but they do not add an Anneal owner, real editor/MCP clients, OCaml same-process producer, later compatible Lake release, independent host, or consenting human evaluation. Repeating a two-open symlink mix with the new A/B bytes would recapitulate the earlier synthetic pointer-swap mechanism and this package's real in-place mixed-proof hazard; it would not answer the remaining product reader policy. No newly available *distinct cached-only* experiment was identified that would materially close another row at this snapshot. Future product implementation or external resources can change that assessment.

## Validation

Run `python3 support/check.py` from this package. It twice rebuilds the LF ledgers with identical hashes; verifies all 333 decisions, four live issue text hashes, 159/174 unique IDs, unchanged status counts, 13 gate inputs, the new package's reference metadata and offline checker. `support/validation-v19.json` pins the reference commit, issue hashes, package files and generated hashes. The builder is offline and does not stage, commit, push, install dependencies, or access `.local/`.
