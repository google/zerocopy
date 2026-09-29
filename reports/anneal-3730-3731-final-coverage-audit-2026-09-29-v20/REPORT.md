# #3730/#3731 coverage audit v20: real-generation reader lease and GC gates

## Scope and status

This audit fetched public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) at **2026-09-29 18:05:22 UTC** and inspected `reference` at `df4f6d6c84f936489c01edfa5ff19b2ee005f4d0`, together with the completed [real-generation GC lease experiment](../anneal-3731-real-generation-gc-lease-v4-30-0-rc2/REPORT.md) in this candidate tree. The four issue body/comment hashes are unchanged from v19. The [investigation ledger](support/investigation-final-v20.csv), [suggestion crosswalk](support/3730-crosswalk-final-v20.csv), and [333-item challenge](support/row-challenge-v20.json) retain every I001–I159 investigation and all 174 #3730 suggestions, with exact v20 residuals, linked evidence and next prerequisites.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 4 | 161 | 5 | 4 |

**I121 and J11 remain partial.** The new package establishes a cooperative lease/GC component result with real generated artifacts. Their remaining claims concern Anneal-owned leases and reclamation across product readers and lifetimes. I051/A03/E04 retain the product-level publication gaps from v19. This is not 100% issue coverage.

## New evidence and exact limits

The GC package retains the same seven-file A/B Charon LLBC, Aeneas Lean source, and compiled Lean artifact families used in the real-artifact publication experiment. It selected A, opened an A proof in a Lean server, and gated a separate reader **before that reader started Lean**. After selecting B, it attempted GC, released the gate, and checked fresh imports through the pinned A path. In the leased case a parent-held shared advisory lock caused GC to defer; the later A old proof passed and B proof failed. After reader/server exit and lease release, GC removed A and a new A import failed. In the unleased control GC removed A before the gated reader started, and both later A imports failed. B remained available throughout. The previously open A document still returned `no goals` even after A removal in the unleased case, showing that this cached response alone cannot establish later file availability or currentness. The [24-file inventory](support/new-file-inventory-v20.csv) and [package review](support/new-package-review-v20.csv) retain exact hashes; the package's offline checker passed.

This narrows **I121** to a real generated-family, later-open GC schedule and **J11** to the matching generation collection suggestion. The shared lease was held by the parent as a cooperative reader-cohort proxy; the gated reader did not acquire its own lease. The result does not establish Anneal's production lease ownership or GC implementation, independent worker handoff, pending-query and scratch-fork retention, replay identity, crash/restart reconciliation, power-loss durability, or cross-platform locks. The [row challenge](support/row-challenge-v20.json) records those residuals without promoting either status.

## Remaining inputs and follow-up challenge

The [gate table](support/unrun-conditional-inputs-v20.csv) preserves exact blockers/inputs for all 13 not-run or conditional rows. A [read-only resource recheck](support/resource-recheck.json) found the 14 cached source/binary pins unchanged from v19, no `ocaml`/`dune`/`opam` on `PATH`, and 8 GiB host RAM. No dependency was installed or downloaded. The real generated-model, publication, and GC lease fixtures do not add an Anneal owner, real editor/MCP clients, OCaml same-process producer, later compatible Lake release, independent host, or consenting human evaluation. The new fixture fills the previously missing distinct cached-only later-open GC cell; repeating the same advisory lock schedule would not answer the remaining product reader policy. No further distinct cached-only experiment was identified that would materially close another row at this snapshot. Future product implementation or external resources can change that assessment.

## Validation

Run `python3 support/check.py` from this package. It twice rebuilds the LF ledgers with identical hashes; verifies all 333 decisions, four live issue text hashes, 159/174 unique IDs, unchanged status counts, 13 gate inputs, the new package's reference metadata and offline checker. `support/validation-v20.json` pins the reference commit, issue hashes, package files and generated hashes. The builder is offline and does not stage, commit, push, install dependencies, or access `.local/`.
