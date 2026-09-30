# #3730/#3731 coverage audit v33: source/artifact and compilation-subject contrasts

## Summary

Two finalized reports add direct bounded evidence to **five partial rows** of published [v31](../anneal-3730-3731-final-coverage-audit-2026-09-29-v31/REPORT.md): [syntax-equivalent Lean rebuild](../anneal-3731-i147-syntax-equivalent-rebuild-2026-09-29/REPORT.md) maps to **I147/C06**, and [V2 profile/cfg slug collision](../anneal-v2-profile-cfg-subject-slug-collision-2026-09-29/REPORT.md) maps to **I020/I076/D07**. This audit derives directly from v31, not unpublished v32. The only context-only clarification is D03's inherited cancellation wording. All 333 row IDs, 345 suggestion destinations, inherited request fields, statuses, gate categories and prerequisites remain unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

The [investigation matrix](support/investigation-final-v33.csv), [suggestion crosswalk](support/3730-crosswalk-final-v33.csv) and [333-row challenge](support/row-challenge-v33.json) append a v33 scope assessment to every item. Only the five directly mapped residuals change.

## Applicability

The baseline is published `reference@e26a9414ab48844eeb95b91ee8b743046c8a8982`. The Lean component used pinned `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) in one local Lake project and direct Lean server. The compilation-subject component copied the exact checked-in `scanner.rs` at `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988` into a minimal harness and invoked pinned Charon separately under debug, release and debug `--cfg probe_alt`. Neither component ran the Anneal V2 CLI, an integrated proof-context selector, or actual publication.

Public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and comments were fetched again at `2026-09-30T01:02:48.649073+00:00` and retained verbatim in the [v33 snapshot](support/live-issue-snapshot-v33.json). #3730 was closed and #3731 open, each with one comment. Body and comment bytes match v31. #3730 body/comment SHA-256 values are `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values are `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Source | Rows | Measured component and limit |
| --- | --- | --- |
| Syntax-equivalent Lean rebuild | I147, C06 | An equal-length noncomment source edit rebuilt `Dep` with changed source, ILean and trace bytes and a changed OLean mtime, yet the baseline and rebuilt 4,616-byte OLeans were byte identical. Resident, new, reopened and fresh-server goal controls plus batch agreed on value 7. A longer parenthesized edit kept the same goal/value but changed OLean bytes; it is a **negative byte-identity control**, not another successful C06 cell. Anneal producer identity and freshness policy remain open. |
| V2 profile/cfg slug collision | I020, I076, D07 | One unchanged Rust source/manifest and copied checked-in slug helper yielded the same LLBC filename under debug, release and debug `RUSTFLAGS=--cfg probe_alt`. Separate pinned Charon runs emitted error-free LLBC with `profile_value` 7/11 and `config_value` 23/29 across the respective contrasts. Distinct private targets and destinations prevent any claim of actual overwrite. The V2 CLI did not call this helper or Charon; complete compilation-unit identity, proof-context selection, invalidation and collision-safe publication remain open. |

For the slug report, 25 parsed-JSON leaves changed between debug and release and 19 between debug and cfg. Those differences include the selected literals, source spans, short-name order and requested output path. The evidence supports selected body/literal contrasts and equal helper filename; it does **not** claim that entire LLBCs differ only in one scalar. Profile and custom cfg extend the earlier feature-only locator collision. **Basis: execution plus copied-source derivation** in the source package.

### D03 context and unchanged rows

D03's inherited v31 residual says “no job was canceled” for its **sequential source-edit/revert matrix**. The separately published [I080/D06 warmed incremental-on shared-target probe](../anneal-3731-i080-incremental-on-shared-target-cancel-recovery-2026-09-29/REPORT.md) did cancel edited A while B waited, completed and was checked against selected cold-oracle bodies; a same-target A retry also succeeded. That distinct small probe does not attest the producing Cargo unit, full output identity or representative Anneal target ownership. Neither new v33 report directly tests D03. Its v31 residual, product/resource gate, prerequisite and partial status are preserved, with this clarification in the v33 assessment only.

The other **327 rows** state that neither new report directly exercises their remaining request and preserve their v31 residual and prerequisite verbatim. Thus five direct + one context-only + 327 other unchanged = 333. No bounded component promotes a row to complete.

## Boundaries

- The byte-identical OLean result is one syntax-level source change. Its ILean and trace changed; OLean equality alone does not establish equal provenance, complete imports, options or native setup.
- The profile/cfg report uses the copied helper and explicit Charon requests. It does not observe an Anneal overwrite, cache invalidation, proof mismatch or concurrent producer. The equal slug is identical helper input, not a 64-bit hash collision between different inputs.
- D03's clarification reconciles the scope of two already published experiments. It is not new D03 execution evidence and does not change the D06 assessment.
- The issue snapshot preserves public request scope at fetch time. No issue or product state was changed.

## Evidence

- [source-package-inventory-v33.csv](support/source-package-inventory-v33.csv) hashes every retained file in published v31 and both source packages. [validation-v33.json](support/validation-v33.json) records input/generated hashes, counts and exact direct/context IDs.
- The [builder](support/build_audit.py) derives all v33 rows directly from v31 and checks 159 investigation titles, 174 suggestion destinations and 345 links against refreshed public text. The [checker](support/check.py) checks every inherited field, unchanged residual and status, source inventory, issue hashes and all three source package checkers, and calls `reference._load_report` on v31, both sources and v33.
- Both new source checkers and `reference._load_report` passed in place and from relocated copies during validation. The source reports preserve exact commands, inputs, outputs, identity hashes, negative controls and resource guards.
- Published v31's row-challenge SHA-256 is `9c1b9741f9d5f4a92fa899ed2ad79d6a9f23177963ec4412e0f5df9b5189603d`.

## Revalidation

Run `python3 -B support/check.py` from this package. It checks retained evidence without starting Lean, Lake, Cargo, Charon, Aeneas or Anneal. Reacquiring either source experiment is a separate observation subject to its pinned tools and resource guards.
