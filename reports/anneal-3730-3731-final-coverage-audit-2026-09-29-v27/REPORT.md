# #3730/#3731 coverage audit v27: coordinates, provenance, rich goals and Lake writers

## Summary

Four new component reports sharpen nine partial rows in the published [v26 coverage ledger](../anneal-3730-3731-final-coverage-audit-2026-09-29-v26/REPORT.md): **I025, I043, I079, I148, I151, C02, E06, E07 and F12**. A tenth row, **I046**, receives corroborating rich-goal evidence but keeps its already complete, explicitly narrow status, residual and prerequisite. All 333 IDs, 345 #3730→#3731 destination links, original request text, gate categories and statuses remain unchanged. The two [v27 CSV matrices](support/investigation-final-v27.csv) ([suggestions](support/3730-crosswalk-final-v27.csv)) and [333-row challenge](support/row-challenge-v27.json) retain every v26 field and append per-row evidence, remaining delta and scope assessment.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

The four reports each exercise a different boundary. The [compiler-backed coordinate bridge](../anneal-3731-compiler-backed-coordinate-bridge-2026-09-29/REPORT.md) maps real rustc and Lean diagnostics over one exact copied doc-comment interval. The [Charon/Aeneas relocation and comment probe](../anneal-3731-charon-relocation-comment-provenance-2026-09-29/REPORT.md) separates generated model text from source provenance in one safe function. The [rich-goal recovery probe](../anneal-3731-rich-goal-unsaved-recovery-v4-30-0-rc2/REPORT.md) compares two direct Lean query methods across one unsaved error/recovery stream. The [matched Lake writer probe](../anneal-3731-i151-matched-lake-writer-isolation-2026-09-29/REPORT.md) isolates one shared-tree source-ownership hazard. None runs an Anneal V2 verification service.

## Applicability

The baseline is published `reference@087760fd8bccaa8852390f189d8daf01f0958b19` and its v26 audit. The coordinate bridge uses pinned rustc and Lean, the Charon/Aeneas report uses the binaries and source release pair it identifies, and the other direct Lean/Lake reports use Lean 4.30.0-rc2 on macOS arm64. Their exact command, fixture, host and negative-control bounds are in the linked source reports and [v27 source inventory](support/source-package-inventory-v27.csv). An observed component result is not an adopted product contract.

Public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) were refetched on 2026-09-29. The full bodies, single comments, IDs, states and timestamps are retained in [`support/live-issue-snapshot-v27.json`](support/live-issue-snapshot-v27.json), fetched at `2026-09-29T22:10:04Z`. #3730 remains closed, #3731 open. Their body/comment SHA-256 values match v26 and the frozen v22 text exactly: #3730 body `81bdc705...`, comment `7544fde7...`; #3731 body `0375e6dc...`, comment `4cc53278...`. The builder and checker compare complete strings and verify all 159 investigation titles, 174 suggestion titles and 345 destination links against that snapshot.

## Findings

### Nine partial-row deltas and one corroboration

| Rows | Direct new evidence | Remaining boundary |
| --- | --- | --- |
| **I025** | An exact 31-byte doc-comment payload bridge paired a real rustc JSON span with Lean batch/LSP spans under CRLF and supplementary Unicode. It round-tripped 28 valid scalar boundaries across byte/scalar/UTF-16 coordinates and rejected seven invalid or unowned cases. | The bridge is hand-authored, not Anneal's source map; production grammar, empty lines/display-width cases, unsaved edits and negotiated editor encoding remain. |
| **I079** | Relocating identical Rust bytes changed the LLBC local source path and Aeneas's generated source-path comment; appending an inert comment after the function changed embedded LLBC source bytes but left generated Lean byte-identical at one path. A restored A run matched after the narrow keyed-map/output-path normalization. | This does not authorize general LLBC normalization or drop current source provenance. Multi-file/path-sensitive builds, diagnostic association and an Anneal cache key remain. |
| **I148, E06, E07** | The same error-free one-function Charon/Aeneas sequence adds successful generated-Lean byte comparisons to v26's error-bearing real-library Charon repeat. The inert comment changed LLBC source bytes without changing generated Lean; relocation changed only a generated source comment line. | No concurrent or representative split-file workload, Lake/Lean reuse cost, theorem/obligation semantic-equivalence oracle, or broad path/flag/revision matrix ran. The earlier real-library LLBC remains `has_errors: true`. |
| **I043, C02** | `plainGoal` and `Lean.Widget.getInteractiveGoals` agreed at 24 paired positions through valid, unsaved syntax-error, unknown-tactic and restored nested proofs: 17 goals, two empty lists and five null results. Every nonempty rich rendered target matched the plain target after presentation tags were removed. Both error versions failed fresh batch. | Rich reference dereference/expiration, generated/projected proofs, exact-version fencing, macro positions and an Anneal adapter remain. |
| **I046** | The same rich/plain cells corroborate useful local goal state before and after failed elaboration, including a reachable later theorem while the whole erroneous file fails batch. | I046 was already complete at its narrow direct-Lean scope in v26. Its status, residual and prerequisite are unchanged; this is additional evidence only. |
| **I151, F12** | Four matched two-writer cells compare shared and isolated Lake build trees under reverse kills. When the newer writer died, the old survivor exited 0 and made the same 7 OLean in both topologies. No-build rejected that artifact against the changed shared source but accepted it against the unchanged isolated source. Fresh Lean controls confirmed the definitions. | Kills occurred before artifact output. OLean/trace/hash syscall interruption, partial-file repair, an Anneal lock graph and a general shared-writer ownership policy remain. No silent Lake freshness failure was observed. |

The coordinate result is context for B02/B03/K01, but does not exercise Anneal's annotation grammar, a negotiated editor client or an authenticated producer sidecar. The relocation result bears on source identity in I009/I074 and the locator/hash questions A02/A08 only as bounded context; it does not execute those remaining contracts. The rich-goal report does not dereference retained objects, so I044 remains unchanged. The Lake report's gate-period RSS guard and small artifact specimens are not I080/I113/J01/J02 resource economics, and its pre-artifact kill does not complete I108's lock graph. D05 remains unchanged because the Charon/Aeneas sequence was serial. D06 and D07 also receive no direct new evidence. These 16 context-only rows have specific explanations in their `v27_scope_assessment` fields.

For each of the other **307** rows with no new direct evidence, the appended assessment names its ID, title and v26 gate and states that none of the four reports exercises that residual. Together with the 16 context-only explanations, this accounts for every row whose residual and prerequisite are unchanged. The direct I046 corroboration is separately labeled, rather than counted as a new completion.

## Boundaries

- The source relocation/comment fixture is one sequential safe function. Its field-aware normalization sorts only known keyed name arrays and keeps raw LLBC; the result does not make arbitrary path or comment changes semantically harmless.
- The coordinate bridge links compiler observations through a deliberately copied byte interval. It does not establish Rust/Lean proof correspondence, edit ownership or a production Anneal projection map.
- Rich goal agreement is limited to availability, goal count and rendered target in 24 direct-Lean cells. An available goal while fresh batch rejects the file is partial elaboration feedback, not verification success.
- The Lake writers stopped at source-level gates before artifact writes. The two isolated roots are a matched control for this fixture, not proof of general crash safety or an implemented Anneal ownership protocol.
- I046's inherited complete status refers only to the original narrow issue scope. No finite component probe here completes an integrated V2 workflow.

## Evidence

[`support/validation-v27.json`](support/validation-v27.json) pins the v26 matrices/challenge, frozen issue source, live read, four derived files, status counts and changed IDs. [`support/source-package-inventory-v27.csv`](support/source-package-inventory-v27.csv) hashes every non-bytecode file in v26 and the four new packages. Each affected row cites exact source report, result, checker and selected specimen paths. The package's [offline builder](support/build_audit.py) preserves v26 rows and adds only v27 fields. The [self-checker](support/check.py) verifies all 333 inherited row dictionaries and both 159/174 CSVs field by field, live issue text and crosswalk topology, unchanged-row explanations, all inventory hashes, and executes the v26 checker and each of the four new report checkers.

## Revalidation

Run `python3 -B support/check.py` from this package. It is read-only and offline. To regenerate the derived ledger and inventory from unchanged source packages, run `python3 -B support/build_audit.py`; that builder writes only its own support files. A changed source package requires a deliberate new hash/read and a fresh checker run before treating this v27 package as the same candidate. This package does not edit v26, CATALOG, issue state, or prior reports.
