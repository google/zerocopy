# Coverage audit and experiment plan for Anneal issues #3730 and #3731

## Summary

Issue #3731 consolidates #3730 into 159 investigation IDs and its follow-up comment preserves the 174-item #3730-to-#3731 crosswalk, 15 new investigations, and 64 explicit extensions to earlier IDs. The investigation ledger, extension ledger, and crosswalk are included in `support/`.

This pass added four experiment report packages: a bounded identity/projection/publication suite, direct Lean-server dependency-generation probes across Lean 4.29 and 4.30-rc2, and a concurrent Aeneas generation probe. They provide new bounded evidence for subsets of 21 agenda IDs; 20 other links are retained as context only because the cited probes do not execute a requested cell. None of the 159 investigations is declared complete by this audit. Existing reports remain evidence for their identified subjects, while their boundaries still apply. The ledger retains all I001–I159 scopes and report pointers. Its remaining-delta field is mostly a conservative prompt to compare each item's exact scope with the linked reports, not a separate item-by-item gap analysis.

The work is not a claim that all experiments in either issue have been executed. Human/agent evaluations, independent reproduction, broad concurrency/resource sweeps, other operating systems/filesystems, real MCP/editor vertical slices, and selected cross-version matrices remain open or conditional.

## Applicability

The agenda scope is read from public GitHub issues #3730 and #3731, including #3731 extension comment `5884299718` and the #3730 closure comment `5884380373`. The latter confirms #3730 was closed as a duplicate backlog, not as completed research; #3731 remains open. `REPORT.json` retains the original review's source hashes. The public #3731 body and extension comment were edited afterward; `support/source-snapshot/` preserves their later text and hashes for this independent check. All 159 base rows, 64 extension rows, and 174 crosswalk rows match that retained later snapshot exactly. The corpus snapshot was `google/zerocopy@8c257ec3f4e067963e12441ce5b261714a005c74`, the fetched `reference` tip at the time of review.

At review, #3730 was closed as a duplicate backlog and #3731 remained open. The #3730 closure comment explicitly says consolidation does not complete research. The issue bodies describe proposed investigations, not adopted implementation requirements. This audit uses “prior evidence” as a navigation pointer to relevant existing packages, not as a finding that each package satisfies every method or scope extension. `support/investigation-matrix.csv` preserves each base item's method and scope, prior report pointers, new bounded evidence, and context-only links. The latter preserve topical navigation without claiming that a cited probe executes a requested cell; narrowing the evidence map does not remove an agenda item. The remaining-delta field gives an item-specific explanation for I151, a common conditional explanation for six rows, and the same broad unresolved-scope statement for the other 152 rows. Read each base row with its linked report boundaries and the 64 additional clauses in `support/scope-extensions.csv` before deciding which cells remain. `support/3730-to-3731-crosswalk.csv` preserves all 174 original suggestions and their consolidated destinations.

Disposition terms in the ledger are deliberately conservative:

- **New bounded execution added; item remains partial** means a new experiment touches one or more conditions in that agenda item but does not meet its full stated matrix.
- **Context-only new package linked; requested cell remains** preserves a topical analogue without counting it as execution of that item's requested conditions.
- **Prior corpus evidence is relevant; requested delta remains** means existing reports are useful starting points, but the agenda's particular breadth, controls, comparisons, or measurements are not established by this audit.
- **Conditional/human/other-platform dimension remains** marks work that needs a selected target, different operator, or human/agent evaluation.

These are planning dispositions, not issue checkboxes or claims about the Anneal product.

## Findings

### Additional experiments were grouped around shared causal fixtures

The brainstorm grouped the backlog into nine suites to avoid one report per suggestion while preserving distinct evidence boundaries:

1. Identity and freshness: ablate subject, source, backend/configuration, model, import, projection, document, worker, and RPC identities; preserve A→B→A and separate cache reuse keys from response provenance.
2. Projection and source ownership: exercise Unicode/UTF-16 coordinates, authored versus synthetic spans, stale patch rejection, formatter/macro cases, and separate diagnostic responsibility from edit authority.
3. Lean query lifecycle: compare old/open, new, reopened, and batch consumers after imported artifact changes; add readiness, request ordering, crash, and launch-mode cases.
4. Generation publication and orchestration: stage, supersede, cancel, crash, publish, retain, and collect generations under causally controlled schedules.
5. Prepared Lake environment and caches: extend existing archive/cache reports with per-operation identity, incomplete artifact families, producer removal, offline/home isolation, and final-path preparation.
6. MCP/LSP shared-workspace contract: test handles, CAS edits, retries, cancellation, subscriptions, client ownership, shadow documents, and capability fallback; keep protocol behavior distinct from user studies.
7. Rust/Charon/Aeneas boundaries: test complete Cargo subject inputs, overlays, proof-only classification, backend lifetimes, determinism, and a generated-output/declaration manifest.
8. Resource and parallel-test economics: guarded worker and consumer sweeps, byte/inode/temporary-space attribution, physical memory, nested parallelism, soak behavior, retention, and filesystem effects.
9. Acceptance, trust, and upgrades: separate goal state from full verification and Rust-level claim coverage; validate fresh oracles, assumptions/TCB, comparator sensitivity, negative controls, and upgrade-specific regression suites.

The complete item-level wording and report pointers are in the matrix. A shared harness may support several rows, but one passing row of a matrix does not imply the other combinations were tested.

### The new model suite adds bounded counterexamples

`anneal-interactive-model-probes-2026-09-29` executes ten identity mutations against six illustrative keys, checks 2,092 UTF-8/UTF-16 coordinate boundaries across 59 strings, explores all 120 permutations of a two-generation five-event schedule, and performs a controlled APFS symlink-pointer swap. It found counterexamples to path-only/URI-version-only freshness, showed a valid-segment edit versus synthetic-gap/stale-CAS rejection in the fixture, and demonstrated why readers must pin an immutable generation directory. These results apply to the model and filesystem experiment only.

It adds bounded evidence for I005/I011/I025–I026/I029/I045/I051/I053/I097/I106/I133/I145/I159. Its more remote analogies are retained in the ledger's context-only column. The agenda still calls for implementation-level schedules, real project projections, Lake publication/cache behavior, crash tests, and larger state spaces.

### A direct Lean server added one launch-mode comparison

`lean-same-server-dependency-generation-v4-30-0-rc2` uses the pinned Lean 4.30.0-rc2 binary directly with `lean --server`. It rebuilt an imported `.olean` while leaving a proof document open. That worker continued to report “no goals”; opening an identical second document in the same server process reported a remaining goal and a failing diagnostic. Closing/reopening the first URI also reported the goal, and fresh batch Lean exited 1. Thus workers in one process can answer against distinct imported generations in this fixture, and per-file worker replacement was sufficient here to pick up the new artifact.

This extends the prior generated V1 `lake env lean --server` stale-import report with a direct-server case. It adds bounded evidence for I041/I042/I046/I049/I131. It is context only for I043/I050/I098/I099/I147, whose requested conditions were not exercised. It does not compare `lake serve`, `lake env lean --server`, direct prepared Lean, or Lake `setup-file`; the source and artifact changed together; only two document workers were exercised; and no real Anneal generated project, concurrent query race, or full batch/live matrix was run.


### The stale-worker contrast repeated under Lean 4.29.0

`lean-import-refresh-cross-version-v4-29-to-v4-30-rc2` reran the same direct-server fixture with Lean 4.29.0. It observed the same old-worker “no goals” response after the imported artifact rebuild, while a new or reopened worker and fresh batch Lean exposed the remaining goal/failure. This extends the observation across two pinned Lean versions, but does not substitute for the launch-mode matrix or a 4.31 candidate upgrade suite.

Basis: **execution** in the v4.29 transcript and the paired v4.30 report.

### Coverage remains partial across the agenda

The ledger has 159 base rows, 64 extension rows, and 174 crosswalk rows. Twenty-one IDs point to bounded new evidence, and 20 additional IDs retain a new package as context only; all remain partial or open. The other rows point to relevant existing packages by research area or remain conditional. No item is declared complete because the issue items often require independent matrices, failure injection, exact toolchain tuples, or evaluation beyond the evidence acquired here. The I151 pointer to a same-input Aeneas generated-source destination was removed during review: it does not exercise the shared writable Lake build-tree behavior requested there. Its APFS generation-pointer analogue remains labeled as context only, with the Lake writer cells open.

A useful next execution tranche is to use the installed pinned project tools for: (1) a real generated-workspace import-refresh matrix across `lake serve`, `lake env lean --server`, and direct prepared Lean; (2) a reproducible projection/parser fixture with real annotation syntax and version-checked edit application; (3) a two-consumer Lake prepared archive and interrupted publication control; and (4) an Aeneas/Charon generation manifest and same-process/concurrent-call probe. Before scaling past small consumer counts, measure live host memory and process usage. Human/agent evaluation and independent reproduction need separate operators and must not be inferred from local automation.

## Boundaries

- The ledger was built from the two issue bodies/comment and relevant package navigation pointers. It is not a re-review of every technical claim in every referenced package.
- “159 investigations” does not mean 159 report packages. The 174-row crosswalk is a mapping of suggestions, not completion evidence.
- A linked prior package may contain strong execution evidence for a narrow pin while leaving the broader requested dimensions open; the ledger does not promote it to complete.
- The new state model is finite and illustrative; the APFS pointer experiment is not a Lake cache or crash-durability test. The Aeneas concurrency probe used identical input and did not inject process failure or compile the generated files. The Lean comparison is limited to two pins and direct server launch.
- The direct Lean experiment applies to `v4.30.0-rc2` on arm64 macOS and the minimal fixture. It does not establish general stale-import behavior beyond the observed state.
- No claim is made that #3730 or #3731 is complete, that Anneal has adopted any proposed design, or that an implementation is safe/unsafe as a whole.

## Evidence

- `support/investigation-matrix.csv` — all I001–I159 entries, exact base titles/methods/scope text, relevant existing report pointers, new bounded evidence, context-only links, disposition, and a mostly generic remaining-delta field.
- `support/scope-extensions.csv` — all 64 extra clauses merged into I001–I144 by the #3731 consolidation comment.
- `support/3730-to-3731-crosswalk.csv` — every original #3730 suggestion and its consolidated #3731 destination (174 rows).
- `support/source-snapshot/` — retained public issue/comment text and SHA-256 manifest from the independent re-review; `support/check.py` verifies source-derived rows, counts, file hashes, and report-pointer existence offline. The evidence mappings themselves remain editorial judgments, not deterministic output of the source parser.
- `anneal-interactive-model-probes-2026-09-29/REPORT.md` and its support artifacts — finite identity, coordinate, schedule, and APFS experiments.
- `lean-same-server-dependency-generation-v4-30-0-rc2/REPORT.md` and its support artifacts — direct Lean server/batch comparison.
- `aeneas-concurrent-generation-determinism-nightly-2026-06-03/REPORT.md` and its support artifacts — split-output concurrency and shared-generator-destination probe.
- `lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/REPORT.md` and its support artifacts — v4.29/v4.30-rc2 direct-server comparison.
- Existing relevant report packages are named per row in the ledger. They are contextual corpus evidence, not re-executed by this audit.

The original issue body/comment hashes and corpus tip are preserved in `REPORT.json`; the later re-review hashes are in `support/source-snapshot/manifest.json`. The original source bytes were not retained in this package, so the earlier hashes cannot be reconstructed from its files. Evidence roles for this report are **source** for agenda wording, **execution** for the linked new packages, and **derived** for grouping and remaining-delta judgments.

## Revalidation

Run `python3 support/check.py` from this package directory to check the retained source-derived rows, 64 extensions, crosswalk, hashes, and pointer existence. Then fetch the current `reference` tip and reread #3730, #3731, and comment `5884299718`. Confirm that the 159 IDs, 64 extension clauses, and 174 crosswalk rows remain current; compare new reports against every base and extension row; update the relevant evidence pointer and remaining delta without converting topical overlap into completion. Re-run each report's included harness at its identified subject. Add cross-platform, human, or independent evidence only when the corresponding target/operator is explicitly selected.
