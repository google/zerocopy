# Coverage audit and experiment plan for Anneal issues #3730 and #3731

## Summary

Issue #3731 consolidates #3730 into 159 investigation IDs and its follow-up comment preserves the 174-item #3730-to-#3731 crosswalk plus 15 scope extensions. The full investigation ledger and crosswalk are included in `support/`.

This pass added two report packages: a bounded executable identity/projection/publication suite and a direct Lean-server dependency-generation probe. They provide new evidence for subsets of 38 agenda IDs; none of the 159 investigations is declared complete by this audit. Existing reports remain evidence for their identified subjects, while their boundaries still apply. The ledger records prior report pointers, new evidence links, and the remaining delta for every I001–I159 item.

The work is not a claim that all experiments in either issue have been executed. Human/agent evaluations, independent reproduction, broad concurrency/resource sweeps, other operating systems/filesystems, real MCP/editor vertical slices, and selected cross-version matrices remain open or conditional.

## Applicability

The agenda scope is read from public GitHub issues #3730 and #3731, including #3731 extension comment `5884299718` and the #3730 closure comment `5884380373`. The latter confirms #3730 was closed as a duplicate backlog, not as completed research; #3731 remains open. Their SHA-256 values are in `REPORT.json`. The corpus snapshot was `google/zerocopy@8c257ec3f4e067963e12441ce5b261714a005c74`, the fetched `reference` tip at the time of review.

At review, #3730 was closed as a duplicate backlog and #3731 remained open. The #3730 closure comment explicitly says consolidation does not complete research. The issue bodies describe proposed investigations, not adopted implementation requirements. This audit uses “prior evidence” as a navigation pointer to relevant existing packages, not as a finding that each package satisfies every method or scope extension. `support/investigation-matrix.csv` preserves each agenda item's requested method and scope, the report pointers, supplemental evidence added in this pass, and what remains. `support/3730-to-3731-crosswalk.csv` preserves all 174 original suggestions and their consolidated destinations.

Disposition terms in the ledger are deliberately conservative:

- **New bounded execution added; item remains partial** means a new experiment touches one or more conditions in that agenda item but does not meet its full stated matrix.
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

It partially informs I011/I025–I032/I045/I051–I053/I097/I105–I109/I112/I133–I135/I145/I151/I159. The agenda still calls for implementation-level schedules, real project projections, Lake publication/cache behavior, crash tests, and larger state spaces.

### A direct Lean server added one launch-mode comparison

`lean-same-server-dependency-generation-v4-30-0-rc2` uses the pinned Lean 4.30.0-rc2 binary directly with `lean --server`. It rebuilt an imported `.olean` while leaving a proof document open. That worker continued to report “no goals”; opening an identical second document in the same server process reported a remaining goal and a failing diagnostic. Closing/reopening the first URI also reported the goal, and fresh batch Lean exited 1. Thus workers in one process can answer against distinct imported generations in this fixture, and per-file worker replacement was sufficient here to pick up the new artifact.

This extends the prior generated V1 `lake env lean --server` stale-import report with a direct-server case. It partially informs I041–I050/I098–I099/I131/I147. It does not compare `lake serve`, direct prepared Lean, or Lake `setup-file`; the source and artifact changed together; only two document workers were exercised; and no real Anneal generated project, concurrent query race, or full batch/live matrix was run.

### Coverage remains partial across the agenda

The ledger has 159 rows and 174 crosswalk rows. Thirty-eight IDs point to one of this pass's bounded experiments; those are still partial. The rest point to relevant existing packages by research area or remain conditional. No item is declared complete because the issue items often require independent matrices, failure injection, exact toolchain tuples, or evaluation beyond the evidence acquired here.

A useful next execution tranche is to use the installed pinned project tools for: (1) a real generated-workspace import-refresh matrix across `lake serve`, `lake env lean --server`, and direct prepared Lean; (2) a reproducible projection/parser fixture with real annotation syntax and version-checked edit application; (3) a two-consumer Lake prepared archive and interrupted publication control; and (4) an Aeneas/Charon generation manifest and same-process/concurrent-call probe. Before scaling past small consumer counts, measure live host memory and process usage. Human/agent evaluation and independent reproduction need separate operators and must not be inferred from local automation.

## Boundaries

- The ledger was built from the two issue bodies/comment and relevant package navigation pointers. It is not a re-review of every technical claim in every referenced package.
- “159 investigations” does not mean 159 report packages. The 174-row crosswalk is a mapping of suggestions, not completion evidence.
- A linked prior package may contain strong execution evidence for a narrow pin while leaving the broader requested dimensions open; the ledger does not promote it to complete.
- The new state model is finite and illustrative; the APFS pointer experiment is not a Lake cache or crash-durability test.
- The direct Lean experiment applies to `v4.30.0-rc2` on arm64 macOS and the minimal fixture. It does not establish general stale-import behavior beyond the observed state.
- No claim is made that #3730 or #3731 is complete, that Anneal has adopted any proposed design, or that an implementation is safe/unsafe as a whole.

## Evidence

- `support/investigation-matrix.csv` — all I001–I159 entries, exact titles/methods/scope text, relevant existing report pointers, new experiment links, disposition, and remaining delta.
- `support/3730-to-3731-crosswalk.csv` — every original #3730 suggestion and its consolidated #3731 destination (174 rows).
- `anneal-interactive-model-probes-2026-09-29/REPORT.md` and its support artifacts — finite identity, coordinate, schedule, and APFS experiments.
- `lean-same-server-dependency-generation-v4-30-0-rc2/REPORT.md` and its support artifacts — direct Lean server/batch comparison.
- Existing relevant report packages are named per row in the ledger. They are contextual corpus evidence, not re-executed by this audit.

The issue body/comment hashes and corpus tip are preserved in `REPORT.json`. Evidence roles for this report are **source** for agenda wording, **execution** for the two new packages, and **derived** for grouping and remaining-delta judgments.

## Revalidation

Fetch the current `reference` tip and reread #3730, #3731, and comment `5884299718`. Confirm that the 159 IDs and 174 crosswalk rows remain current; compare new reports against every ledger row; update the relevant evidence pointer and remaining delta without converting topical overlap into completion. Re-run each report's included harness at its identified subject. Add cross-platform, human, or independent evidence only when the corresponding target/operator is explicitly selected.
