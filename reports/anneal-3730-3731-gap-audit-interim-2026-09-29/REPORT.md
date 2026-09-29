# Interim gap audit for Anneal issues #3730 and #3731

## Summary

The issue backlog contains 159 consolidated investigations and a 174-suggestion crosswalk. At the completed-package snapshot **2026-09-29T07:20:04Z**, all 159 IDs and all 174 suggestions have a row in the preserved ledgers. The 21 newly completed #3730 report packages and 42 older relevant corpus packages provide evidence across the agenda, but **no investigation is certified complete against its full requested scope by this audit**. The explicit per-ID remaining conditions are in `support/investigation-gap-matrix.csv`; the original 174 suggestions inherit their mapped destinations and gaps in `support/3730-crosswalk-disposition.csv`.

This is an **interim** audit. Other workers were producing packages at snapshot time. The ledger must be refreshed after those packages finish and before anyone claims 100% completion.

## Applicability

The requested scopes and #3730-to-#3731 mapping are copied from the published `anneal-3730-3731-coverage-audit-2026-09-29` support files. This report examines that agenda against completed packages available in this `reference` checkout at 2026-09-29T07:20:04Z. The earlier ledger's prior-report column was used as a navigation index; each of its 42 distinct package targets exists, and the distinct summaries/boundaries were reviewed. They do not automatically satisfy the later, broader investigation wording. The 21 new packages were reviewed by their summary, applicability, findings, and explicit boundaries. No GitHub issue status or checkbox is changed here.

The subject is the agenda/corpus relationship, not a new experiment on Anneal itself. Current V2 is incomplete; many reports use finite models, tiny Lean/Charon/Aeneas/Lake fixtures, or source/specification review. A package can answer a narrow question while leaving the requested matrix open.

## Findings

### Reconciliation outcome

The item-level dispositions are: **human-gated** 1, **partial execution** 131, **platform-gated** 1, **requested execution not run** 15, **requested integration not run** 10, **toolchain-gated** 1. “Partial execution” means at least one relevant executed slice exists, not that the full investigation or implementation contract has passed. “Requested execution/integration not run” means source or historical pointers may exist, but the proposed live comparison has not been performed. I081 needs a local OCaml/Dune toolchain for same-process Aeneas; I124's other-platform cells are conditional on an applicable host; I141 specifically requires human participants. The CSV carries these distinctions and the narrow residual for every row.

The strongest new concrete evidence includes: a coherent-capture counterexample and generation fence in a fake stage engine; actual Charon/Aeneas CLI success/failure/determinism and subject-identity specimens; direct Lean LSP version, unsaved-buffer, and imported-artifact behavior; small Lake relocation/cache/shared-writer and retention matrices; and a prototype proof-acceptance negative-control suite. These results are valuable but none supplies a complete real Anneal editor→MCP→Charon→Aeneas→Lake→Lean vertical path.

### Smallest useful follow-up report set

The following packages can share fixtures and each close several explicit rows. An author must still keep unexecuted cells visible; these are work packages, not claims of completion:

1. **Architecture and alternatives** (I001–I008, I142, I144, I159): matched one-shot/project/broker designs, structured stage API, upstream API gaps, falsification and decision gates.
2. **Real Rust input and annotation pipeline** (I009–I024, I073–I080): Cargo subject closure and overlay, tolerant annotation parser, compiler attachment, proof-only classifier, authored-text ownership, and Charon scaling/reuse.
3. **Production projection and provenance** (I025–I032, I059–I060): real syntax/generator, source-map properties, completion/workspace edits, diagnostics, and streaming/materialized equality.
4. **Lean document and protocol matrix** (I033–I050, I056, I091, I147): layouts, context fidelity, import refresh across launch modes, exact goal positions/readiness, RPC lifetime, and version/incarnation races.
5. **Immutable generation and failure recovery** (I051–I055, I105–I112, I121–I122): real multi-module staged publication, complete output sets, late completions, cancellation, lock/GC/restart, and event reconciliation.
6. **Editor/MCP integration** (I057–I072, I152, I155–I157): one authority, hidden document lifecycle, typed tools, two clients, subscriptions, retries, access tiers, and batch/live shells.
7. **Aeneas library and manifest** (I081–I088, I148–I149, I156, I158): same-process use once local toolchain is available, flag/concurrency matrix, executable provenance, golden translations, and exact handoff manifest.
8. **Prepared Lake/artifact contract** (I089–I104, I120, I125, I150–I151): operation matrix, clean/prepared parity, corrupt/interrupted cache, path relocation, offline enforcement, native/plugin identity, and writable-tree failures.
9. **Resources and fixture economics** (I113–I119, I139, I146, I153–I154): bounded cold/warm concurrency, physical memory, total disk bill, soak, nested parallelism, topology, retention, and contamination.
10. **Acceptance and independent evaluation** (I126–I141, I143–I144, I159): trust/taint, fresh oracle, coverage, comparators, real fault replay, independent reproduction and upgrade; a human study for I141 and remote test only if locally justified.

One package can legitimately cover multiple IDs only when its executed controls and preserved evidence address each row's requested condition. The detailed residuals in the matrix prevent broad package titles from being counted as coverage.

## Boundaries

- This is a snapshot of completed files, not an inspection of in-progress experiments or later upstream changes. No attempt was made to stage or publish it here.
- The old corpus pointers were reviewed at summary/boundary level; this audit did not revalidate all 42 reports' scripts and primary-source citations. Thus no item is certified complete solely from a pointer.
- The item dispositions are deliberately conservative. An agenda ID often contains several methods and matrix dimensions; a small executed case does not close all of them.
- The 174-item crosswalk maps suggestions to I IDs. It is not 174 independent experiment completions. Multiple suggestions share a destination, and several destinations retain unrelated residuals.
- Human evaluation (I141), other-platform semantics (I124), and remote execution (I143) depend on a selected scope/operator/environment; local substitutes must be labeled as such.

## Evidence

- `support/investigation-gap-matrix.csv`: all 159 exact scopes, prior pointers, reviewed new packages, disposition, and specific remaining condition.
- `support/3730-crosswalk-disposition.csv`: all 174 original suggestions, destination IDs and inherited remaining conditions.
- `reports/anneal-3730-3731-coverage-audit-2026-09-29/support/`: the prior exact issue-derived scope and crosswalk source for this report.
- The 21 package names in the matrix refer to their preserved `REPORT.md` and support artifacts in the same corpus. Evidence role: **source** for agenda text and package boundaries; **derived** for the conservative coverage judgment.

## Revalidation

Regenerate the ledgers against the completed package snapshot, check that the 159 IDs are exactly I001–I159 and that 174 unique #3730 IDs all map to existing destinations, then review every newly completed package's applicability and boundaries against the per-row residual before changing any disposition. A passing `tools/reference.py check` verifies package structure but does not establish that the requested experiment was performed.
