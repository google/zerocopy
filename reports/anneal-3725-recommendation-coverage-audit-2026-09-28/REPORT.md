# Recommendation-level coverage audit for zerocopy issue #3725

## Summary

Issue #3725 contains 136 research recommendations, not 136 independent report-package requirements. This audit maps each recommendation against the `reference` corpus at `6056bd38f7b1896b4120e212d9e63e2430d92792` (260 packages), including four newly executed reports. This report then publishes the mapping requested by R103. In the resulting corpus, exactly one recommendation (R103) is complete as written; 83 remain partial, 23 remain gaps, and 29 remain conditional. The four new execution reports strengthen bounded evidence but do not establish the unfinished semantic proofs, human evaluations, or broader matrices requested by the issue.

This report is a recommendation-to-evidence map, not a correctness audit of every claim in 260 report packages. The full 136-row disposition and remaining-deliverable table is preserved at `support/recommendation-matrix.md`.

## Applicability

The examined issue is `google/zerocopy#3725`, closed when read. Its body hash is recorded in `REPORT.json`. The corpus snapshot inspected was `reference` at `google/zerocopy@6056bd38f7b1896b4120e212d9e63e2430d92792`, with 260 report packages. The comparison also considered closed issue #3720 and closely matched report contents. This audit reuses the issue recommendation wording and makes conservative judgments about whether each requested method/deliverable is present.

Disposition meanings:

- **Complete**: the recommendation's specified deliverable is present in the mapped evidence.
- **Partial**: related evidence exists, but an explicit proof, experiment, comparison, or evaluation requested by the recommendation remains.
- **Gap**: no close report was identified for the central deliverable.
- **Conditional**: the recommendation is gated on a concrete supported target or use case and has no such target established in the issue/corpus context.

These labels are about the recommendation's deliverable, not report quality or system correctness. A source survey does not count as a proof or execution merely because it discusses the same subject.

## Findings

### The four new executed reports add narrow evidence

The following reports were published in the current follow-on:

- `anneal-v1-contract-mutation-adequacy-2026-09-28` executes six specification mutations. It demonstrates that impossible preconditions and weakened postconditions can yield valid proofs that fail to describe the intended function; it does not establish general spec adequacy.
- `cargo-rust-charon-anneal-coverage-matrix-2026-09-28` traces a fixture through Cargo units, rustc invocations, Charon, Aeneas, and one V1 theorem. It proves only one annotated library obligation and does not cover every Cargo root/configuration.
- `lean-batch-diagnostic-normalization-oracle-v4-30-0-rc2` tests path-normalized diagnostics against changed-theorem controls. It shows normalized diagnostic equality alone is not a semantic-equivalence oracle.
- `lean-lsp-old-version-wait-race-v4-30-0-rc2` demonstrates that a successful wait for an older document version may precede a goal query for newer in-memory text. It derives a client snapshot guard, but does not execute a proof-patch race.

Basis: **execution** in each identified report; **derived** for the remaining-scope judgments. The complete row-by-row disposition is in `support/recommendation-matrix.md`.

### Recommendation counts after this batch

| Disposition | Count | Interpretation |
| --- | ---: | --- |
| Complete | 1 | R103's requested recommendation-to-evidence audit is now persisted in this report. |
| Partial | 83 | Related corpus evidence exists, but a material deliverable requested by the recommendation is still missing. |
| Gap | 23 | No close evidence was identified for the central deliverable. |
| Conditional | 29 | Deferred until a concrete target or use case is selected. |

The 23 gaps include both research that is possible in principle and work that needs different resources (for example, human participants, independent operators, or a mechanization effort). The 29 conditional items are not treated as required work without their stated use case. The counts sum to 136 and should not be interpreted as project commitments.

### Earlier completion language should be scoped to its batch

Prior statements that a selected batch was “100% persisted” do not mean the full issue agenda was complete. This table records report-level evidence alongside unclosed deliverables, so future planning can select by shared fixture and method without inferring coverage from titles, package counts, or #3720 survey checkmarks.

## Boundaries

- The audit is a recommendation-level crosswalk; it did not reread all 260 report packages in full or revalidate all source claims.
- The issue itself says its entries are recommendations, not adopted architecture or a requirement to execute every candidate. Conditional items remain conditional until a specific supported use case is chosen.
- Partial and Gap dispositions do not establish that Anneal is incorrect or unsafe. They describe research evidence not present in this corpus snapshot.
- Human studies, independent reproduction, and checked semantic correspondence cannot be inferred from local single-operator tool execution.
- The audit does not update, reopen, or close issue #3725.

## Evidence

- `google/zerocopy#3725`, body SHA-256 `f733f6eec6c7ec45633288bbe025dfd5a155d66a885b593dc6a4b0d97160621c`, read on 2026-09-28; issue state was closed.
- `google/zerocopy@6056bd38f7b1896b4120e212d9e63e2430d92792`, branch `reference`, catalog contained 260 packages before this audit report was added.
- `support/recommendation-matrix.md` preserves all 136 IDs, recommendation titles, dispositions, evidence pointers, and remaining deliverables after incorporating the four new reports.

Evidence roles: **source** for the public issue text and reference-corpus package metadata/prose; **execution** for the four new reports; **derived** for disposition assignment and the claim that a close subject match does not meet an explicitly stronger deliverable.

## Revalidation

For a later audit, fetch the then-current `reference` tip, read the issue body and state, count the report catalog, and check every recommendation ID against the corresponding report content and method. Preserve a row as Partial when the report lacks an explicitly requested proof, execution, comparison, or evaluation; do not infer completion from topical overlap. Recompute counts from the row table and verify they sum to 136. Record changes in report evidence separately from changes in issue scope.
