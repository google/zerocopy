# R386 SerAPI and Rocq LSP/Flèche current-source review

## Summary

At the 2026-09-30 ref observation, both official default branches still pointed to the exact commits pinned in [R386](../coq-rocq-stm-serapi-fleche-architecture-2013-2026/REPORT.md): [`rocq-archive/coq-serapi@6196f9f572ef9dd3749b885cabce7a57406cedb9`](https://github.com/rocq-archive/coq-serapi/commit/6196f9f572ef9dd3749b885cabce7a57406cedb9) and [`rocq-community/rocq-lsp@2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe`](https://github.com/rocq-community/rocq-lsp/commit/2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe). Each old-to-current comparison is the same commit, so each has a zero-commit forward range and no changed paths. This is **source identity under the inspected default-branch refs**, not a new-version revalidation or a runtime behavior finding.

## Frozen claim and source identity

The [matrix](support/matrix.json) freezes R386's exact six Summary paragraphs, eleven evidence-map claims, original source subjects, report/evidence-map hashes, and section locator at reference `f64e634e06aaf8b7eae2fefb3a9d7f2ebf82d3b2`. The original R386 selector comes from the 581-report version inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`; the frozen parent has 607 report packages, including 26 additions reconciled by path and hash. Historical STM and PIDE publications and Anneal's design pin retain their original roles. They are not treated as newer SerAPI or Flèche implementations.

Separate [SerAPI](support/serapi-refs.txt) and [Rocq LSP](support/rocq-lsp-refs.txt) official `git ls-remote` snapshots record `HEAD` and `refs/heads/main` at the corresponding old commit. Equality of the full commit IDs proves a zero-forward comparison for these selected branch tips without inferring ancestry from names or dates. This review did not select or compare release tags or a maintained successor to archived SerAPI; it makes no cross-repository version equivalence claim.

## Claim-mapped source files

The original [R386 evidence map](../coq-rocq-stm-serapi-fleche-architecture-2013-2026/evidence-map.json) names two SerAPI files and four Rocq LSP/Flèche files. The [official-source observation](support/official-source-observation.json) records each old/current Git blob SHA-1, content SHA-256, byte size, and commit-pinned raw URL. The [six preserved source snapshots](support/snapshots/) reproduce the evidence-map blobs byte for byte:

| Repository | Claim-mapped paths | Result |
| --- | --- | --- |
| `rocq-archive/coq-serapi` | [`README.md`](https://github.com/rocq-archive/coq-serapi/blob/6196f9f572ef9dd3749b885cabce7a57406cedb9/README.md), [`serapi/serapi_protocol.mli`](https://github.com/rocq-archive/coq-serapi/blob/6196f9f572ef9dd3749b885cabce7a57406cedb9/serapi/serapi_protocol.mli) | Same pinned commit and blobs. R386's SerAPI interface, parent-state parsing, and cancellation clauses have no newer default-branch source to compare. |
| `rocq-community/rocq-lsp` | [`README.md`](https://github.com/rocq-community/rocq-lsp/blob/2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe/README.md), [`etc/doc/USER_MANUAL.md`](https://github.com/rocq-community/rocq-lsp/blob/2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe/etc/doc/USER_MANUAL.md), [`etc/doc/PROTOCOL.md`](https://github.com/rocq-community/rocq-lsp/blob/2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe/etc/doc/PROTOCOL.md), [`fleche/doc.ml`](https://github.com/rocq-community/rocq-lsp/blob/2e0c43c34af6d6cad272ca2b8c4a417fe780bfbe/fleche/doc.ml) | Same pinned commit and blobs. R386's Flèche document, workspace, recovery, and versioned-request clauses have no newer default-branch source to compare. |

The matrix maps each of the eleven exact evidence-map claims to its original evidence IDs and, where applicable, the specific files above. The zero-forward result does not establish that those claims are complete descriptions of either project, that their interfaces are compatible with each other, or that an Anneal integration would preserve their semantics.

## Limits and revalidation

No SerAPI, Rocq LSP, Flèche, Rocq, or Anneal executable was installed or run. Current-version runtime result is `unexecuted_in_this_review`; Anneal product result is `unassessed`. No whole repository archive was acquired; six claim-mapped source files are preserved. The [offline checker](support/check_matrix.py) validates frozen corpus paths and hashes, exact claims and evidence-map links, separate official ref snapshots, and the preserved blob/source hashes. It cannot refresh live refs or prove product behavior.

Run `python3 reports/rocq-serapi-fleche-current-source-review/support/check_matrix.py` from a checkout with the frozen corpus commits. A later recheck should record the timestamped tip of each repository separately, compare any actual forward ranges and claim-mapped paths, and test exact runtime acceptance semantics only if an integration decision requires them. Setup/prompt refinement: first ask whether a version-specific report's pin is already the observed default-branch tip; if so, preserve a zero-forward source disposition instead of inventing a newer implementation comparison.
