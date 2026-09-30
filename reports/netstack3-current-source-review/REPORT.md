# R501 Netstack3 architecture against a later Fuchsia source snapshot

## Summary

The [frozen R501 matrix](support/matrix.json) preserves the original report and metadata bytes, exact `## Summary` excerpt and four numbered clauses at reference `4774f2e455d1b70a6321b760deeb6caae0e6f920`. Official Fuchsia Gitiles evidence places R501's pinned [`c480400b0e6cb9a9b36384935639fb3e6566bd68`](https://fuchsia.googlesource.com/fuchsia/+/c480400b0e6cb9a9b36384935639fb3e6566bd68) behind the selected, observed main snapshot [`955de750a2aae45faa99e02e29715b794dd3b544`](https://fuchsia.googlesource.com/fuchsia/+/955de750a2aae45faa99e02e29715b794dd3b544) by a bounded 91-commit range. An intervening [Netstack3 change](https://fuchsia.googlesource.com/fuchsia/+/76ab45a89c9f0ccc6e0bef3867a9ffcc775f8e10) changes three blobs in IP/filter metadata handling. This is a narrow source delta adjacent to R501's architectural discussion. It does **not** establish that any of R501's four architectural conclusions changed or that present behavior was revalidated.

The public `main` ref advanced during collection. The chosen `955de750…` commit is a **fixed observed snapshot**, not a claim to the latest main commit at report freeze. The [recorded source comparison](support/official-source-comparison.json) includes the later ref observation and the old/new Git tree IDs. No Fuchsia code or tests were run; Anneal product implications are unassessed.

## Applicability

R501's original `## Summary` says that protocol semantics and bindings remain separated, lifecycle and operational eligibility differ, stable local invariants benefit from static types while some socket identities survive dynamic transitions, and shared-state authority is serialized at defined sections without making all core calls actors. The exact four clauses and original five upstream subject pins are in the matrix. The original report's historical commits remain historical evidence; this review only compares its current Netstack3 pin with one later Fuchsia source snapshot.

The selector is R501 in the 581-row inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. The current parent contains 593 report packages. The matrix hashes and accounts for all 12 additions, none of which replaces R501.

## Findings

The Gitiles log range from old to selected new commit contains 91 commits without a further pagination token. Its final listed commit has the old revision as its parent, establishing this forward ancestry. Recursive Netstack3 tree comparison found three changed final blobs, all in [`76ab45a89c9f0ccc6e0bef3867a9ffcc775f8e10`](https://fuchsia.googlesource.com/fuchsia/+/76ab45a89c9f0ccc6e0bef3867a9ffcc775f8e10):

| Commit-pinned source file | Source-level difference |
| --- | --- |
| [`core/filter/src/logic.rs`](https://fuchsia.googlesource.com/fuchsia/+/955de750a2aae45faa99e02e29715b794dd3b544/src/connectivity/network/netstack3/core/filter/src/logic.rs) | `ProofOfEgressCheck::clone_for_fragmentation` becomes `clone_for_multiple_frames`; its documented use broadens to fragmentation or GSO segmentation. |
| [`core/ip/src/base.rs`](https://fuchsia.googlesource.com/fuchsia/+/955de750a2aae45faa99e02e29715b794dd3b544/src/connectivity/network/netstack3/core/ip/src/base.rs) | Adds `SplitDeviceIpLayerMetadata` and a splitting helper that retains unique transmit metadata in the primary frame while copying shareable fields into a secondary; the fragmentation path uses the helper. The source still has a TODO about socket penalty metadata for only one frame. |
| [`core/ip/src/base/tests.rs`](https://fuchsia.googlesource.com/fuchsia/+/955de750a2aae45faa99e02e29715b794dd3b544/src/connectivity/network/netstack3/core/ip/src/base/tests.rs) | Adds a unit test for splitting metadata. The test was inspected as source only. |

The old and new Git tree IDs are identical for Netstack3 `docs`, top-level bindings `src`, `core/tcp`, `core/udp`, `core/device`, `core/lock-order`, and `core/sync`. This supports source continuity **within those trees at the selected pair of commits**. The IP/filter delta is not mapped to a revision of R501's four broader architectural claims. Each clause therefore remains a historical claim with a bounded current-source observation, not a revalidated current-version behavioral claim.

## Boundaries

The source evidence is repository metadata and commit-pinned file inspection. The JSON records Git object IDs and a selected ref but does not contain raw source file snapshots; source snapshot SHA-256 fields are null. Its offline checker verifies internal evidence consistency and the exact frozen reference corpus, but cannot independently refresh Gitiles or prove that `main` remains at the selected commit. No Fuchsia build, test, device, or Netstack3 process was run. All four clause runtime fields are `unexecuted_in_this_review`; the Anneal product field is `unassessed`. No behavior equivalence, compatibility, or product guarantee follows from this source review.

## Evidence and revalidation

The package includes the [matrix](support/matrix.json), [recorded official-source comparison](support/official-source-comparison.json), [single-row selector](support/frozen-cohort.csv), [baseline inventory](support/version-inventory-ebcdcad-581.csv), [baseline path list](support/baseline-report-paths.txt), and [offline checker](support/check_matrix.py). Run `python3 reports/netstack3-current-source-review/support/check_matrix.py` from a checkout containing the frozen commits. A stronger review should pin a new Fuchsia source revision, inspect the affected IP/filter call paths and dependencies for each precise claim, then run a version-pinned fixture if runtime behavior matters. Prompt/setup refinement: freeze a moving upstream ref before comparing, record ancestry and exact changed blobs, and keep source findings separate from execution and Anneal design conclusions.
