# R510 reconciliation and Reflector current-source review

## Summary

The [R510 matrix](support/matrix.json) freezes the exact three `## Summary` paragraphs, section locator, report subjects, evidence map and file hashes at reference `7aba064d95afec974b2478feca6f8c1a1c0b3088`. Official `kubernetes-sigs/controller-runtime` `main` still equals R510's pin. Official `kubernetes/kubernetes` `master` is 20 commits forward from R510's pin, but the cited client-go Reflector file has the same Git blob at both commits. This is a bounded source result for the three mapped files. It does not prove current controller/cache runtime behavior or Anneal product behavior.

## Separate upstream identities and releases

R510 pins [`kubernetes-sigs/controller-runtime@8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b`](https://github.com/kubernetes-sigs/controller-runtime/commit/8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b) for level-based reconcile contracts and event-key deduplication. Its official `main` ref remains at that exact commit, so there is **no forward controller-runtime source revision** to compare.

R510 pins [`kubernetes/kubernetes@6d1d025050cb63ae5b8e53037aced205e6a28410`](https://github.com/kubernetes/kubernetes/commit/6d1d025050cb63ae5b8e53037aced205e6a28410) for `staging/src/k8s.io/client-go/tools/cache/reflector.go`. The selected official `master` is [`08147af84478f859c2e2234d71ceace8bdb412c7`](https://github.com/kubernetes/kubernetes/commit/08147af84478f859c2e2234d71ceace8bdb412c7), 20 ahead and zero behind. This compares the **client-go subtree in the pinned Kubernetes monorepo**, without substituting the separate `kubernetes/client-go` mirror.

The latest official controller-runtime release is [`v0.25.1`](https://github.com/kubernetes-sigs/controller-runtime/releases/tag/v0.25.1), published 2026-09-14, with tag commit `67b72c2517be1d2b0dec612477eb20c3c959a8aa`. The latest official Kubernetes release is [`v1.37.1`](https://github.com/kubernetes/kubernetes/releases/tag/v1.37.1), published 2026-09-23; its annotated tag object peels to commit `f78e722310e50bcaca9276be22276d9e91d91308`. The release histories **diverge** from their corresponding R510 development pins. They are recorded as separate release identities, not treated as forward claim rechecks.

The original selector is R510 in the 581-row inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. The frozen reference has 603 report packages; all 22 additions are reconciled and hashed in the matrix.

## Claim-mapped source findings

The original [evidence map](../reconciliation-event-hints-repair-loops-2005-2026/support/evidence-map.json) names two controller-runtime files, `pkg/reconcile/reconcile.go` and `pkg/doc.go`, for the level-based reconcile and enqueue-key claims. Their commit-pinned Git blobs are identical because `main` is still the pinned commit. There is no newer controller-runtime source finding.

The map names Kubernetes `staging/src/k8s.io/client-go/tools/cache/reflector.go` for snapshot/resource-version continuity, expired-version recovery, store replacement, and watch-list initial consistency. Its Git blob is unchanged from R510's pin to the selected newer `master`. The official compare returned 38 changed files, below the 300-file cap, and **none is the mapped Reflector file**. Some other Kubernetes source changed, including apiserver storage correctness tests; this review does not infer system-wide cache semantics from the unchanged Reflector blob. The [official-source observation](support/official-source-observation.json) records the complete 38-path list, each mapped file's Git blob SHA-1 and content SHA-256, raw ref outputs, and release tag identities.

R510's inotify manual, WatchList KEP, Kubernetes website docs, Anneal design pin, and direct save/format/watch-loop report remain their original historical/documentary or derived evidence. This supplement does not refresh those sources or turn the report's Anneal recommendations into adopted implementation state.

## Boundaries and revalidation

No controller, Reflector, Kubernetes cluster, watcher, or Anneal process was installed or executed. `runtime_result` is `unexecuted_in_this_review`; `anneal_product_result` is `unassessed`. Commit-pinned individual files were read for hashes; no full source archive was acquired. The [offline checker](support/check_matrix.py) validates exact frozen claims and evidence map bytes, corpus reconciliation, upstream/ref/release relationships, and mapped blob identity. It cannot refresh upstream refs or prove runtime convergence, watch continuity, or publication safety.

Run `python3 reports/reconciliation-current-source-review/support/check_matrix.py` from a checkout containing the frozen corpus commits. A stronger recheck would inspect dependencies and call paths outside the mapped files, then execute a version-pinned list/watch expiration and controller-reconcile fixture. Prompt/setup refinement: name the monorepo path of client-go explicitly, keep controller and cache contracts separate, and peel release tags before interpreting a source difference as a newer version.
